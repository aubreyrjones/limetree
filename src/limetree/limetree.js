"use strict";

// MIT License

// Copyright (c) 2021 Aubrey R. Jones

// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:

// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.

// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.


/**
 * Layout algorithm translated from: https://github.com/llimllib/pymag-trees/
 * Relicensed as part of this transformative work under the MIT license above,
 * in accordance with original LICENSE:
 * 
 * 
 *           DO WHAT THE FUCK YOU WANT TO PUBLIC LICENSE
 *                  Version 2, December 2004
 *
 * Copyright (C) 2004 Sam Hocevar <sam@hocevar.net>
 *
 * Everyone is permitted to copy and distribute verbatim or modified
 * copies of this license document, and changing it is allowed as long
 * as the name is changed.
 *
 *         DO WHAT THE FUCK YOU WANT TO PUBLIC LICENSE
 * TERMS AND CONDITIONS FOR COPYING, DISTRIBUTION AND MODIFICATION
 *
 * 0. You just DO WHAT THE FUCK YOU WANT TO.
 * 
*/

function sleep(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
}

function debug_step() {
    draw_all_configured();
    return sleep(50);
}

var finishedLayout = false;

const exrp = p => (1.5**p) * (0.15 ** (1 - p));

const RANK_SEPARATION = 80.0;
const BOX_W_MARGIN = 4;
const W_SEPARATION = 20;
const BOX_TOP_OFFSET = 26;
const BOX_HEIGHT = BOX_TOP_OFFSET + 10;

var _next_node_id = 999;
var _all_nodes = {};
var _root_node = null;
var _rank_lists = new Array();
var _rank_wave = new Array();

var rank_list = function (rank) {
    let slen = _rank_lists.length;
    for (let i = 0; i <= (rank - slen); i++) {
        _rank_lists.push(new Array());
        _rank_wave.push(-1);
    }
    return _rank_lists[rank];
}

function rank_left(v) {
    if (v.rankorder <= 0) return null;
    return rank_list(v.rank)[v.rankorder - 1];
}

function rank_right(v) {
    if (v.rankorder >= rightmost_placed_for_rank(v.rank)) return null;
    return rank_list(v.rank)[v.rankorder + 1];
}

// record the rankorder of the rightmost node to be placed for this rank.
var mark_wave = function(v) {
    _rank_wave[v.rank] = v.rankorder;
}

function rightmost_placed_for_rank(rank) {
    return _rank_wave[rank];
}

function print_wave_front() {
    let toPrint = new Array();
    for (let i = 0 ; i < _rank_wave.length; i++) {
        let wf = rightmost_placed_for_rank(i);
        if (wf < 0) {
            toPrint.push(null);
        }
        else {
            toPrint.push(rank_list(i)[wf].label);
        }
    }
    console.log("Wavefront: ", toPrint);
}

// get the last placed node in the rank
var wave_front = function(rank) {
    let entry = rightmost_placed_for_rank(rank);
    if (entry < 0) return null;
    let rl = rank_list(rank);
    
    if (entry >= rl.length){
         return null;
    }

    return rl[entry];
}

    
let _styles = {
    "default" : {
        "fillStyle" : "rgb(200, 200, 200)",
        "outline" : "2px solid black",
        "font-face" : "sans-serif"
    }
};
let _node_label_keys = [];
let _payload_mask_objects = [];

var g_pan_x = -1500;
var g_pan_y = -200;
var g_scale = 0.6;

var next_node_id = function() {
    let i = _next_node_id;
    _next_node_id += 1;
    return i;
}

var split_sorted_key = function(k) {
    let splits = k.split(":", 1);
    if (splits.length == 1) { return k; }
    return splits[1];
}

var make_edge = function(n, t) {
    return {
        name : n,
        target : t
    }
}

var is_masked = function(keyname) {
    if (keyname[0] == "@") return true;
    for (let mask of _payload_mask_objects) {
        if (mask == keyname) return true;
    }

    return false;
}

class LiveNode {
    constructor(o) {
        // Payload, general tree pointers, and style information.
        this.parent = null;
        this.ancestors = new Set();
        this.ancestors.add(this);
        this.rank = 0;
        this.rankorder = -1;
        this.maxdepth = 0;
        this.payload = {};
        this.children = new Array();
        this.pos_x = -2000;
        this.pos_y = RANK_SEPARATION * this.rank;
        this.boxwidth = 100;
        this.style = "default";
        this.tag = false;
        this.tag2 = false;
        this.tag3 = false;
        this.tag4 = false;

        // get the id
        if ("!id" in o) {
            this.id = o["!id"]; // explicit id
        } 
        else if ("id" in o) {
            this.id = o["id"]; // maybe there was a payload named `id` we can use?
        }
        else {
            this.id = next_node_id(); // make one up.
        }

        // register us with global trackers
        _all_nodes[this.id] = this;


        // fetch style information from the global style map
        this.font = '24px sans-serif'; // or fake it for now
        
        // load the payload object, recurse on children.
        let _keys = Object.keys(o);
        _keys.sort();

        for (let k of _keys) {
            if (k[0] === '!') {
                // control value
                this[k.slice(1)] = o[k];
            }
            else {
                let my_key = split_sorted_key(k);

                if (!is_masked(k) && o[k] instanceof Object) {
                    if (o[k] instanceof Array) {
                        for (let i = 0; i < o[k].length; i++) {
                            let sub_o = o[k][i];
                            if (sub_o instanceof Object) {
                                let child_key = my_key + "[" + i + "]";
                                this.add_child(child_key, new LiveNode(sub_o));
                            }
                        }
                    }
                    else {
                        this.add_child(my_key, new LiveNode(o[k]));
                    }
                }
                else {
                    // regular payload value
                    this.payload[my_key] = o[k];
                }
            }
        }

        // if we don't have an explicit label already, try some fallbacks.
        if (!("label" in self)) {
            for (let k of _node_label_keys) {
                if (o[k]) {
                    this.label = o[k];
                    break;
                }
            }
        }

        // setup for layout
        this.x = -10000 + (Math.random() * 1000); //layout position, copied over to pos_x when ready.
        this.sib_index = -1;
        this.delta = 0.0;
    }

    add_child(edge_name, c) {
        let childIndex = this.children.length;
        c.sib_index = childIndex;
        c.parent = this;
        this.children.push(make_edge(edge_name, c))
    }

    measure_self(ctx) {
        ctx.font = this.font;
        let label = this.label || this.id;
        let labelWidth = ctx.measureText(label).width;
        this.boxwidth = labelWidth + (BOX_W_MARGIN * 2);
    }

    rank_self(my_rank, parent_ancestors) {
        let maxChildRank = my_rank;
        parent_ancestors.forEach(item => this.ancestors.add(item));
        if (this.parent) {
            this.ancestors.add(this.parent);
        }

        for (let edge of this.children) {
            let cRank = edge.target.rank_self(my_rank + 1, this.ancestors);
            if (cRank > maxChildRank) {
                maxChildRank = cRank;
            }
        }
        this.maxdepth = maxChildRank;

        this.rank = my_rank;
        this.pos_y = this.rank * RANK_SEPARATION;
        let rl = rank_list(my_rank);
        this.rankorder = rl.length;
        rl.push(this);

        return this.maxdepth;
    }

    resolve_delta(parent_value) {
        this.x += this.delta + parent_value;
        for (let edge of this.children) {
            edge.target.resolve_delta(this.delta + parent_value);
        }
    }

    non_tagging_delta_sum() {
        if (this.parent) {
            return this.delta + this.parent.non_tagging_delta_sum();
        }
        return this.delta;
    }

    delta_sum() {
        //this.tag3 = true;
        if (this.parent) {
            return this.delta + this.parent.delta_sum();
        }
        return this.delta;
    }

    center_at(x) {
        this.x = x - this.halfw();
    }

    descends_from(v) {
        return this.ancestors.has(v);
    }

    halfw() {
        return (this.boxwidth / 2);
    }

    center() {
        return this.right_side() - this.halfw();
    }

    left_side() {
        return this.pos_x;
    }

    right_side() {
        return this.pos_x + this.boxwidth;
    }

    top() {
        return this.pos_y - BOX_TOP_OFFSET;
    }

    bottom() {
        return this.top() + BOX_HEIGHT;
    }

    y_inside(y) {
        return y <= this.bottom() && y >= this.top();
    }

    x_inside(x) {
        return x >= this.left_side() && x <= this.right_side();
    }

    click_inside(x, y) {
        return this.x_inside(x) && this.y_inside(y);
    }

    layout_left_side() {
        this.tag2 = true;
        return this.x + this.delta_sum();
    }

    layout_right_side() {
        this.tag = true;
        return this.x + this.delta_sum() + this.boxwidth;
        //return this.layout_left_side() + this.boxwidth; // separated for tagging
    }

    layout_center() {
        return this.layout_left_side() + this.halfw();
    }

    layout_natural_right() {
        return this.x + this.boxwidth; // NO DELTA
    }

    right_sib() {
        if (!this.parent) return null;
        if (this.sib_index >= this.parent.count() - 1) return null; //right-most child
        return this.parent.child(this.sib_index + 1);
    }

    child(index) {
        if (index < 0) {
            index = this.children.length + index;
        }
        if (index < 0 || index >= this.children.length) {
            return null;
        }
        
        return this.children[index].target;
    }

    has_child(n) {
        for (let edge of this.children) {
            if (n === edge.target) return true;
        }

        return false;
    }

    count() {
        return this.children.length;
    }

    leaf() {
        if (this.count()) { return false; }
        return true;
    }

    draw(ctx) {
        const tagged = this.tag;
        const tagged2 = this.tag2;
        const tagged3 = this.tag3;
        const tagged4 = this.tag4;

        ctx.lineWidth = 1;

        if (!finishedLayout) {
            this.pos_x = this.x + this.non_tagging_delta_sum();
        }

        ctx.font = this.font
        let label = this.label || this.id;

        let style = _styles[this.style];

        ctx.strokeStyle = 'black';
        for (let ck in this.children) {
            let c = this.children[ck].target;
            if (!finishedLayout) {
                c.pos_x = c.x + c.non_tagging_delta_sum();
            }
            ctx.beginPath();
            ctx.moveTo(this.center(), this.pos_y);
            ctx.lineTo(c.center(), c.pos_y);
            ctx.stroke();
        }

        if (tagged || tagged2 || tagged3) {
            ctx.lineWidth = 4;
            if (tagged) {
                ctx.strokeStyle = "red";
                ctx.strokeRect(this.pos_x - 4, this.top() - 4, this.boxwidth + 8, BOX_HEIGHT + 8);
            }
            if (tagged2) {
                ctx.strokeStyle = "blue";
                ctx.strokeRect(this.pos_x - 8, this.top() - 8, this.boxwidth + 16, BOX_HEIGHT + 16);
            }
            if (tagged3) {
                ctx.strokeStyle = "green";
                ctx.strokeRect(this.pos_x - 12, this.top() - 12, this.boxwidth + 24, BOX_HEIGHT + 24);
            }
            if (tagged4) {
                ctx.strokeStyle = "orange";
                ctx.strokeRect(this.pos_x - 12, this.top() - 12, this.boxwidth + 24, BOX_HEIGHT + 24);
            }
        }
        
        ctx.lineWidth = 1;
        ctx.strokeStyle = style.outline;
        ctx.fillStyle = style.fillStyle;
        ctx.fillRect(this.pos_x, this.top(), this.boxwidth, BOX_HEIGHT);
        ctx.strokeRect(this.pos_x, this.top(), this.boxwidth, BOX_HEIGHT);
        ctx.fillStyle = 'black';
        ctx.fillText(label, this.pos_x + BOX_W_MARGIN, this.pos_y);

        this.tag = false;
        this.tag2 = false;
        this.tag3 = false;
        this.tag4 = false;
    }
}

var least = function(a, b) {
    if (a < b) return a;
    return b;
}

var greatest = function(a, b) {
    if (a > b) return a;
    return b;
}

async function _layout(v, distance) {
    if (v.rankorder > 0) {
        v.x = rank_left(v).layout_right_side() + distance;
    }
    else {
        v.x = 0.0;
    }

    if (v.leaf()) {
        mark_wave(v);
        await debug_step(); // DEBUG
        return;
    }
    
    // inner node
    let cCount = v.count();
    for (let i = 0; i < cCount; i++) {
        let c = v.child(i);
        await _layout(c, distance); // DEBUG
        //_layout(c, distance);
    }

    // stack between and above leaves
    let midpoint = (v.child(0).layout_left_side() + v.child(-1).layout_right_side()) / 2.0;
    console.log(v.child(0).label, v.child(-1).label, v.child(0).layout_left_side(), v.child(-1).layout_right_side(), midpoint, v.boxwidth);
    let natural = midpoint - v.halfw();
    v.x = natural; // set the natural midpoint, but we'll still adjust farther along
    
    
    let lefthandMargin = 0;
    let lefthand = rank_left(v);
    
    if (lefthand) {
        lefthandMargin = lefthand.layout_right_side() + distance;
        //if (v.x < lefthandMargin) { v.x = lefthandMargin; }
    }

    let wantedMove = lefthandMargin - natural;

    do_constrained_move(v, wantedMove, false);

    const rearrangeInners = true;
    if (rearrangeInners) {
        let myMid = v.layout_center();
        // the goal here is to let child nodes to the left of us "relax"
        for (let e of v.children.slice(0).reverse()) {
            let c = e.target;
            let stress = myMid - c.layout_center();
            if (stress != 0) {
                do_constrained_move(c, stress, true);
            }
        }
    }

    mark_wave(v);
    await debug_step(); // DEBUG
    return v;
}

function do_constrained_move(v, wantedMove, doRightCheck = true) {
    if (v.label == "GEMFW") {
        console.log("THAT'S THE GUY!", wantedMove);
    }

    console.log("constrained move", v.label);
    if (wantedMove == 0) { 
        return; 
    }
    else if (wantedMove < 0) { // we're moving left
        let leftEdge = wavefront_subtree_left_edge(v);
        wantedMove = constrain_by_left_edge(leftEdge, wantedMove);
    }
    else if (doRightCheck && wantedMove > 0) {
        console.log("doing right check.");
        let rightEdge = wavefront_subtree_right_edge(v);
        wantedMove = constrain_by_right_edge(rightEdge, wantedMove);
    }

    if (v.label == "GEMFW") {
        console.log("THAT'S THE GUY! CONSTRAINED", wantedMove);
    }

    const deferred = true;
    if (deferred) {
        console.log("deferred move.");
        move_tree_deferred(v, wantedMove);
    }
    else {
        console.log("Moving subtree.");
        move_tree(v, wantedMove);
    }    
}

function search_rank_left_for_descendant(root, rank) {
    root.tag3 = true;
    let waveFront = wave_front(rank);
    if (!waveFront) return null;
    if (waveFront.descends_from(root)) return waveFront;

    while (waveFront = rank_left(waveFront)) {
        if (waveFront.descends_from(root)) return waveFront;
    }

    return null;
}

function search_rank_for_left_edge(root, startNode) {
    let nextLeft = rank_left(startNode);
    
    while (nextLeft && nextLeft.descends_from(root)) {
        nextLeft.tag3 = true;
        startNode = nextLeft;
        nextLeft = rank_left(startNode);
    }

    return startNode;
}

function wavefront_subtree_left_edge(root) {
    let edge = new Array();
    for (let i = root.rank; i <= root.maxdepth; i++) {
        let edgeNode = search_rank_left_for_descendant(root, i);
        if (!edgeNode) continue;
        edge.push(search_rank_for_left_edge(root, edgeNode));
        
    }
    return edge;
}

var wavefront_subtree_right_edge = function(root) {
    let edge = new Array();
    for (let i = root.rank; i <= root.maxdepth; i++) {
        let edgeNode = search_rank_left_for_descendant(root, i);
        if (!edgeNode) continue;
        edge.push(edgeNode);
    }
    return edge;
}

function constrain_by_left_edge(edge_list, amount) {
    for (let v of edge_list) {

        if (v.rankorder == 0) {
            continue;
        }

        let leftmargin = rank_left(v).layout_right_side() + W_SEPARATION;
        let targetX = v.layout_left_side() + amount;
        
        let overlap = targetX - leftmargin;
    
        
        if (overlap < 0) {
            amount -= overlap;
        }
    }
    return amount;
}

function constrain_by_right_edge(edge_list, amount) {
    for (let v of edge_list) {
        let rightNeighbor = rank_right(v);
        if (!rightNeighbor) continue;

        let rightMargin = rightNeighbor.layout_left_side() - W_SEPARATION;
        let targetRightEdge = v.layout_right_side() + amount;

        let overlap = targetRightEdge - rightMargin;

        if (overlap > 0) {
            amount -= overlap;
        }
    }
    return amount;
}


var move_tree_deferred = function(root, amount) {
    //root.delta += amount;
    root.x += amount;
    root.children.forEach(e => e.target.delta += amount);
}

var move_tree = function(v, amount) {
    //v.tag4 = true;
    v.x += amount;
    for (let edge of v.children) {
        move_tree(edge.target, amount);
    }
}


async function layout_tree(root) {
    await _layout(root, W_SEPARATION);

    root.resolve_delta(0.0);

    iter_all(n => n.pos_x = n.x);
    finishedLayout = true;
}

// UI

var xform_point = function(_x, _y) {
    return {
        x: _x / g_scale + g_pan_x ,
        y: _y / g_scale+ g_pan_y
    }
}

var _cur_x;
var _cur_y;

var _user_dragging = false;
var _drag_pan_x;
var _drag_pan_y;
var _user_drag_start_x;
var _user_drag_start_y;

var _zoom_param = 0.8;

var _select_node = function(x, y) {
    for (let rl of _rank_lists) {
        let example = rl[0];
        if (y < example.top) return null; // our click is above where we start, and we already checked everything lower
        if (example.y_inside(y)) {
            for (let n of rl) {
                if (n.x_inside(x)) return n;
            }
        }
    }

    return null;
}

var _clicked = function(e) {
    let p = xform_point(e.offsetX, e.offsetY);
    let n = _select_node(p.x, p.y);
    if (n) {
        set_node_data(n);
    }
}

var _mouse_down = function(e) {
    _user_dragging = true;
    _drag_pan_x = g_pan_x;
    _drag_pan_y = g_pan_y;
    _user_drag_start_x = e.offsetX;
    _user_drag_start_y = e.offsetY;
}

var _mouse_up = function(e) {
    _user_dragging = false;
}

var _mouse_moved = function(e) {
    _cur_x = e.offsetX;
    _cur_y = e.offsetY;

    if (!_user_dragging) {
        let p = xform_point(e.offsetX, e.offsetY);
        let n = _select_node(p.x, p.y);
        if (n) {
            set_node_data(n);
        }
    }
    else {
        g_pan_x = _drag_pan_x + (_user_drag_start_x - e.offsetX) / g_scale;
        g_pan_y = _drag_pan_y + (_user_drag_start_y - e.offsetY) / g_scale;

        draw_all_configured();
    }
}

var _wheel_turned = function(e) {
    _zoom_param += -e.deltaY * 0.001;
    if (_zoom_param > 1) _zoom_param = 1;
    if (_zoom_param < 0) _zoom_param = 0;
    let oldMouse = xform_point(_cur_x, _cur_y);
    g_scale = exrp(_zoom_param);
    if (g_scale < 0.05) g_scale = 0.05;
    if (g_scale > 2.0) g_scale = 2.0;

    let afterMouse = xform_point(_cur_x, _cur_y);
    g_pan_x += oldMouse.x - afterMouse.x;
    g_pan_y += oldMouse.y - afterMouse.y ;

    draw_all_configured();
}

var _displayed_node = null;

var layout_obj = function(parent_div, name, o, extra) {
    let tbl = document.createElement("table");
    parent_div.appendChild(tbl);
    
    let title = tbl.insertRow();
    let titleCell = title.insertCell();
    titleCell.innerHTML = name;
    titleCell.style = 'text-align:center';
    titleCell.setAttribute("colspan", "2");

    if (extra) {
        layout_obj(parent_div, "EXTRA", extra);
    }

    for (let pk in o) {
        let r = tbl.insertRow();
        if (o[pk] instanceof Object) {
            layout_obj(parent_div, pk, o[pk]);
            continue;
        }
        let name = r.insertCell();
        let value = r.insertCell();
        name.innerHTML = pk;
        value.innerHTML = o[pk];
    }
}

var set_node_data = function(n) {
    if (n == _displayed_node) return;
    _displayed_node = n;

    let info_div = document.getElementById("node_info");
    info_div.innerText = "";
    layout_obj(info_div, n.label || n.id, n.payload, {"delta" : n.delta, "deltasum" : n.non_tagging_delta_sum(), "id" : n.id, "x" : n.x, "redge" : n.layout_natural_right(), "depth" : n.maxdepth});
}

// Startup


var load_nodes = function() {
    let data = JSON.parse(_node_data);

    for (let sk in data["styles"]) {
        _styles[sk] = data["styles"][sk];
    }
    
    if ("label_keys" in data) 
        _node_label_keys = data["label_keys"];
    if ("payload_objects" in data)
        _payload_mask_objects = data["payload_objects"];

    if (data["nodes"].length == 1) { // recursive definition
        _root_node = new LiveNode(data["nodes"][0], 0);
    }
    else {
        // let n = new Array();
        // for (let o of data["nodes"]) {
        //     n.push(new LiveNode(o, 0));
        // }
        //not yet implemented
    }

    _root_node.rank_self(0, new Set());
}


var iter_all = function(f) {
    for (let nk in _all_nodes) {
        f(_all_nodes[nk]);
    }
}

var draw_all = function(canvas) {
    if (canvas.getContext) {
        let ctx = canvas.getContext('2d');
        ctx.clearRect(0, 0, canvas.width, canvas.height);
        ctx.save();
        ctx.scale(g_scale, g_scale);
        ctx.translate(-g_pan_x, -g_pan_y);
        iter_all(n => n.draw(ctx));
        ctx.restore();
    }
}

var draw_all_configured;

var start_limetree = function() {
    load_nodes();
    set_node_data(_root_node);

    let canvas = document.getElementById('tree_canvas');
    canvas.addEventListener('mousedown', _mouse_down);
    canvas.addEventListener('mouseup', _mouse_up);
    canvas.addEventListener('mousemove', _mouse_moved);
    canvas.addEventListener('wheel', _wheel_turned);
    canvas.addEventListener('click', _clicked);
    
    window.addEventListener('resize', _ => {
        canvas.width  = window.innerWidth;
        canvas.height = window.innerHeight;
        draw_all_configured();
    }, false);
    
    canvas.width  = window.innerWidth;
    canvas.height = window.innerHeight;

    let ctx = canvas.getContext('2d');

    draw_all_configured = _ => draw_all(canvas);

    iter_all(n => n.measure_self(ctx));

    layout_tree(_root_node);
    
    
    draw_all_configured();
}

// parse trees
const N1_node_data = `{"nodes": [{"production": "global_list", "type": null, "value": null, "id": 0, "line": -1, "attr": {}, "c": [{"production": "pipeline", "type": null, "value": null, "id": 1, "line": 1, "attr": {}, "c": [{"production": null, "type": "IDENT", "value": "_1997", "id": 2, "line": 1, "attr": {}, "c": []}, {"production": "component_contents", "type": null, "value": null, "id": 3, "line": -1, "attr": {}, "c": [{"production": "Gets", "type": null, "value": null, "id": 4, "line": 2, "attr": {}, "c": [{"production": "vardecl", "type": null, "value": null, "id": 5, "line": 2, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "gl_Position:", "id": 6, "line": 2, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 7, "line": -1, "attr": {}, "c": []}, {"production": "index", "type": null, "value": null, "id": 8, "line": -1, "attr": {}, "c": []}]}, {"production": "MMult", "type": null, "value": null, "id": 9, "line": 3, "attr": {}, "c": [{"production": "MMult", "type": null, "value": null, "id": 10, "line": 3, "attr": {}, "c": [{"production": "MMult", "type": null, "value": null, "id": 11, "line": 3, "attr": {}, "c": [{"production": "staged_vardecl", "type": null, "value": null, "id": 12, "line": 3, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "u[", "id": 13, "line": 3, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 14, "line": 3, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "projMatrix:", "id": 15, "line": 3, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 16, "line": -1, "attr": {}, "c": [{"production": "typeref", "type": null, "value": null, "id": 17, "line": 3, "attr": {}, "c": [{"production": null, "type": "IDENT", "value": "mat4", "id": 18, "line": 3, "attr": {}, "c": []}]}]}, {"production": "index", "type": null, "value": null, "id": 19, "line": -1, "attr": {}, "c": []}]}]}, {"production": "staged_vardecl", "type": null, "value": null, "id": 20, "line": 4, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "u[", "id": 21, "line": 4, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 22, "line": 4, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "viewMatrix:", "id": 23, "line": 4, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 24, "line": -1, "attr": {}, "c": [{"production": "typeref", "type": null, "value": null, "id": 25, "line": 4, "attr": {}, "c": [{"production": null, "type": "IDENT", "value": "mat4", "id": 26, "line": 4, "attr": {}, "c": []}]}]}, {"production": "index", "type": null, "value": null, "id": 27, "line": -1, "attr": {}, "c": []}]}]}]}, {"production": "staged_vardecl", "type": null, "value": null, "id": 28, "line": 5, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "u[", "id": 29, "line": 5, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 30, "line": 5, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "modelMatrix:", "id": 31, "line": 5, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 32, "line": -1, "attr": {}, "c": [{"production": "typeref", "type": null, "value": null, "id": 33, "line": 5, "attr": {}, "c": [{"production": null, "type": "IDENT", "value": "mat4", "id": 34, "line": 5, "attr": {}, "c": []}]}]}, {"production": "index", "type": null, "value": null, "id": 35, "line": -1, "attr": {}, "c": []}]}]}]}, {"production": "staged_vardecl", "type": null, "value": null, "id": 36, "line": 6, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "a[", "id": 37, "line": 6, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 38, "line": 6, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "position:", "id": 39, "line": 6, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 40, "line": -1, "attr": {}, "c": [{"production": "typeref", "type": null, "value": null, "id": 41, "line": 6, "attr": {}, "c": [{"production": null, "type": "IDENT", "value": "vec4", "id": 42, "line": 6, "attr": {}, "c": []}]}]}, {"production": "index", "type": null, "value": null, "id": 43, "line": -1, "attr": {}, "c": [{"production": null, "type": "INTEGER", "value": "0", "id": 44, "line": 6, "attr": {}, "c": []}]}]}]}]}]}, {"production": "Gets", "type": null, "value": null, "id": 45, "line": 8, "attr": {}, "c": [{"production": "staged_vardecl", "type": null, "value": null, "id": 46, "line": 8, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "f[", "id": 47, "line": 8, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 48, "line": 8, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "f_color:", "id": 49, "line": 8, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 50, "line": -1, "attr": {}, "c": []}, {"production": "index", "type": null, "value": null, "id": 51, "line": -1, "attr": {}, "c": [{"production": null, "type": "INTEGER", "value": "0", "id": 52, "line": 8, "attr": {}, "c": []}]}]}]}, {"production": "Gets", "type": null, "value": null, "id": 53, "line": 9, "attr": {}, "c": [{"production": "staged_vardecl", "type": null, "value": null, "id": 54, "line": 9, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "v[", "id": 55, "line": 9, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 56, "line": 9, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "v_color:", "id": 57, "line": 9, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 58, "line": -1, "attr": {}, "c": []}, {"production": "index", "type": null, "value": null, "id": 59, "line": -1, "attr": {}, "c": []}]}]}, {"production": "staged_vardecl", "type": null, "value": null, "id": 60, "line": 10, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "a[", "id": 61, "line": 10, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 62, "line": 10, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "a_color:", "id": 63, "line": 10, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 64, "line": -1, "attr": {}, "c": [{"production": "typeref", "type": null, "value": null, "id": 65, "line": 10, "attr": {}, "c": [{"production": null, "type": "IDENT", "value": "vec4", "id": 66, "line": 10, "attr": {}, "c": []}]}]}, {"production": "index", "type": null, "value": null, "id": 67, "line": -1, "attr": {}, "c": [{"production": null, "type": "INTEGER", "value": "1", "id": 68, "line": 10, "attr": {}, "c": []}]}]}]}]}]}, {"production": "Gets", "type": null, "value": null, "id": 69, "line": 14, "attr": {}, "c": [{"production": "vardecl", "type": null, "value": null, "id": 70, "line": 14, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "pi:", "id": 71, "line": 14, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 72, "line": -1, "attr": {}, "c": []}, {"production": "index", "type": null, "value": null, "id": 73, "line": -1, "attr": {}, "c": []}]}, {"production": null, "type": "FLOAT", "value": "3.14", "id": 74, "line": 14, "attr": {}, "c": []}]}]}]}]}], "styles": [], "edges": [], "links": [], "label_keys": ["production", "type"], "payload_objects": ["attr"]}`;
const N2_node_data = `{"nodes": [{"production": "global_list", "type": null, "value": null, "id": 0, "line": -1, "attr": {}, "c": [{"production": "pipeline", "type": null, "value": null, "id": 1, "line": 1, "attr": {}, "c": [{"production": null, "type": "IDENT", "value": "_1997", "id": 2, "line": 1, "attr": {}, "c": []}, {"production": "component_contents", "type": null, "value": null, "id": 3, "line": -1, "attr": {}, "c": [{"production": "Gets", "type": null, "value": null, "id": 4, "line": 2, "attr": {}, "c": [{"production": "staged_vardecl", "type": null, "value": null, "id": 5, "line": 2, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "f[", "id": 6, "line": 2, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 7, "line": 2, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "f_color:", "id": 8, "line": 2, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 9, "line": -1, "attr": {}, "c": []}, {"production": "index", "type": null, "value": null, "id": 10, "line": -1, "attr": {}, "c": [{"production": null, "type": "INTEGER", "value": "0", "id": 11, "line": 2, "attr": {}, "c": []}]}]}]}, {"production": "Gets", "type": null, "value": null, "id": 12, "line": 3, "attr": {}, "c": [{"production": "staged_vardecl", "type": null, "value": null, "id": 13, "line": 3, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "v[", "id": 14, "line": 3, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 15, "line": 3, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "v_color:", "id": 16, "line": 3, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 17, "line": -1, "attr": {}, "c": []}, {"production": "index", "type": null, "value": null, "id": 18, "line": -1, "attr": {}, "c": []}]}]}, {"production": "staged_vardecl", "type": null, "value": null, "id": 19, "line": 4, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "a[", "id": 20, "line": 4, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 21, "line": 4, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "a_color:", "id": 22, "line": 4, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 23, "line": -1, "attr": {}, "c": [{"production": "typeref", "type": null, "value": null, "id": 24, "line": 4, "attr": {}, "c": [{"production": null, "type": "IDENT", "value": "vec4", "id": 25, "line": 4, "attr": {}, "c": []}]}]}, {"production": "index", "type": null, "value": null, "id": 26, "line": -1, "attr": {}, "c": [{"production": null, "type": "INTEGER", "value": "1", "id": 27, "line": 4, "attr": {}, "c": []}]}]}]}]}]}, {"production": "Gets", "type": null, "value": null, "id": 28, "line": 8, "attr": {}, "c": [{"production": "vardecl", "type": null, "value": null, "id": 29, "line": 8, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "pi:", "id": 30, "line": 8, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 31, "line": -1, "attr": {}, "c": []}, {"production": "index", "type": null, "value": null, "id": 32, "line": -1, "attr": {}, "c": []}]}, {"production": null, "type": "FLOAT", "value": "3.14", "id": 33, "line": 8, "attr": {}, "c": []}]}]}]}]}], "styles": [], "edges": [], "links": [], "label_keys": ["production", "type"], "payload_objects": ["attr"]}`

// random graphs
const N3_node_data = `{"nodes": [{"!id": 0, "!label": "WTOEAMTB", "children": [{"!id": 1, "!label": "QLKEI", "children": []}, {"!id": 2, "!label": "AJUFJREXABEVYR", "children": [{"!id": 3, "!label": "OMBTL", "children": [{"!id": 4, "!label": "BHEVDXD", "children": [{"!id": 5, "!label": "TNXVYJXRSQEP", "children": []}]}, {"!id": 6, "!label": "TKKRTNPHESO", "children": [{"!id": 7, "!label": "TTVPCFPUN", "children": [{"!id": 8, "!label": "VDHQX", "children": [{"!id": 9, "!label": "VCOTQT", "children": [{"!id": 10, "!label": "EFSNTSSVVYF", "children": [{"!id": 11, "!label": "OHJLMBCMTUFRN", "children": [{"!id": 12, "!label": "KXFWTACNPFV", "children": []}, {"!id": 13, "!label": "MDJOTOOHTO", "children": []}, {"!id": 14, "!label": "IFYQIOANGA", "children": []}, {"!id": 15, "!label": "LGRITMAFAONCU", "children": []}]}]}, {"!id": 16, "!label": "CHRIFGUYBQK", "children": [{"!id": 17, "!label": "XQLTIGFMXQNEGO", "children": []}, {"!id": 18, "!label": "KOIYCJPPJGBF", "children": [{"!id": 19, "!label": "WRVRBHDO", "children": []}]}, {"!id": 20, "!label": "IGIEQPGKU", "children": []}]}, {"!id": 21, "!label": "ADSGRHHKND", "children": [{"!id": 22, "!label": "LROVCAKXKLJDV", "children": [{"!id": 23, "!label": "ISBQKYMKDG", "children": []}, {"!id": 24, "!label": "AACVGDGX", "children": []}, {"!id": 25, "!label": "RETOOORNY", "children": []}]}, {"!id": 26, "!label": "XQCEI", "children": [{"!id": 27, "!label": "UOSXNKINKJ", "children": []}]}]}]}]}]}, {"!id": 28, "!label": "NQLVB", "children": []}, {"!id": 29, "!label": "PFVXSTCWBRDW", "children": [{"!id": 30, "!label": "BKCRKY", "children": [{"!id": 31, "!label": "MWBDWHDVMDSPX", "children": [{"!id": 32, "!label": "IJAVPIP", "children": [{"!id": 33, "!label": "RKDVK", "children": [{"!id": 34, "!label": "APEKAG", "children": []}, {"!id": 35, "!label": "WWKDEDJBY", "children": []}, {"!id": 36, "!label": "PUHKSUHBOCLAE", "children": []}, {"!id": 37, "!label": "OQMGE", "children": []}]}]}]}, {"!id": 38, "!label": "CICMRWCCQVGG", "children": [{"!id": 39, "!label": "NOSBWTPPK", "children": []}]}]}, {"!id": 40, "!label": "OQIFPJR", "children": [{"!id": 41, "!label": "MVNUEEIKYQKPXM", "children": [{"!id": 42, "!label": "CSUHUYDR", "children": [{"!id": 43, "!label": "JIKLRTFXPM", "children": [{"!id": 44, "!label": "OAREIEDKDYHN", "children": []}, {"!id": 45, "!label": "FRVJUMUPGT", "children": []}, {"!id": 46, "!label": "KXXSOGNFWASTJS", "children": []}]}, {"!id": 47, "!label": "WNUQWE", "children": [{"!id": 48, "!label": "IRDHSMWPNYF", "children": []}, {"!id": 49, "!label": "TIFPOVXO", "children": []}]}]}]}]}]}]}]}]}]}], "styles": [], "edges": [], "links": [], "label_keys": [], "payload_objects": []}`
const N4_node_data = `{"nodes": [{"!id": 0, "!label": "RSWGTTVKPHAV", "children": [{"!id": 1, "!label": "UCOUGPLLGRK", "children": []}, {"!id": 2, "!label": "EXHCTEBVRXPA", "children": [{"!id": 3, "!label": "LRDXCQNOMIO", "children": [{"!id": 4, "!label": "YAFRWXMQMASYF", "children": [{"!id": 5, "!label": "TXWGKHRBPHAJN", "children": [{"!id": 6, "!label": "XKYTLED", "children": []}]}, {"!id": 7, "!label": "EOAFYTJYJGC", "children": [{"!id": 8, "!label": "LMWYXFQQDUV", "children": []}]}, {"!id": 9, "!label": "XDPDLPY", "children": [{"!id": 10, "!label": "KLWNSOQUBMJP", "children": [{"!id": 11, "!label": "GDVMUWR", "children": [{"!id": 12, "!label": "FXVSNRHKTPENWP", "children": [{"!id": 13, "!label": "QEEORNIG", "children": []}, {"!id": 14, "!label": "NXTKFSLXKEAUFU", "children": [{"!id": 15, "!label": "JBBMMS", "children": []}, {"!id": 16, "!label": "RMIMU", "children": []}]}, {"!id": 17, "!label": "LGOQGJAWFFIBL", "children": [{"!id": 18, "!label": "YNHSGIRYVJBBTQ", "children": []}, {"!id": 19, "!label": "NAMWW", "children": []}]}, {"!id": 20, "!label": "TMBNPNF", "children": []}]}, {"!id": 21, "!label": "WKCJQTDL", "children": [{"!id": 22, "!label": "YVLNWSEN", "children": [{"!id": 23, "!label": "GYMQNHEYXRLBT", "children": []}, {"!id": 24, "!label": "IEQNYQEUQLXRI", "children": []}, {"!id": 25, "!label": "YKKAEO", "children": []}]}, {"!id": 26, "!label": "YYBNBMU", "children": [{"!id": 27, "!label": "CDYHGNVPRJTUP", "children": []}]}]}]}, {"!id": 28, "!label": "UBNQLOITHQFGXX", "children": [{"!id": 29, "!label": "UPSRTMV", "children": [{"!id": 30, "!label": "BLODCPXFP", "children": [{"!id": 31, "!label": "VXDQCKAFKDP", "children": []}, {"!id": 32, "!label": "QPXLV", "children": []}]}, {"!id": 33, "!label": "BGJHDNGHBFNTE", "children": [{"!id": 34, "!label": "WVBHD", "children": []}, {"!id": 35, "!label": "KTWMAFMEOQCJF", "children": []}, {"!id": 36, "!label": "VCWSVPREY", "children": []}, {"!id": 37, "!label": "TITWKWICD", "children": []}]}]}, {"!id": 38, "!label": "SPPNKGY", "children": [{"!id": 39, "!label": "WILHQPS", "children": [{"!id": 40, "!label": "YRSOCLSBPK", "children": []}]}]}, {"!id": 41, "!label": "YDMHLCOVW", "children": [{"!id": 42, "!label": "TYBTLAQIRIF", "children": [{"!id": 43, "!label": "XBPUKIKMO", "children": []}]}, {"!id": 44, "!label": "ESDXTQOUBEIE", "children": [{"!id": 45, "!label": "VCRVNKSWDH", "children": []}, {"!id": 46, "!label": "VHQUADHIHROXB", "children": []}, {"!id": 47, "!label": "VVOLFMKEPRFNR", "children": []}]}]}]}, {"!id": 48, "!label": "XBHSCYAEAVQO", "children": [{"!id": 49, "!label": "ISLYQJLU", "children": []}]}]}]}]}]}]}]}], "styles": [], "edges": [], "links": [], "label_keys": [], "payload_objects": []}`
const N5_node_data = `{"nodes": [{"!id": 0, "!label": "GNKSJGQIU", "children": [{"!id": 1, "!label": "EFXMBOKOOCFNM", "children": [{"!id": 2, "!label": "CFKEQFIRELJ", "children": [{"!id": 3, "!label": "YJCLHTACCEXLU", "children": [{"!id": 4, "!label": "BERPVRKVSAE", "children": [{"!id": 5, "!label": "HEKYFLLNQX", "children": []}, {"!id": 6, "!label": "ACFSGIFBIS", "children": [{"!id": 7, "!label": "DXHBEUR", "children": [{"!id": 8, "!label": "SIDWNWRKTMG", "children": [{"!id": 9, "!label": "LIAPJUWUOPXHY", "children": [{"!id": 10, "!label": "CEFRV", "children": []}, {"!id": 11, "!label": "FGTFDVAYL", "children": []}]}]}, {"!id": 12, "!label": "ENTYTAJF", "children": [{"!id": 13, "!label": "VGUYGUK", "children": [{"!id": 14, "!label": "STJGWJMGWA", "children": []}, {"!id": 15, "!label": "DFAGIKDKOUTIDU", "children": []}, {"!id": 16, "!label": "UMGYXNKWKQG", "children": []}]}]}, {"!id": 17, "!label": "WRSYWPVKLRWRF", "children": [{"!id": 18, "!label": "TBBNXHVASKYU", "children": []}, {"!id": 19, "!label": "XKSOEXG", "children": [{"!id": 20, "!label": "RXIGDCWCNXM", "children": []}, {"!id": 21, "!label": "SXLVXTWXKV", "children": []}, {"!id": 22, "!label": "AEEGCBNLTXJPS", "children": []}, {"!id": 23, "!label": "KXODUPYKVIX", "children": []}]}, {"!id": 24, "!label": "RISUSQ", "children": [{"!id": 25, "!label": "KUWOMCXGJYYC", "children": []}]}]}, {"!id": 26, "!label": "WPNVAFGRGMHS", "children": [{"!id": 27, "!label": "THRRIXEJDXQF", "children": [{"!id": 28, "!label": "DMOMHALPMTB", "children": []}]}, {"!id": 29, "!label": "PGWCIKHFO", "children": [{"!id": 30, "!label": "UBGFCAYCOBVI", "children": []}, {"!id": 31, "!label": "PVSFQEQO", "children": []}, {"!id": 32, "!label": "TREJYE", "children": []}, {"!id": 33, "!label": "JBNGPHIUEGWM", "children": []}]}, {"!id": 34, "!label": "PHMYX", "children": [{"!id": 35, "!label": "HEAPLBAQAQLYEG", "children": []}]}]}]}, {"!id": 36, "!label": "GEMFW", "children": []}]}]}, {"!id": 37, "!label": "UEBOBJ", "children": [{"!id": 38, "!label": "BOYEGFGSUO", "children": [{"!id": 39, "!label": "YKCUHWGUW", "children": [{"!id": 40, "!label": "LGNJQ", "children": [{"!id": 41, "!label": "BAAJRVFUNLRLO", "children": [{"!id": 42, "!label": "FNJPHJSGDYQUC", "children": []}, {"!id": 43, "!label": "PHOVNN", "children": []}, {"!id": 44, "!label": "QWMHFDEKPHITP", "children": []}, {"!id": 45, "!label": "EHFXAWN", "children": []}]}, {"!id": 46, "!label": "SIUPXVNPMFIAAS", "children": [{"!id": 47, "!label": "ERCVGSJKM", "children": []}, {"!id": 48, "!label": "EHSYJLHGHYXLVR", "children": []}, {"!id": 49, "!label": "TEWGPLWSKKF", "children": []}]}]}]}]}]}]}]}]}]}], "styles": [], "edges": [], "links": [], "label_keys": [], "payload_objects": []}`