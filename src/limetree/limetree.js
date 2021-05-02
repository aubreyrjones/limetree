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

var DEFERRED_MOVE_MODE = true;


function sleep(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
}

function debug_step() {
    draw_all_configured();
    return sleep(100);
}

var finishedLayout = false;

const exrp = p => (1.5**p) * (0.15 ** (1 - p));

const RANK_SEPARATION = 100.0;
const BOX_W_MARGIN = 4;
const W_SEPARATION = 20;
const BOX_TOP_OFFSET = 26;
const BOX_HEIGHT = BOX_TOP_OFFSET + 10;

var LAYOUT_RECURSION_COUNTER = 0;
var DELTA_SUM_COUNTER = 0;
var LEFT_SIDE_COUNTER = 0;
var RIGHT_SIDE_COUNTER = 0;
var MOVE_COUNTER = 0;

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
        this.highlight = false;

        // tree debugging tags and whatnot.
        this.tag = false;
        this.tag2 = false;
        this.tag3 = false;
        this.tag4 = false;
        this.tag_common = 0;
        this.last_common = -1;
        this.moveCount = 0;
        this.lastMoveStep = -1;
        this.placedStep = -1;

        

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
        this.childIdeals = new Array();
        this.leftEdgeByRank = new Array(); // int -> RANK ORDER
        this.rightEdgeByRank = new Array(); // int -> RANK ORDER
    }

    rank_left_edge(rank) {
        if (rank < this.rank || rank > this.maxdepth) {return -1;}
        return this.leftEdgeByRank[rank - this.rank];
    }

    rank_right_edge(rank) {
        if (rank < this.rank || rank > this.maxdepth) {return -1;}
        return this.rightEdgeByRank[rank - this.rank];
    }

    subtree_left_edge() {
        let rval = new Array();
        for (let i = 0; i < this.leftEdgeByRank.length; i++) {
            rval.push(rank_list(this.rank + i)[this.leftEdgeByRank[i]]);
        }
        return rval;
    }

    subtree_right_edge() {
        let rval = new Array();
        for (let i = 0; i < this.rightEdgeByRank.length; i++) {
            rval.push(rank_list(this.rank + i)[this.rightEdgeByRank[i]]);
        }
        return rval;
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

    calculate_ideal_child_positions() {
        this.childIdeals = new Array();

        let childWidth = 0;
        this.children.forEach(e => childWidth += e.target.boxwidth);
        childWidth += W_SEPARATION * (this.count() - 1);

        let lStart = (-childWidth / 2.0) + this.halfw();
        for (let e of this.children) {
            this.childIdeals.push(lStart);
            lStart += e.target.boxwidth + W_SEPARATION;
        }
    }

    // collect the children's idea of subtree extrema
    sigma(rank) {
        let rval = {
            'l' : -1,
            'r' : -1
        };

        for (let e of this.children) {
            let cExtreme = e.target.rank_left_edge(rank);
            if (cExtreme >= 0) {
                rval['l'] = cExtreme;
                break;
            }
        }

        for (let e of Array.from(this.children).reverse()) {
            let cExtreme = e.target.rank_right_edge(rank);
            if (cExtreme >= 0) {
                rval['r'] = cExtreme;
                break;
            }
        }

        return rval;
    }

    rank_self(my_rank, parent_ancestors) {
        // set up ancestry query set.
        parent_ancestors.forEach(item => this.ancestors.add(item));
        if (this.parent) {
            this.ancestors.add(this.parent);
        }

        // rank children and collect their maximum depth
        let maxChildRank = my_rank;
        for (let edge of this.children) {
            let cRank = edge.target.rank_self(my_rank + 1, this.ancestors);
            if (cRank > maxChildRank) {
                maxChildRank = cRank;
            }
        }
        this.maxdepth = maxChildRank;

        // attach to rank structure
        this.rank = my_rank;
        let rl = rank_list(my_rank);
        this.rankorder = rl.length;
        rl.push(this);


        // subtree extrema
        this.leftEdgeByRank = new Array();
        this.rightEdgeByRank = new Array();
        this.leftEdgeByRank.push(this.rankorder); // our own level.
        this.rightEdgeByRank.push(this.rankorder);

        if (!this.leaf()) {
            let depthCount = this.maxdepth - this.rank; // must be non-zero for non-leaf
            for (let i = 0; i < depthCount; i++) {
                let r = i + this.rank + 1;
                let edges = this.sigma(r);
                this.leftEdgeByRank.push(edges['l']);
                this.rightEdgeByRank.push(edges['r']);
            }
        }

        // visual layout
        this.pos_y = this.rank * RANK_SEPARATION;

        return this.maxdepth;
    }

    highlight_edges(v1, v2) {
        if (!v2) v2 = v1;

        for (let n of this.subtree_left_edge()) {
            n.highlight = v1;
        }

        for (let n of this.subtree_right_edge()) {
            n.highlight = v2;
        }
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
        if (! DEFERRED_MOVE_MODE) return 0;

        this.tag4 = true;
        DELTA_SUM_COUNTER++;

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
        LEFT_SIDE_COUNTER++;
        this.tag2 = true;
        return this.x + this.delta_sum();
    }

    layout_right_side() {
        RIGHT_SIDE_COUNTER++;
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
        const tagged_common = this.tag_common;

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

        if (false && (tagged || tagged2 || tagged3 || tagged4 || tagged_common)) {
            ctx.lineWidth = 4;
            if (tagged) {
                ctx.strokeStyle = "red";
                ctx.strokeRect(this.pos_x - 4, this.top() - 4, this.boxwidth + 8, BOX_HEIGHT + 8);
            }
            if (tagged2) {
                ctx.strokeStyle = "blue";
                ctx.strokeRect(this.pos_x - 8, this.top() - 8, this.boxwidth + 16, BOX_HEIGHT + 16);
            }    
        }

        if (tagged_common) {
            ctx.lineWidth = 4;
            ctx.strokeStyle = "orange";
            ctx.strokeRect(this.pos_x - 16, this.top() - 16, this.boxwidth + 32, BOX_HEIGHT + 32);
        }

        if (this.last_common > 0) {
            ctx.lineWidth = 4;
            ctx.strokeStyle = "blue";
            ctx.strokeRect(this.pos_x - 12, this.top() - 12, this.boxwidth + 24, BOX_HEIGHT + 24);
        }
        
        ctx.lineWidth = 1;
        ctx.strokeStyle = style.outline;
        ctx.fillStyle = style.fillStyle;
        ctx.fillRect(this.pos_x, this.top(), this.boxwidth, BOX_HEIGHT);
        if (false && DEFERRED_MOVE_MODE && this.moveCount != 0) {
            ctx.lineWidth = 4;
            if (this.moveCount == 1) {
                ctx.strokeStyle = 'green';
            }
            else if (this.moveCount == 2) {
                ctx.strokeStyle = 'blue';
            }
            else {
                ctx.strokeStyle = 'red';
            }
            ctx.strokeRect(this.pos_x, this.top(), this.boxwidth, BOX_HEIGHT);
        }
        else {
            if (this.highlight) {
                ctx.strokeStyle = this.highlight;
                ctx.lineWidth = 6;
            }
            ctx.strokeRect(this.pos_x, this.top(), this.boxwidth, BOX_HEIGHT);
        }
        ctx.fillStyle = 'black';
        ctx.fillText(label, this.pos_x + BOX_W_MARGIN, this.pos_y);

        this.tag = false;
        this.tag2 = false;
        this.tag3 = false;
        this.tag4 = false;

        if (!finishedLayout) {
            this.highlight = false;
        }
    }
}

function find_common(a, b) {
    if (a === b) return b;
    if (a.parent === b.parent) return a.parent; // could be null if we passed in some root nodes, I guess?

    let ap = a.parent, bp = b.parent;

    while (ap.rank > bp.rank) {
        ap = ap.parent;
        if (ap.parent === bp) return bp;
    }

    while (bp.rank > ap.rank) {
        bp = bp.parent;
        if (bp.parent === ap) return ap;
    }

    while (ap != bp) {
        ap = ap.parent;
        bp = bp.parent;
    }

    return ap;
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
    LAYOUT_RECURSION_COUNTER++;
    v.placedStep = LAYOUT_RECURSION_COUNTER;

    if (v.rankorder > 0) {
        v.x = rank_left(v).layout_right_side() + distance;
        let common = find_common(v, rank_left(v));
        common.tag_common++;
        //common.last_common = LAYOUT_RECURSION_COUNTER;
    }
    else {
        v.x = 0.0;
    }

    await debug_step(); // DEBUG
    if (v.leaf()) {
        mark_wave(v);
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
    let natural = midpoint - v.halfw();
    v.x = natural; // set the natural midpoint, but we'll still adjust farther along
    
    
    let lefthandMargin = 0;
    let lefthand = rank_left(v);
    
    if (lefthand) {
        lefthandMargin = lefthand.layout_right_side() + distance;
    }

    let wantedMove = lefthandMargin - natural;

    do_constrained_move(v, wantedMove, false);

    v.tag_common = 0; // reset the counter now that we're "in place".

    const rearrangeInners = true;
    if (rearrangeInners) {
        //let myMid = v.layout_center();
        for (let e of v.children.slice(0).reverse()) {
            let c = e.target;
            let stress = v.layout_left_side() + v.childIdeals[c.sib_index] - c.layout_left_side();
            if (stress > 0) {
                do_constrained_move(c, stress, true);
            }
        }
    }

    if (v.tag_common > 0) {
        console.log(v.label, v.tag_common);
    }

    // if ('already_placed' in v.payload) {
    //     whatthefuck();
    // }
    // else {
    //     v.tag_common = 0; // reset the counter now that we're "in place".
    //     v.payload['already_placed'] = true;
    // }

    mark_wave(v);
    await debug_step(); // DEBUG
    return v;
}

function do_constrained_move(v, wantedMove, doRightCheck = true) {
    const nodeLocalEdgeLists = true;

    v.highlight_edges("orange");

    if (wantedMove == 0) { 
        return; 
    }
    else if (wantedMove < 0) { // we're moving left
        let leftEdge;
        if (nodeLocalEdgeLists) {
            v.tag3 = true;
            leftEdge = v.subtree_left_edge();
        } 
        else { 
            leftEdge = wavefront_subtree_left_edge(v) 
        };
        wantedMove = constrain_by_left_edge(leftEdge, wantedMove);
    }
    else if (doRightCheck && wantedMove > 0) {
        let rightEdge;
        if (nodeLocalEdgeLists) {
            v.tag3 = true;
            rightEdge = v.subtree_right_edge();
        }
        else {
            rightEdge = wavefront_subtree_right_edge(v);;
        }
        wantedMove = constrain_by_right_edge(rightEdge, wantedMove);
    }

    const deferred = DEFERRED_MOVE_MODE;
    if (deferred) {
        move_tree_deferred(v, wantedMove);
    }
    else {
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
    root.tag3 = true;
    let nextLeft = rank_left(startNode);
    
    while (nextLeft && nextLeft.descends_from(root)) {
        nextLeft.tag3 = true;
        startNode = nextLeft;
        nextLeft = rank_left(startNode);
    }

    return startNode;
}

function wavefront_subtree_left_edge(root) {
    root.tag3 = true;
    let edge = new Array();
    for (let i = root.rank; i <= root.maxdepth; i++) {
        let edgeNode = search_rank_left_for_descendant(root, i);
        if (!edgeNode) continue;
        edge.push(search_rank_for_left_edge(root, edgeNode));
        
    }
    return edge;
}

var wavefront_subtree_right_edge = function(root) {
    root.tag3 = true;
    let edge = new Array();
    for (let i = root.rank; i <= root.maxdepth; i++) {
        let edgeNode = search_rank_left_for_descendant(root, i);
        if (!edgeNode) continue;
        edge.push(edgeNode);
    }
    return edge;
}

function constrain_by_left_edge(edge_list, amount) {
    let commons = new Set();

    for (let v of edge_list) {

        if (v.rankorder == 0) {
            continue;
        }

        let common = find_common(v, rank_left(v));
        if (!commons.has(common)) {
            common.tag_common++;
            common.last_common = LAYOUT_RECURSION_COUNTER;
            commons.add(common);
        }

        let leftmargin = rank_left(v).layout_right_side() + W_SEPARATION;
        let targetX = v.layout_left_side() + amount;
        
        let overlap = targetX - leftmargin;
    
        
        if (overlap < 0) {
            amount -= overlap;
        }
    }

    commons.forEach( n => n.highlight_edges("red"));

    console.log("commons", commons.size);
    return amount;
}

function constrain_by_right_edge(edge_list, amount) {
    let commons = new Set();

    for (let v of edge_list) {
        let rightNeighbor = rank_right(v);
        if (!rightNeighbor) continue;

        let common = find_common(v, rightNeighbor);
        if (!commons.has(common)) {
            common.tag_common++;
            common.last_common = LAYOUT_RECURSION_COUNTER;
            commons.add(common);
        }

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
    root.delta += amount;

    MOVE_COUNTER++;
    root.moveCount++;
    root.lastMoveStep = LAYOUT_RECURSION_COUNTER;
}

var move_tree = function(v, amount) {
    MOVE_COUNTER++;
    v.tag4 = true;
    root.lastMoveStep = LAYOUT_RECURSION_COUNTER;

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

    if (_displayed_node) {
        _displayed_node.highlight_edges(false);
    }

    _displayed_node = n;
    _displayed_node.highlight_edges("orange", "cyan");
    if (finishedLayout) {
        draw_all_configured();
    }

    let info_div = document.getElementById("node_info");
    info_div.innerText = "";
    let extra = {
        "delta" : n.delta, 
        "deltasum" : n.non_tagging_delta_sum(), 
        "id" : n.id,
        "node moves" : n.moveCount,
        "placed at" : n.placedStep,
        "last move" : n.lastMoveStep,
        "last common" : n.last_common,
        "common count" : n.tag_common,
        "depth" : n.maxdepth, 
        "n nodes" : Object.keys(_all_nodes).length,
        "layout count" : LAYOUT_RECURSION_COUNTER,
        "sum count" : DELTA_SUM_COUNTER,
        "left count" : LEFT_SIDE_COUNTER,
        "right count" : RIGHT_SIDE_COUNTER,
        "total moves" : MOVE_COUNTER
    };
    layout_obj(info_div, n.label || n.id, n.payload, extra);
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
    iter_all(n => n.calculate_ideal_child_positions());

    layout_tree(_root_node);
    
    
    draw_all_configured();
}

// parse trees
const n1_node_data = `{"nodes": [{"production": "global_list", "type": null, "value": null, "id": 0, "line": -1, "attr": {}, "c": [{"production": "pipeline", "type": null, "value": null, "id": 1, "line": 1, "attr": {}, "c": [{"production": null, "type": "IDENT", "value": "_1997", "id": 2, "line": 1, "attr": {}, "c": []}, {"production": "component_contents", "type": null, "value": null, "id": 3, "line": -1, "attr": {}, "c": [{"production": "Gets", "type": null, "value": null, "id": 4, "line": 2, "attr": {}, "c": [{"production": "vardecl", "type": null, "value": null, "id": 5, "line": 2, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "gl_Position:", "id": 6, "line": 2, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 7, "line": -1, "attr": {}, "c": []}, {"production": "index", "type": null, "value": null, "id": 8, "line": -1, "attr": {}, "c": []}]}, {"production": "MMult", "type": null, "value": null, "id": 9, "line": 3, "attr": {}, "c": [{"production": "MMult", "type": null, "value": null, "id": 10, "line": 3, "attr": {}, "c": [{"production": "MMult", "type": null, "value": null, "id": 11, "line": 3, "attr": {}, "c": [{"production": "staged_vardecl", "type": null, "value": null, "id": 12, "line": 3, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "u[", "id": 13, "line": 3, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 14, "line": 3, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "projMatrix:", "id": 15, "line": 3, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 16, "line": -1, "attr": {}, "c": [{"production": "typeref", "type": null, "value": null, "id": 17, "line": 3, "attr": {}, "c": [{"production": null, "type": "IDENT", "value": "mat4", "id": 18, "line": 3, "attr": {}, "c": []}]}]}, {"production": "index", "type": null, "value": null, "id": 19, "line": -1, "attr": {}, "c": []}]}]}, {"production": "staged_vardecl", "type": null, "value": null, "id": 20, "line": 4, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "u[", "id": 21, "line": 4, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 22, "line": 4, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "viewMatrix:", "id": 23, "line": 4, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 24, "line": -1, "attr": {}, "c": [{"production": "typeref", "type": null, "value": null, "id": 25, "line": 4, "attr": {}, "c": [{"production": null, "type": "IDENT", "value": "mat4", "id": 26, "line": 4, "attr": {}, "c": []}]}]}, {"production": "index", "type": null, "value": null, "id": 27, "line": -1, "attr": {}, "c": []}]}]}]}, {"production": "staged_vardecl", "type": null, "value": null, "id": 28, "line": 5, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "u[", "id": 29, "line": 5, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 30, "line": 5, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "modelMatrix:", "id": 31, "line": 5, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 32, "line": -1, "attr": {}, "c": [{"production": "typeref", "type": null, "value": null, "id": 33, "line": 5, "attr": {}, "c": [{"production": null, "type": "IDENT", "value": "mat4", "id": 34, "line": 5, "attr": {}, "c": []}]}]}, {"production": "index", "type": null, "value": null, "id": 35, "line": -1, "attr": {}, "c": []}]}]}]}, {"production": "staged_vardecl", "type": null, "value": null, "id": 36, "line": 6, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "a[", "id": 37, "line": 6, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 38, "line": 6, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "position:", "id": 39, "line": 6, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 40, "line": -1, "attr": {}, "c": [{"production": "typeref", "type": null, "value": null, "id": 41, "line": 6, "attr": {}, "c": [{"production": null, "type": "IDENT", "value": "vec4", "id": 42, "line": 6, "attr": {}, "c": []}]}]}, {"production": "index", "type": null, "value": null, "id": 43, "line": -1, "attr": {}, "c": [{"production": null, "type": "INTEGER", "value": "0", "id": 44, "line": 6, "attr": {}, "c": []}]}]}]}]}]}, {"production": "Gets", "type": null, "value": null, "id": 45, "line": 8, "attr": {}, "c": [{"production": "staged_vardecl", "type": null, "value": null, "id": 46, "line": 8, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "f[", "id": 47, "line": 8, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 48, "line": 8, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "f_color:", "id": 49, "line": 8, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 50, "line": -1, "attr": {}, "c": []}, {"production": "index", "type": null, "value": null, "id": 51, "line": -1, "attr": {}, "c": [{"production": null, "type": "INTEGER", "value": "0", "id": 52, "line": 8, "attr": {}, "c": []}]}]}]}, {"production": "Gets", "type": null, "value": null, "id": 53, "line": 9, "attr": {}, "c": [{"production": "staged_vardecl", "type": null, "value": null, "id": 54, "line": 9, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "v[", "id": 55, "line": 9, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 56, "line": 9, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "v_color:", "id": 57, "line": 9, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 58, "line": -1, "attr": {}, "c": []}, {"production": "index", "type": null, "value": null, "id": 59, "line": -1, "attr": {}, "c": []}]}]}, {"production": "staged_vardecl", "type": null, "value": null, "id": 60, "line": 10, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "a[", "id": 61, "line": 10, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 62, "line": 10, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "a_color:", "id": 63, "line": 10, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 64, "line": -1, "attr": {}, "c": [{"production": "typeref", "type": null, "value": null, "id": 65, "line": 10, "attr": {}, "c": [{"production": null, "type": "IDENT", "value": "vec4", "id": 66, "line": 10, "attr": {}, "c": []}]}]}, {"production": "index", "type": null, "value": null, "id": 67, "line": -1, "attr": {}, "c": [{"production": null, "type": "INTEGER", "value": "1", "id": 68, "line": 10, "attr": {}, "c": []}]}]}]}]}]}, {"production": "Gets", "type": null, "value": null, "id": 69, "line": 14, "attr": {}, "c": [{"production": "vardecl", "type": null, "value": null, "id": 70, "line": 14, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "pi:", "id": 71, "line": 14, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 72, "line": -1, "attr": {}, "c": []}, {"production": "index", "type": null, "value": null, "id": 73, "line": -1, "attr": {}, "c": []}]}, {"production": null, "type": "FLOAT", "value": "3.14", "id": 74, "line": 14, "attr": {}, "c": []}]}]}]}]}], "styles": [], "edges": [], "links": [], "label_keys": ["production", "type"], "payload_objects": ["attr"]}`;
const n2_node_data = `{"nodes": [{"production": "global_list", "type": null, "value": null, "id": 0, "line": -1, "attr": {}, "c": [{"production": "pipeline", "type": null, "value": null, "id": 1, "line": 1, "attr": {}, "c": [{"production": null, "type": "IDENT", "value": "_1997", "id": 2, "line": 1, "attr": {}, "c": []}, {"production": "component_contents", "type": null, "value": null, "id": 3, "line": -1, "attr": {}, "c": [{"production": "Gets", "type": null, "value": null, "id": 4, "line": 2, "attr": {}, "c": [{"production": "staged_vardecl", "type": null, "value": null, "id": 5, "line": 2, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "f[", "id": 6, "line": 2, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 7, "line": 2, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "f_color:", "id": 8, "line": 2, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 9, "line": -1, "attr": {}, "c": []}, {"production": "index", "type": null, "value": null, "id": 10, "line": -1, "attr": {}, "c": [{"production": null, "type": "INTEGER", "value": "0", "id": 11, "line": 2, "attr": {}, "c": []}]}]}]}, {"production": "Gets", "type": null, "value": null, "id": 12, "line": 3, "attr": {}, "c": [{"production": "staged_vardecl", "type": null, "value": null, "id": 13, "line": 3, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "v[", "id": 14, "line": 3, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 15, "line": 3, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "v_color:", "id": 16, "line": 3, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 17, "line": -1, "attr": {}, "c": []}, {"production": "index", "type": null, "value": null, "id": 18, "line": -1, "attr": {}, "c": []}]}]}, {"production": "staged_vardecl", "type": null, "value": null, "id": 19, "line": 4, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "a[", "id": 20, "line": 4, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 21, "line": 4, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "a_color:", "id": 22, "line": 4, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 23, "line": -1, "attr": {}, "c": [{"production": "typeref", "type": null, "value": null, "id": 24, "line": 4, "attr": {}, "c": [{"production": null, "type": "IDENT", "value": "vec4", "id": 25, "line": 4, "attr": {}, "c": []}]}]}, {"production": "index", "type": null, "value": null, "id": 26, "line": -1, "attr": {}, "c": [{"production": null, "type": "INTEGER", "value": "1", "id": 27, "line": 4, "attr": {}, "c": []}]}]}]}]}]}, {"production": "Gets", "type": null, "value": null, "id": 28, "line": 8, "attr": {}, "c": [{"production": "vardecl", "type": null, "value": null, "id": 29, "line": 8, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "pi:", "id": 30, "line": 8, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 31, "line": -1, "attr": {}, "c": []}, {"production": "index", "type": null, "value": null, "id": 32, "line": -1, "attr": {}, "c": []}]}, {"production": null, "type": "FLOAT", "value": "3.14", "id": 33, "line": 8, "attr": {}, "c": []}]}]}]}]}], "styles": [], "edges": [], "links": [], "label_keys": ["production", "type"], "payload_objects": ["attr"]}`

// random graphs
const n3_node_data = `{"nodes": [{"!id": 0, "!label": "WTOEAMTB", "children": [{"!id": 1, "!label": "QLKEI", "children": []}, {"!id": 2, "!label": "AJUFJREXABEVYR", "children": [{"!id": 3, "!label": "OMBTL", "children": [{"!id": 4, "!label": "BHEVDXD", "children": [{"!id": 5, "!label": "TNXVYJXRSQEP", "children": []}]}, {"!id": 6, "!label": "TKKRTNPHESO", "children": [{"!id": 7, "!label": "TTVPCFPUN", "children": [{"!id": 8, "!label": "VDHQX", "children": [{"!id": 9, "!label": "VCOTQT", "children": [{"!id": 10, "!label": "EFSNTSSVVYF", "children": [{"!id": 11, "!label": "OHJLMBCMTUFRN", "children": [{"!id": 12, "!label": "KXFWTACNPFV", "children": []}, {"!id": 13, "!label": "MDJOTOOHTO", "children": []}, {"!id": 14, "!label": "IFYQIOANGA", "children": []}, {"!id": 15, "!label": "LGRITMAFAONCU", "children": []}]}]}, {"!id": 16, "!label": "CHRIFGUYBQK", "children": [{"!id": 17, "!label": "XQLTIGFMXQNEGO", "children": []}, {"!id": 18, "!label": "KOIYCJPPJGBF", "children": [{"!id": 19, "!label": "WRVRBHDO", "children": []}]}, {"!id": 20, "!label": "IGIEQPGKU", "children": []}]}, {"!id": 21, "!label": "ADSGRHHKND", "children": [{"!id": 22, "!label": "LROVCAKXKLJDV", "children": [{"!id": 23, "!label": "ISBQKYMKDG", "children": []}, {"!id": 24, "!label": "AACVGDGX", "children": []}, {"!id": 25, "!label": "RETOOORNY", "children": []}]}, {"!id": 26, "!label": "XQCEI", "children": [{"!id": 27, "!label": "UOSXNKINKJ", "children": []}]}]}]}]}]}, {"!id": 28, "!label": "NQLVB", "children": []}, {"!id": 29, "!label": "PFVXSTCWBRDW", "children": [{"!id": 30, "!label": "BKCRKY", "children": [{"!id": 31, "!label": "MWBDWHDVMDSPX", "children": [{"!id": 32, "!label": "IJAVPIP", "children": [{"!id": 33, "!label": "RKDVK", "children": [{"!id": 34, "!label": "APEKAG", "children": []}, {"!id": 35, "!label": "WWKDEDJBY", "children": []}, {"!id": 36, "!label": "PUHKSUHBOCLAE", "children": []}, {"!id": 37, "!label": "OQMGE", "children": []}]}]}]}, {"!id": 38, "!label": "CICMRWCCQVGG", "children": [{"!id": 39, "!label": "NOSBWTPPK", "children": []}]}]}, {"!id": 40, "!label": "OQIFPJR", "children": [{"!id": 41, "!label": "MVNUEEIKYQKPXM", "children": [{"!id": 42, "!label": "CSUHUYDR", "children": [{"!id": 43, "!label": "JIKLRTFXPM", "children": [{"!id": 44, "!label": "OAREIEDKDYHN", "children": []}, {"!id": 45, "!label": "FRVJUMUPGT", "children": []}, {"!id": 46, "!label": "KXXSOGNFWASTJS", "children": []}]}, {"!id": 47, "!label": "WNUQWE", "children": [{"!id": 48, "!label": "IRDHSMWPNYF", "children": []}, {"!id": 49, "!label": "TIFPOVXO", "children": []}]}]}]}]}]}]}]}]}]}], "styles": [], "edges": [], "links": [], "label_keys": [], "payload_objects": []}`
const n4_node_data = `{"nodes": [{"!id": 0, "!label": "RSWGTTVKPHAV", "children": [{"!id": 1, "!label": "UCOUGPLLGRK", "children": []}, {"!id": 2, "!label": "EXHCTEBVRXPA", "children": [{"!id": 3, "!label": "LRDXCQNOMIO", "children": [{"!id": 4, "!label": "YAFRWXMQMASYF", "children": [{"!id": 5, "!label": "TXWGKHRBPHAJN", "children": [{"!id": 6, "!label": "XKYTLED", "children": []}]}, {"!id": 7, "!label": "EOAFYTJYJGC", "children": [{"!id": 8, "!label": "LMWYXFQQDUV", "children": []}]}, {"!id": 9, "!label": "XDPDLPY", "children": [{"!id": 10, "!label": "KLWNSOQUBMJP", "children": [{"!id": 11, "!label": "GDVMUWR", "children": [{"!id": 12, "!label": "FXVSNRHKTPENWP", "children": [{"!id": 13, "!label": "QEEORNIG", "children": []}, {"!id": 14, "!label": "NXTKFSLXKEAUFU", "children": [{"!id": 15, "!label": "JBBMMS", "children": []}, {"!id": 16, "!label": "RMIMU", "children": []}]}, {"!id": 17, "!label": "LGOQGJAWFFIBL", "children": [{"!id": 18, "!label": "YNHSGIRYVJBBTQ", "children": []}, {"!id": 19, "!label": "NAMWW", "children": []}]}, {"!id": 20, "!label": "TMBNPNF", "children": []}]}, {"!id": 21, "!label": "WKCJQTDL", "children": [{"!id": 22, "!label": "YVLNWSEN", "children": [{"!id": 23, "!label": "GYMQNHEYXRLBT", "children": []}, {"!id": 24, "!label": "IEQNYQEUQLXRI", "children": []}, {"!id": 25, "!label": "YKKAEO", "children": []}]}, {"!id": 26, "!label": "YYBNBMU", "children": [{"!id": 27, "!label": "CDYHGNVPRJTUP", "children": []}]}]}]}, {"!id": 28, "!label": "UBNQLOITHQFGXX", "children": [{"!id": 29, "!label": "UPSRTMV", "children": [{"!id": 30, "!label": "BLODCPXFP", "children": [{"!id": 31, "!label": "VXDQCKAFKDP", "children": []}, {"!id": 32, "!label": "QPXLV", "children": []}]}, {"!id": 33, "!label": "BGJHDNGHBFNTE", "children": [{"!id": 34, "!label": "WVBHD", "children": []}, {"!id": 35, "!label": "KTWMAFMEOQCJF", "children": []}, {"!id": 36, "!label": "VCWSVPREY", "children": []}, {"!id": 37, "!label": "TITWKWICD", "children": []}]}]}, {"!id": 38, "!label": "SPPNKGY", "children": [{"!id": 39, "!label": "WILHQPS", "children": [{"!id": 40, "!label": "YRSOCLSBPK", "children": []}]}]}, {"!id": 41, "!label": "YDMHLCOVW", "children": [{"!id": 42, "!label": "TYBTLAQIRIF", "children": [{"!id": 43, "!label": "XBPUKIKMO", "children": []}]}, {"!id": 44, "!label": "ESDXTQOUBEIE", "children": [{"!id": 45, "!label": "VCRVNKSWDH", "children": []}, {"!id": 46, "!label": "VHQUADHIHROXB", "children": []}, {"!id": 47, "!label": "VVOLFMKEPRFNR", "children": []}]}]}]}, {"!id": 48, "!label": "XBHSCYAEAVQO", "children": [{"!id": 49, "!label": "ISLYQJLU", "children": []}]}]}]}]}]}]}]}], "styles": [], "edges": [], "links": [], "label_keys": [], "payload_objects": []}`
const n5_node_data = `{"nodes": [{"!id": 0, "!label": "GNKSJGQIU", "children": [{"!id": 1, "!label": "EFXMBOKOOCFNM", "children": [{"!id": 2, "!label": "CFKEQFIRELJ", "children": [{"!id": 3, "!label": "YJCLHTACCEXLU", "children": [{"!id": 4, "!label": "BERPVRKVSAE", "children": [{"!id": 5, "!label": "HEKYFLLNQX", "children": []}, {"!id": 6, "!label": "ACFSGIFBIS", "children": [{"!id": 7, "!label": "DXHBEUR", "children": [{"!id": 8, "!label": "SIDWNWRKTMG", "children": [{"!id": 9, "!label": "LIAPJUWUOPXHY", "children": [{"!id": 10, "!label": "CEFRV", "children": []}, {"!id": 11, "!label": "FGTFDVAYL", "children": []}]}]}, {"!id": 12, "!label": "ENTYTAJF", "children": [{"!id": 13, "!label": "VGUYGUK", "children": [{"!id": 14, "!label": "STJGWJMGWA", "children": []}, {"!id": 15, "!label": "DFAGIKDKOUTIDU", "children": []}, {"!id": 16, "!label": "UMGYXNKWKQG", "children": []}]}]}, {"!id": 17, "!label": "WRSYWPVKLRWRF", "children": [{"!id": 18, "!label": "TBBNXHVASKYU", "children": []}, {"!id": 19, "!label": "XKSOEXG", "children": [{"!id": 20, "!label": "RXIGDCWCNXM", "children": []}, {"!id": 21, "!label": "SXLVXTWXKV", "children": []}, {"!id": 22, "!label": "AEEGCBNLTXJPS", "children": []}, {"!id": 23, "!label": "KXODUPYKVIX", "children": []}]}, {"!id": 24, "!label": "RISUSQ", "children": [{"!id": 25, "!label": "KUWOMCXGJYYC", "children": []}]}]}, {"!id": 26, "!label": "WPNVAFGRGMHS", "children": [{"!id": 27, "!label": "THRRIXEJDXQF", "children": [{"!id": 28, "!label": "DMOMHALPMTB", "children": []}]}, {"!id": 29, "!label": "PGWCIKHFO", "children": [{"!id": 30, "!label": "UBGFCAYCOBVI", "children": []}, {"!id": 31, "!label": "PVSFQEQO", "children": []}, {"!id": 32, "!label": "TREJYE", "children": []}, {"!id": 33, "!label": "JBNGPHIUEGWM", "children": []}]}, {"!id": 34, "!label": "PHMYX", "children": [{"!id": 35, "!label": "HEAPLBAQAQLYEG", "children": []}]}]}]}, {"!id": 36, "!label": "GEMFW", "children": []}]}]}, {"!id": 37, "!label": "UEBOBJ", "children": [{"!id": 38, "!label": "BOYEGFGSUO", "children": [{"!id": 39, "!label": "YKCUHWGUW", "children": [{"!id": 40, "!label": "LGNJQ", "children": [{"!id": 41, "!label": "BAAJRVFUNLRLO", "children": [{"!id": 42, "!label": "FNJPHJSGDYQUC", "children": []}, {"!id": 43, "!label": "PHOVNN", "children": []}, {"!id": 44, "!label": "QWMHFDEKPHITP", "children": []}, {"!id": 45, "!label": "EHFXAWN", "children": []}]}, {"!id": 46, "!label": "SIUPXVNPMFIAAS", "children": [{"!id": 47, "!label": "ERCVGSJKM", "children": []}, {"!id": 48, "!label": "EHSYJLHGHYXLVR", "children": []}, {"!id": 49, "!label": "TEWGPLWSKKF", "children": []}]}]}]}]}]}]}]}]}]}], "styles": [], "edges": [], "links": [], "label_keys": [], "payload_objects": []}`
const n6_node_data = `{"nodes": [{"!id": 0, "!label": "WNEOUTYH", "children": [{"!id": 1, "!label": "YXPPULM", "children": [{"!id": 2, "!label": "QMIPOBJPEMYYKLBEWOJNKRTTMFON", "children": [{"!id": 3, "!label": "OEMDVQJMPAJFBB", "children": [{"!id": 4, "!label": "UDAARBFI", "children": []}, {"!id": 5, "!label": "REIOECEX", "children": [{"!id": 6, "!label": "EUWAXWIWQIWL", "children": []}, {"!id": 7, "!label": "XUKYLAJYELNJCKFOEDAEGRWYYRW", "children": [{"!id": 8, "!label": "YVOGWUHYWAKBGDWLESHOPXRIG", "children": []}, {"!id": 9, "!label": "BNQWKTGPRQGYUMDTE", "children": [{"!id": 10, "!label": "BMAEDOMMDUNJGKCJEXGQJGS", "children": []}, {"!id": 11, "!label": "CXEFGYKDUMVIENGDIEPFJMY", "children": [{"!id": 12, "!label": "COEHIBCCUXDVOYESEWRDSV", "children": []}, {"!id": 13, "!label": "OKQAHNDTPNUDCACB", "children": []}, {"!id": 14, "!label": "WDDJDSJJCSTAHRXPBNB", "children": [{"!id": 15, "!label": "TOFOPBSOVYDMWATXYW", "children": []}, {"!id": 16, "!label": "VKNIXQKEFQDGKIGERSKIDXBBP", "children": []}, {"!id": 17, "!label": "LCKUMAPLYKUSYSVHFQYYCGTTRSM", "children": []}, {"!id": 18, "!label": "POIMEIAMEXAPWPJGVGKQCDJ", "children": []}]}]}]}, {"!id": 19, "!label": "TBDFEWWWBYXBFIGG", "children": []}, {"!id": 20, "!label": "NPKMIXXSPIFMKHA", "children": [{"!id": 21, "!label": "NLBKPBHOVO", "children": []}, {"!id": 22, "!label": "PEODUIRDRIKUYLTBCEGJITX", "children": [{"!id": 23, "!label": "LUMCOVIHECNTVMNOCAXULBNGGB", "children": [{"!id": 24, "!label": "LEYSVFX", "children": []}, {"!id": 25, "!label": "PWDFPCUCSNUNPFNOD", "children": []}, {"!id": 26, "!label": "HAUIYJQWQGIXUBEUJQ", "children": []}, {"!id": 27, "!label": "QYLORCKJQ", "children": []}, {"!id": 28, "!label": "BLXCQNGPAYRORQDM", "children": []}, {"!id": 29, "!label": "SSSIYWKYEWUFHID", "children": []}, {"!id": 30, "!label": "RBNQJRBDXMOS", "children": []}]}, {"!id": 31, "!label": "XSIUAHQSE", "children": []}, {"!id": 32, "!label": "GKXBCJSFBNJCENOVBGTGAXOERBC", "children": []}, {"!id": 33, "!label": "WPNOBCICSTVGJTDFH", "children": []}, {"!id": 34, "!label": "DPQHWMKWAMEX", "children": []}, {"!id": 35, "!label": "FLXPUKLNATAP", "children": []}]}, {"!id": 36, "!label": "LJHYNKSHVCEKGGE", "children": [{"!id": 37, "!label": "KVRPQLNUQUOGIAJCM", "children": []}, {"!id": 38, "!label": "LALMREWGLGC", "children": [{"!id": 39, "!label": "KVQKNCCHLUHWRGEHQVGTXMV", "children": []}, {"!id": 40, "!label": "ATWNTOGRGGTTVGORC", "children": []}, {"!id": 41, "!label": "DLPUBKDVCTBCCCLDWQNYOEPOF", "children": []}, {"!id": 42, "!label": "VRBFEWQU", "children": []}, {"!id": 43, "!label": "MSXARMGNFGAHCYKWJRIHI", "children": []}]}, {"!id": 44, "!label": "BGOLRWSOHRUIJCLOPDYNOW", "children": []}, {"!id": 45, "!label": "WYLKALKBCKIIWX", "children": []}, {"!id": 46, "!label": "LEWADDOEHYQXOHIHYR", "children": []}, {"!id": 47, "!label": "QCMBVKKH", "children": [{"!id": 48, "!label": "WJLUDVWLSRVIUEBLWUTRVHFDMYTE", "children": []}, {"!id": 49, "!label": "GUHNJECC", "children": []}, {"!id": 50, "!label": "ASYGURJSTPURNXHFAOLNNH", "children": []}, {"!id": 51, "!label": "OJAXHGKUVVJAOGWADOOYD", "children": []}, {"!id": 52, "!label": "QULGYD", "children": []}]}]}, {"!id": 53, "!label": "HOVELKGCAQJAQABTOEMPOIBEXQV", "children": []}, {"!id": 54, "!label": "KVFHLQCNINTNPYHLR", "children": []}, {"!id": 55, "!label": "ENKGOHHGDJQAATCTIITXJGDBIL", "children": []}, {"!id": 56, "!label": "JANSQKBFFNHNSXYS", "children": []}]}, {"!id": 57, "!label": "JMTWKAVMV", "children": []}]}, {"!id": 58, "!label": "OKXWWRIQYYINLKHATOQLRAYJWTOJ", "children": [{"!id": 59, "!label": "KJTNM", "children": []}, {"!id": 60, "!label": "IIDSIYLGBAPFYQDHKNOCFIW", "children": []}, {"!id": 61, "!label": "PSSJCTGDAKPQEU", "children": []}, {"!id": 62, "!label": "JGNYBFUQHCF", "children": []}, {"!id": 63, "!label": "TEDCLERMNOTAHNDAURQSMRQLQDPN", "children": []}, {"!id": 64, "!label": "BRMAEBVJ", "children": [{"!id": 65, "!label": "LTHSDXWSWXXJIFKNUEUTTTEFSMO", "children": []}]}, {"!id": 66, "!label": "QMTOFGGQYGMULIN", "children": [{"!id": 67, "!label": "WFINTGSJLSDXHONPSFD", "children": []}, {"!id": 68, "!label": "QCEHOJRWNKLFCPXXSD", "children": [{"!id": 69, "!label": "TDSBNJPIBXDM", "children": [{"!id": 70, "!label": "XQUFMKYSTPPQNIXYCDRSJOWIHKYK", "children": []}, {"!id": 71, "!label": "XBJOCOWOCLISCAPIUNWK", "children": []}, {"!id": 72, "!label": "XIFSOBHVUINOCF", "children": []}, {"!id": 73, "!label": "PBEIRYIBBLWLJTQBNAIYHHGBL", "children": []}]}, {"!id": 74, "!label": "QMECNJJWAPXSKXBSOLHBALI", "children": []}, {"!id": 75, "!label": "FMWJTJRU", "children": []}]}]}]}, {"!id": 76, "!label": "QTNTOCHXMMQDTSKXIPYRYCL", "children": [{"!id": 77, "!label": "NIXPREHI", "children": [{"!id": 78, "!label": "USCWXTIJJAJKXOFL", "children": []}]}, {"!id": 79, "!label": "GSFABUIMVQQP", "children": []}, {"!id": 80, "!label": "BTQOMOVBWUTDHAHTFHFUHNAY", "children": []}, {"!id": 81, "!label": "POMQT", "children": []}, {"!id": 82, "!label": "BQWNMSPAKMMYJANFBGRULKRKWJIKS", "children": []}]}, {"!id": 83, "!label": "JXTSCPUTBU", "children": []}, {"!id": 84, "!label": "PLBGSQQMQERSJJXMYLDA", "children": [{"!id": 85, "!label": "BDSCHRXDCAFFOQEFDGTXQSUW", "children": [{"!id": 86, "!label": "LUYRJE", "children": []}, {"!id": 87, "!label": "OQJXFHLRIJ", "children": []}, {"!id": 88, "!label": "OXYBLUAWGFN", "children": [{"!id": 89, "!label": "BMRDVLWVGDNUUPBGIDUGORK", "children": []}, {"!id": 90, "!label": "YQUMXCDBSYDCY", "children": []}]}, {"!id": 91, "!label": "IXOCSQMDIBUMTGFBOJA", "children": [{"!id": 92, "!label": "DXIMMTLNNVJFXSBSUBJ", "children": []}, {"!id": 93, "!label": "CFFQHXUURRSKMNHKE", "children": []}, {"!id": 94, "!label": "IQUJRVXTSETENHPSEUKGNC", "children": []}, {"!id": 95, "!label": "ENHKARENLPOTWOLEJFILHONUOPLG", "children": []}, {"!id": 96, "!label": "TJHIYAEMM", "children": []}]}, {"!id": 97, "!label": "VHBWTWPXCSXBMIIDI", "children": [{"!id": 98, "!label": "GTPDLNJCOLDOPLXFSNJQRWPS", "children": []}, {"!id": 99, "!label": "COGCGVABCCSCLA", "children": [{"!id": 100, "!label": "YVIHNEJWILXUCDMFCCLI", "children": []}, {"!id": 101, "!label": "UVHRN", "children": []}]}, {"!id": 102, "!label": "RKABBSUYVBMYKLCYNOYOXPHJWX", "children": []}, {"!id": 103, "!label": "CLFFEUFCBDE", "children": []}]}, {"!id": 104, "!label": "YABEMFODWUUSFDIXMVTWOFUM", "children": [{"!id": 105, "!label": "FDYURVNWQMBIUEHRSAJNAP", "children": []}, {"!id": 106, "!label": "OLCTNRNQM", "children": []}, {"!id": 107, "!label": "TNOUBM", "children": []}, {"!id": 108, "!label": "ASCLENCPWJRFATIJSUNNVVYVGT", "children": []}, {"!id": 109, "!label": "SMGNUUOTCHUBSAVGBJQYOLMFLERX", "children": []}, {"!id": 110, "!label": "HCYTGHMISIQDFBVDFPRG", "children": []}]}]}, {"!id": 111, "!label": "LWJVCIONAVYXVIDWXDS", "children": []}, {"!id": 112, "!label": "NUGTUGJQQYQXDKMUBSUWRM", "children": []}]}]}, {"!id": 113, "!label": "MRHEMEIEQHBRFNQOUV", "children": [{"!id": 114, "!label": "QSLMOMLOCJLFKAFIPFPCYJFX", "children": [{"!id": 115, "!label": "VLWRXXGJRXGTTUBVKNGBMYYGKSV", "children": []}, {"!id": 116, "!label": "HQFRRVJFDVRFPYNPTUBMHIQ", "children": []}, {"!id": 117, "!label": "RHLNECNJYEJUITQLR", "children": [{"!id": 118, "!label": "EUNATUGKPLDGHNHUMTEMPMCSJ", "children": []}, {"!id": 119, "!label": "SKROLRDNXVN", "children": []}, {"!id": 120, "!label": "TALRDODCYPDRVQNE", "children": []}, {"!id": 121, "!label": "WYNSSETDOEJQVBYYQQLSP", "children": [{"!id": 122, "!label": "XJHPRF", "children": []}, {"!id": 123, "!label": "LTINOKVCPKVGUJIWEYPRJVDXRS", "children": [{"!id": 124, "!label": "CILRJHRVU", "children": []}, {"!id": 125, "!label": "CHQLVFTFHKXAMGY", "children": []}, {"!id": 126, "!label": "SVNHS", "children": []}, {"!id": 127, "!label": "FKYMGDSL", "children": []}, {"!id": 128, "!label": "HSBOOIEYRWETWDSRGPHH", "children": []}, {"!id": 129, "!label": "WNSHLXBJBVPQUCSVLQLYPQPSN", "children": []}]}, {"!id": 130, "!label": "BVGPWQUDIEFTHKXWIYSJGUUHNS", "children": []}, {"!id": 131, "!label": "OAGSPVIRWWKLEWJEOUGASE", "children": []}, {"!id": 132, "!label": "SGLQVKUDDNKV", "children": []}]}, {"!id": 133, "!label": "OQSAJMRDMTASPPPOCKGSLGUBVCGV", "children": []}, {"!id": 134, "!label": "DLYHKPQOSRPTH", "children": []}]}]}]}, {"!id": 135, "!label": "IYFQO", "children": []}, {"!id": 136, "!label": "QCSSMDPEOXLKULCGIFDY", "children": [{"!id": 137, "!label": "GCGCHRPRDND", "children": [{"!id": 138, "!label": "ASVIBYEOSNUKTMENNFKGLVKAMK", "children": []}, {"!id": 139, "!label": "WWRXKOMEDCDAQMMAXSQG", "children": []}, {"!id": 140, "!label": "BWVYOJ", "children": []}, {"!id": 141, "!label": "ORYXTPVLFMKQXH", "children": []}, {"!id": 142, "!label": "SQSWPTPFUPCWDSRWDCEEQJ", "children": []}, {"!id": 143, "!label": "BTCOVSPHQHXQLHLQFNSDLJWCMU", "children": []}]}, {"!id": 144, "!label": "TNNLJ", "children": [{"!id": 145, "!label": "CUHFNOXLSBSUUNLUITVGSXDUUGV", "children": []}, {"!id": 146, "!label": "POHKQTAPXJUHDRGQTRK", "children": [{"!id": 147, "!label": "CHXBYCOEHPSPKMTKQBGR", "children": []}]}, {"!id": 148, "!label": "OQFDCLMTTOYVQYTERTXXG", "children": []}, {"!id": 149, "!label": "AFOHOGGQWFULJDYVGKXAGVL", "children": []}]}]}]}]}]}]}], "styles": [], "edges": [], "links": [], "label_keys": [], "payload_objects": []}`
const _node_data = `{"nodes": [{"!id": 0, "!label": "HKEQOD", "children": [{"!id": 1, "!label": "WHUTN", "children": [{"!id": 2, "!label": "LWXYDNN", "children": [{"!id": 3, "!label": "AQQQKBE", "children": []}, {"!id": 4, "!label": "LPOCLW", "children": [{"!id": 5, "!label": "TPSSPPQ", "children": []}, {"!id": 6, "!label": "OHUOH", "children": []}, {"!id": 7, "!label": "GXXTOHV", "children": []}, {"!id": 8, "!label": "SEBGC", "children": [{"!id": 9, "!label": "DWUHB", "children": [{"!id": 10, "!label": "HGKOLC", "children": []}, {"!id": 11, "!label": "UBYNK", "children": [{"!id": 12, "!label": "OYILUSE", "children": []}, {"!id": 13, "!label": "RHNDRV", "children": []}, {"!id": 14, "!label": "TIFDYHV", "children": []}, {"!id": 15, "!label": "EFGYNN", "children": []}]}, {"!id": 16, "!label": "NQPWNVY", "children": []}]}, {"!id": 17, "!label": "KYBICBQ", "children": []}, {"!id": 18, "!label": "GMTRJ", "children": [{"!id": 19, "!label": "TSUTU", "children": [{"!id": 20, "!label": "SXTDBDG", "children": []}]}, {"!id": 21, "!label": "MDLHT", "children": []}]}, {"!id": 22, "!label": "TDWHX", "children": [{"!id": 23, "!label": "KLLLCQ", "children": [{"!id": 24, "!label": "GLDDEQM", "children": []}, {"!id": 25, "!label": "LGMQD", "children": []}, {"!id": 26, "!label": "DCTNIOW", "children": []}, {"!id": 27, "!label": "CKVEP", "children": []}]}]}]}]}, {"!id": 28, "!label": "QQNFJ", "children": [{"!id": 29, "!label": "IOBRA", "children": []}, {"!id": 30, "!label": "KHWNOQ", "children": []}, {"!id": 31, "!label": "NIWUIOL", "children": [{"!id": 32, "!label": "HFKIJWO", "children": [{"!id": 33, "!label": "WWTGJP", "children": [{"!id": 34, "!label": "VPVFR", "children": []}, {"!id": 35, "!label": "FYWTG", "children": [{"!id": 36, "!label": "LIXABWO", "children": []}, {"!id": 37, "!label": "UXVSKU", "children": []}]}, {"!id": 38, "!label": "IGMQOU", "children": []}, {"!id": 39, "!label": "AYVYJFD", "children": []}]}, {"!id": 40, "!label": "FSLUSI", "children": [{"!id": 41, "!label": "CTIPU", "children": []}, {"!id": 42, "!label": "IFBPOK", "children": []}, {"!id": 43, "!label": "GXHED", "children": []}]}]}, {"!id": 44, "!label": "ROVXSIX", "children": []}]}, {"!id": 45, "!label": "JFYHTY", "children": [{"!id": 46, "!label": "FNXPF", "children": []}, {"!id": 47, "!label": "BJHIW", "children": [{"!id": 48, "!label": "KLSPM", "children": [{"!id": 49, "!label": "YCWAQUO", "children": []}, {"!id": 50, "!label": "BGMKQ", "children": []}, {"!id": 51, "!label": "DTUKC", "children": []}]}, {"!id": 52, "!label": "DCVVAT", "children": [{"!id": 53, "!label": "QNPRXPM", "children": []}]}]}, {"!id": 54, "!label": "MQCJWL", "children": []}, {"!id": 55, "!label": "DDAODHU", "children": [{"!id": 56, "!label": "HISUVA", "children": []}, {"!id": 57, "!label": "RJPSDL", "children": []}, {"!id": 58, "!label": "WNEER", "children": [{"!id": 59, "!label": "TGUKSLX", "children": []}, {"!id": 60, "!label": "RQIRAQ", "children": []}, {"!id": 61, "!label": "EUUMRN", "children": []}]}]}]}]}, {"!id": 62, "!label": "KEHDG", "children": [{"!id": 63, "!label": "VIEXV", "children": [{"!id": 64, "!label": "YAKNDF", "children": [{"!id": 65, "!label": "YFHFOX", "children": [{"!id": 66, "!label": "VUXYYK", "children": []}, {"!id": 67, "!label": "LHPWHF", "children": []}, {"!id": 68, "!label": "UADSABQ", "children": []}]}, {"!id": 69, "!label": "AMKMJU", "children": [{"!id": 70, "!label": "MGRLUL", "children": [{"!id": 71, "!label": "YXMBS", "children": []}, {"!id": 72, "!label": "MNDRJ", "children": []}, {"!id": 73, "!label": "KARYO", "children": []}]}, {"!id": 74, "!label": "IUISK", "children": []}]}]}]}]}]}, {"!id": 75, "!label": "AITRES", "children": []}]}, {"!id": 76, "!label": "KRVHCNN", "children": []}, {"!id": 77, "!label": "CGKDU", "children": []}, {"!id": 78, "!label": "GVIVKOB", "children": [{"!id": 79, "!label": "WBVHPP", "children": [{"!id": 80, "!label": "QXQRYH", "children": []}]}, {"!id": 81, "!label": "ULRATN", "children": [{"!id": 82, "!label": "LOFIYY", "children": [{"!id": 83, "!label": "TEXDP", "children": [{"!id": 84, "!label": "MIAMSK", "children": [{"!id": 85, "!label": "JTSPC", "children": []}, {"!id": 86, "!label": "HXDGOG", "children": [{"!id": 87, "!label": "APFOIV", "children": []}, {"!id": 88, "!label": "HUYWBIR", "children": []}, {"!id": 89, "!label": "ENURA", "children": []}]}]}, {"!id": 90, "!label": "GCVALAD", "children": [{"!id": 91, "!label": "RCBUTSF", "children": []}, {"!id": 92, "!label": "QWGYC", "children": []}]}, {"!id": 93, "!label": "PWUUOY", "children": []}, {"!id": 94, "!label": "PCFVLWB", "children": [{"!id": 95, "!label": "CNEWTY", "children": []}, {"!id": 96, "!label": "QRWCTTS", "children": []}]}]}, {"!id": 97, "!label": "VXNLVXX", "children": [{"!id": 98, "!label": "KTEGEWP", "children": []}, {"!id": 99, "!label": "UAKVX", "children": []}, {"!id": 100, "!label": "LXFIFLU", "children": []}, {"!id": 101, "!label": "JQXSSWW", "children": [{"!id": 102, "!label": "UDVHFWL", "children": [{"!id": 103, "!label": "XCIIE", "children": [{"!id": 104, "!label": "EITPGBF", "children": []}]}]}, {"!id": 105, "!label": "JVKVYQC", "children": [{"!id": 106, "!label": "JBEVUE", "children": [{"!id": 107, "!label": "PXRLPXA", "children": []}, {"!id": 108, "!label": "RHDBAD", "children": []}]}]}]}]}, {"!id": 109, "!label": "ROGOVC", "children": [{"!id": 110, "!label": "OASTQ", "children": [{"!id": 111, "!label": "KNYXAT", "children": []}, {"!id": 112, "!label": "SRLBSF", "children": []}, {"!id": 113, "!label": "MYLYSN", "children": []}, {"!id": 114, "!label": "VUWBH", "children": [{"!id": 115, "!label": "PUSCG", "children": [{"!id": 116, "!label": "AXALX", "children": []}, {"!id": 117, "!label": "NBQFNDG", "children": []}]}]}]}, {"!id": 118, "!label": "GDRNYW", "children": []}, {"!id": 119, "!label": "XDLWVQ", "children": [{"!id": 120, "!label": "EWWQNO", "children": []}]}, {"!id": 121, "!label": "UQGNRA", "children": [{"!id": 122, "!label": "HJOLR", "children": [{"!id": 123, "!label": "DVAXQEX", "children": []}, {"!id": 124, "!label": "VPVWWX", "children": []}, {"!id": 125, "!label": "CPTFYSC", "children": []}]}, {"!id": 126, "!label": "VLSFJN", "children": [{"!id": 127, "!label": "WPEOH", "children": [{"!id": 128, "!label": "JBKPO", "children": []}]}, {"!id": 129, "!label": "FDJLOLA", "children": []}]}, {"!id": 130, "!label": "SXNJXC", "children": [{"!id": 131, "!label": "YMWEKDA", "children": []}]}, {"!id": 132, "!label": "HQEVF", "children": [{"!id": 133, "!label": "LIMFFM", "children": []}, {"!id": 134, "!label": "MFPLQBJ", "children": []}, {"!id": 135, "!label": "YAEQP", "children": [{"!id": 136, "!label": "WNGXN", "children": []}, {"!id": 137, "!label": "BMEOFRL", "children": []}, {"!id": 138, "!label": "IXKWR", "children": []}]}]}]}]}]}, {"!id": 139, "!label": "AMCBTVV", "children": [{"!id": 140, "!label": "RRWOI", "children": [{"!id": 141, "!label": "YDCBXC", "children": [{"!id": 142, "!label": "MRBUR", "children": []}, {"!id": 143, "!label": "KGFIGJH", "children": []}, {"!id": 144, "!label": "BMUHX", "children": []}]}]}]}, {"!id": 145, "!label": "SQAMNH", "children": [{"!id": 146, "!label": "SBQFMV", "children": [{"!id": 147, "!label": "KSAKNAW", "children": [{"!id": 148, "!label": "VPEFWCC", "children": []}, {"!id": 149, "!label": "GXUSGB", "children": [{"!id": 150, "!label": "NXLBG", "children": [{"!id": 151, "!label": "UEABSIL", "children": [{"!id": 152, "!label": "OOUVLEU", "children": []}]}, {"!id": 153, "!label": "JKCSJY", "children": []}, {"!id": 154, "!label": "BXKUVBR", "children": []}]}, {"!id": 155, "!label": "SIVJEW", "children": [{"!id": 156, "!label": "HVMFE", "children": []}, {"!id": 157, "!label": "AXGJR", "children": []}, {"!id": 158, "!label": "QYARSF", "children": [{"!id": 159, "!label": "IOGHS", "children": []}]}, {"!id": 160, "!label": "UGGSH", "children": []}]}, {"!id": 161, "!label": "UPDYSCF", "children": [{"!id": 162, "!label": "HRNCDE", "children": []}]}]}, {"!id": 163, "!label": "EPMUGD", "children": [{"!id": 164, "!label": "NQYNB", "children": []}, {"!id": 165, "!label": "KXXUQPU", "children": []}, {"!id": 166, "!label": "KIOPYRE", "children": []}, {"!id": 167, "!label": "PAFOBD", "children": []}]}]}, {"!id": 168, "!label": "NHLMX", "children": [{"!id": 169, "!label": "GYBYTK", "children": []}, {"!id": 170, "!label": "MLYGPAU", "children": [{"!id": 171, "!label": "XNJFJQO", "children": [{"!id": 172, "!label": "GYTRXX", "children": [{"!id": 173, "!label": "TLBCAF", "children": []}]}, {"!id": 174, "!label": "OOKVHDB", "children": [{"!id": 175, "!label": "IUROT", "children": []}, {"!id": 176, "!label": "JDKIL", "children": []}, {"!id": 177, "!label": "OAERT", "children": []}]}]}, {"!id": 178, "!label": "JXPMXXW", "children": []}, {"!id": 179, "!label": "MIVSG", "children": []}]}, {"!id": 180, "!label": "YWWDF", "children": []}]}, {"!id": 181, "!label": "AOEUMYX", "children": []}, {"!id": 182, "!label": "DWKASC", "children": []}]}, {"!id": 183, "!label": "KILFOM", "children": []}, {"!id": 184, "!label": "MHBRRVQ", "children": [{"!id": 185, "!label": "XDDHSBQ", "children": []}, {"!id": 186, "!label": "LWNOW", "children": []}, {"!id": 187, "!label": "LUGQFJ", "children": []}]}, {"!id": 188, "!label": "VSPGSK", "children": [{"!id": 189, "!label": "TBCBR", "children": []}]}]}]}, {"!id": 190, "!label": "WRYEKOU", "children": [{"!id": 191, "!label": "JMXNU", "children": [{"!id": 192, "!label": "YEEHW", "children": [{"!id": 193, "!label": "QQNDHIB", "children": [{"!id": 194, "!label": "KNSBCI", "children": []}, {"!id": 195, "!label": "WKMDGJ", "children": [{"!id": 196, "!label": "HJCOG", "children": []}, {"!id": 197, "!label": "YCOCEA", "children": []}, {"!id": 198, "!label": "JUTAOHV", "children": []}]}, {"!id": 199, "!label": "COVPE", "children": [{"!id": 200, "!label": "QOCMOGU", "children": []}, {"!id": 201, "!label": "NTEKUOT", "children": []}, {"!id": 202, "!label": "EOTMS", "children": [{"!id": 203, "!label": "DMVMY", "children": [{"!id": 204, "!label": "QELTYJU", "children": []}, {"!id": 205, "!label": "XKEBAK", "children": []}]}, {"!id": 206, "!label": "JCQNGBO", "children": [{"!id": 207, "!label": "YWHUQ", "children": []}]}, {"!id": 208, "!label": "FCHDRWR", "children": []}]}]}]}]}, {"!id": 209, "!label": "APNIBNS", "children": [{"!id": 210, "!label": "MMXIBE", "children": [{"!id": 211, "!label": "VBWATC", "children": []}, {"!id": 212, "!label": "RPGFCE", "children": [{"!id": 213, "!label": "EONQQ", "children": []}, {"!id": 214, "!label": "YRKIDE", "children": []}, {"!id": 215, "!label": "XCYCAQD", "children": []}]}, {"!id": 216, "!label": "FLLRJG", "children": [{"!id": 217, "!label": "JHGDMW", "children": []}, {"!id": 218, "!label": "QXBARW", "children": []}]}, {"!id": 219, "!label": "WVRQLR", "children": []}]}]}]}]}]}]}], "styles": [], "edges": [], "links": [], "label_keys": [], "payload_objects": []}`