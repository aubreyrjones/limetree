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


const RANK_SEPARATION = 80.0;
const BOX_W_MARGIN = 4;
const W_SEPARATION = 20;
const BOX_TOP_OFFSET = 26;
const BOX_HEIGHT = BOX_TOP_OFFSET + 10;

var _next_node_id = 999;
var _all_nodes = {};
var _root_node = null;
var _rank_lists = new Array();

var rank_list = function (rank) {
    let slen = _rank_lists.length;
    for (let i = 0; i <= (rank - slen); i++) {
        _rank_lists.push(new Array());
    }
    return _rank_lists[rank];
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

var g_pan_x = -500;
var g_pan_y = -50;
var g_scale = 1.0;

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
        this.rank = 0;
        this.payload = {};
        this.children = new Array();
        this.pos_x = 0;
        this.pos_y = RANK_SEPARATION * this.rank;
        this.boxwidth = 100;
        this.style = "default";
        

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
        this.x = 0; //layout position, copied over to pos_x when ready.
        this.sib_index = -1;
        this.left_countour = 10000000000;
        this.right_countour = -10000000000;
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

    rank_self(my_rank) {
        for (let edge of this.children) {
            edge.target.rank_self(my_rank + 1);
        }

        this.rank = my_rank;
        this.pos_y = this.rank * RANK_SEPARATION;
        let rl = rank_list(my_rank);
        rl.push(this);
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
        return this.x;
    }

    layout_right_side() {
        return this.layout_left_side() + this.boxwidth;
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

    left_sib() {
        if ((!this.parent) || (this.sib_index == 0)) return null;
        return this.parent.child(this.sib_index - 1);
    }


    leftmost_sib() {
        if ((!this.parent) || (this.sib_index == 0)) return null;
        return this.parent.child(0);
    }


    draw(ctx) {
        ctx.font = this.font
        let label = this.label || this.id;

        let style = _styles[this.style];

        ctx.strokeStyle = 'black';
        for (let ck in this.children) {
            let c = this.children[ck].target;
            ctx.beginPath();
            ctx.moveTo(this.center(), this.pos_y);
            ctx.lineTo(c.center(), c.pos_y);
            ctx.stroke();
        }

        ctx.strokeStyle = style.outline;
        ctx.fillStyle = style.fillStyle;
        ctx.fillRect(this.pos_x, this.top(), this.boxwidth, BOX_HEIGHT);
        ctx.strokeRect(this.pos_x, this.top(), this.boxwidth, BOX_HEIGHT);
        ctx.fillStyle = 'black';
        ctx.fillText(label, this.pos_x + BOX_W_MARGIN, this.pos_y);
    }
}

var first_walk = function(v, distance) {
    if (v.leaf()) {
        if (v.left_sib()) {
            v.x = v.left_sib().layout_right_side() + distance;
        }
        else {
            v.x = 0.0;
        }

        return v;
    }

    // inner node
    let cCount = v.count();
    for (let i = 0; i < cCount; i++) {
        let c = v.child(i);
        first_walk(c, distance);
        if (i > 0) {
            let overlap = find_overlap(v.child(i - 1), c);
            console.log(c.label, v.child(i - 1).label, overlap);
            if (overlap > 0) {
                move_tree(c, overlap + distance);
            }
        }
    }

    // stack leaves

    let midpoint = (v.child(0).layout_left_side() + v.child(-1).layout_right_side()) / 2.0;
    v.x = midpoint - v.halfw();
    
    return v;
}

var find_overlap = function(l, r) {
    let max_overlap = l.layout_right_side() - r.layout_left_side();
    if (l.count() && r.count()) {
        let c_overlap = find_overlap(l.child(-1), r.child(0));
        if (c_overlap > max_overlap) return c_overlap;
    }

    return max_overlap;
}

var move_tree = function(v, amount) {
    v.x += amount;
    for (let edge of v.children) {
        move_tree(edge.target, amount);
    }
}

var find_left_countour = function(v) {
    let l = v.layout_left_side();
    let cl = l;

    for (let edge of v.children) {
        let _cl = find_left_countour(edge.target);
        if (_cl < cl) cl = _cl;
    }

    if (cl < l) return cl;
    return l;
}

var find_right_contour = function(v) {
    let r = v.layout_right_side();
    let cr = r;

    for (let edge of v.children) {
        let _cr = find_right_countour(edge.target);
        if (_cl < cl) cl = _cl;
    }

    if (cr > r) return cr;
    return r;
}


var layout_tree = function(root) {
    first_walk(root, W_SEPARATION);
    //second_walk(root);

    iter_all(n => n.pos_x = n.x);
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
    let oldMouse = xform_point(_cur_x, _cur_y);
    g_scale += -e.deltaY * 0.01;
    if (g_scale < 0.05) g_scale = 0.05;
    if (g_scale > 2.0) g_scale = 2.0;

    let afterMouse = xform_point(_cur_x, _cur_y);
    g_pan_x += oldMouse.x - afterMouse.x;
    g_pan_y += oldMouse.y - afterMouse.y ;

    draw_all_configured();
}

var _displayed_node = null;

var layout_obj = function(parent_div, name, o) {
    let tbl = document.createElement("table");
    parent_div.appendChild(tbl);
    
    let title = tbl.insertRow();
    let titleCell = title.insertCell();
    titleCell.innerHTML = name;
    titleCell.style = 'text-align:center';
    titleCell.setAttribute("colspan", "2");

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
    layout_obj(info_div, n.label || n.id, n.payload);
}

// Startup


var load_nodes = function() {
    let data = JSON.parse(_node_data);

    for (let sk in data["styles"]) {
        _styles[sk] = data["styles"][sk];
    }
    
    _node_label_keys = data["label_keys"];
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
    _root_node.rank_self(0);
    
    draw_all_configured();
}


const _node_data = `{"nodes": [{"production": "global_list", "type": null, "value": null, "id": 0, "line": -1, "attr": {}, "c": [{"production": "pipeline", "type": null, "value": null, "id": 1, "line": 1, "attr": {}, "c": [{"production": null, "type": "IDENT", "value": "_1997", "id": 2, "line": 1, "attr": {}, "c": []}, {"production": "component_contents", "type": null, "value": null, "id": 3, "line": -1, "attr": {}, "c": [{"production": "Gets", "type": null, "value": null, "id": 4, "line": 2, "attr": {}, "c": [{"production": "vardecl", "type": null, "value": null, "id": 5, "line": 2, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "gl_Position:", "id": 6, "line": 2, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 7, "line": -1, "attr": {}, "c": []}, {"production": "index", "type": null, "value": null, "id": 8, "line": -1, "attr": {}, "c": []}]}, {"production": "MMult", "type": null, "value": null, "id": 9, "line": 3, "attr": {}, "c": [{"production": "MMult", "type": null, "value": null, "id": 10, "line": 3, "attr": {}, "c": [{"production": "MMult", "type": null, "value": null, "id": 11, "line": 3, "attr": {}, "c": [{"production": "staged_vardecl", "type": null, "value": null, "id": 12, "line": 3, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "u[", "id": 13, "line": 3, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 14, "line": 3, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "projMatrix:", "id": 15, "line": 3, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 16, "line": -1, "attr": {}, "c": [{"production": "typeref", "type": null, "value": null, "id": 17, "line": 3, "attr": {}, "c": [{"production": null, "type": "IDENT", "value": "mat4", "id": 18, "line": 3, "attr": {}, "c": []}]}]}, {"production": "index", "type": null, "value": null, "id": 19, "line": -1, "attr": {}, "c": []}]}]}, {"production": "staged_vardecl", "type": null, "value": null, "id": 20, "line": 4, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "u[", "id": 21, "line": 4, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 22, "line": 4, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "viewMatrix:", "id": 23, "line": 4, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 24, "line": -1, "attr": {}, "c": [{"production": "typeref", "type": null, "value": null, "id": 25, "line": 4, "attr": {}, "c": [{"production": null, "type": "IDENT", "value": "mat4", "id": 26, "line": 4, "attr": {}, "c": []}]}]}, {"production": "index", "type": null, "value": null, "id": 27, "line": -1, "attr": {}, "c": []}]}]}]}, {"production": "staged_vardecl", "type": null, "value": null, "id": 28, "line": 5, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "u[", "id": 29, "line": 5, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 30, "line": 5, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "modelMatrix:", "id": 31, "line": 5, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 32, "line": -1, "attr": {}, "c": [{"production": "typeref", "type": null, "value": null, "id": 33, "line": 5, "attr": {}, "c": [{"production": null, "type": "IDENT", "value": "mat4", "id": 34, "line": 5, "attr": {}, "c": []}]}]}, {"production": "index", "type": null, "value": null, "id": 35, "line": -1, "attr": {}, "c": []}]}]}]}, {"production": "staged_vardecl", "type": null, "value": null, "id": 36, "line": 6, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "a[", "id": 37, "line": 6, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 38, "line": 6, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "position:", "id": 39, "line": 6, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 40, "line": -1, "attr": {}, "c": [{"production": "typeref", "type": null, "value": null, "id": 41, "line": 6, "attr": {}, "c": [{"production": null, "type": "IDENT", "value": "vec4", "id": 42, "line": 6, "attr": {}, "c": []}]}]}, {"production": "index", "type": null, "value": null, "id": 43, "line": -1, "attr": {}, "c": [{"production": null, "type": "INTEGER", "value": "0", "id": 44, "line": 6, "attr": {}, "c": []}]}]}]}]}]}, {"production": "Gets", "type": null, "value": null, "id": 45, "line": 8, "attr": {}, "c": [{"production": "staged_vardecl", "type": null, "value": null, "id": 46, "line": 8, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "f[", "id": 47, "line": 8, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 48, "line": 8, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "f_color:", "id": 49, "line": 8, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 50, "line": -1, "attr": {}, "c": []}, {"production": "index", "type": null, "value": null, "id": 51, "line": -1, "attr": {}, "c": [{"production": null, "type": "INTEGER", "value": "0", "id": 52, "line": 8, "attr": {}, "c": []}]}]}]}, {"production": "Gets", "type": null, "value": null, "id": 53, "line": 9, "attr": {}, "c": [{"production": "staged_vardecl", "type": null, "value": null, "id": 54, "line": 9, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "v[", "id": 55, "line": 9, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 56, "line": 9, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "v_color:", "id": 57, "line": 9, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 58, "line": -1, "attr": {}, "c": []}, {"production": "index", "type": null, "value": null, "id": 59, "line": -1, "attr": {}, "c": []}]}]}, {"production": "staged_vardecl", "type": null, "value": null, "id": 60, "line": 10, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "a[", "id": 61, "line": 10, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 62, "line": 10, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "a_color:", "id": 63, "line": 10, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 64, "line": -1, "attr": {}, "c": [{"production": "typeref", "type": null, "value": null, "id": 65, "line": 10, "attr": {}, "c": [{"production": null, "type": "IDENT", "value": "vec4", "id": 66, "line": 10, "attr": {}, "c": []}]}]}, {"production": "index", "type": null, "value": null, "id": 67, "line": -1, "attr": {}, "c": [{"production": null, "type": "INTEGER", "value": "1", "id": 68, "line": 10, "attr": {}, "c": []}]}]}]}]}]}, {"production": "Gets", "type": null, "value": null, "id": 69, "line": 14, "attr": {}, "c": [{"production": "vardecl", "type": null, "value": null, "id": 70, "line": 14, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "pi:", "id": 71, "line": 14, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 72, "line": -1, "attr": {}, "c": []}, {"production": "index", "type": null, "value": null, "id": 73, "line": -1, "attr": {}, "c": []}]}, {"production": null, "type": "FLOAT", "value": "3.14", "id": 74, "line": 14, "attr": {}, "c": []}]}]}]}]}], "styles": [], "edges": [], "links": [], "label_keys": ["production", "type"], "payload_objects": ["attr"]}`