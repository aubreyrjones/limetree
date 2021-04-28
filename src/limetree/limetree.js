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

var _next_node_id = 999;
var _all_nodes = {};
var _root_node = null;

let _styles = {};
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
    constructor(o, rank) {
        // Payload, general tree pointers, and style information.
        this.parent = null;
        this.rank = rank;
        this.payload = {};
        this.children = new Array();
        this.pos_x = 0;
        this.pos_y = RANK_SEPARATION * this.rank;
        this.boxwidth = 100;
        

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
                                this.add_child(child_key, new LiveNode(sub_o, rank + 1));
                            }
                        }
                    }
                    else {
                        this.add_child(my_key, new LiveNode(o[k], rank + 1));
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
        this.thread = null;
        this.mod = 0.0;
        this.ancestor = this;
        this.change = 0.0;
        this.shift = 0.0;
        this.sib_index = -1;
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

    center() {
        return this.right_side() - (this.boxwidth / 2);
    }

    left_side() {
        return this.pos_x;
    }

    right_side() {
        return this.pos_x + this.boxwidth;
    }

    layout_left_side() {
        return this.x;
    }

    layout_right_side() {
        return this.x + this.boxwidth;
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

    left() {
        if (this.thread) return this.thread;
        if (this.count()) return this.child(0);
        return null;
    }

    right() {
        if (this.thread) return this.thread;
        if (this.count()) return this.child(-1);
        return null;
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

        ctx.strokeStyle = 'black';
        for (let ck in this.children) {
            let c = this.children[ck].target;
            ctx.beginPath();
            ctx.moveTo(this.center(), this.pos_y);
            ctx.lineTo(c.center(), c.pos_y);
            ctx.stroke();
        }

        
        ctx.fillStyle = 'rgb(200, 200, 200)';
        ctx.fillRect(this.pos_x, this.pos_y - 25, this.boxwidth, 24 + 12);
        ctx.fillStyle = 'black';
        ctx.fillText(label, this.pos_x + BOX_W_MARGIN, this.pos_y);
    }
}

var first_walk = function(v, distance) {
    if (v.leaf()) {
        if (v.leftmost_sib()) {
            v.x = v.left_sib().layout_right_side() + distance;
        }
        else {
            v.x = 0.0;
        }

        return v;
    }

    // inner node
    let default_ancestor = v.child(0);
    for (let edge of v.children) {
        let c = edge.target;
        first_walk(c, distance);
        default_ancestor = apportion(c, default_ancestor, distance);
    }
    execute_shifts(v);

    let midpoint = (v.child(0).layout_left_side() + v.child(-1).layout_right_side()) / 2.0;
    let ell = v.child(0);
    let arr = v.child(-1);
    let w = v.left_sib();
    if (w) {
        v.x = w.layout_right_side() + distance;
        v.mod = v.x - midpoint;
    }
    else {
        v.x = midpoint;
    }

    return v;
}

var apportion = function(v, default_ancestor, distance) {
    let w = v.left_sib();
    if (w) {
        let vir = v;
        let vor = v;

        let vil = w;
        let vol = v.leftmost_sib();
        let sir = v.mod;
        let sor = v.mod;
        let sil = vil.mod;
        let sol = vol.mod;

        while (vil.right() && vir.left()) {
            vil = vil.right();
            vir = vir.left();
            vol = vol.left();
            vor = vor.right();
            vor.ancestor = v;
            let shift = (vil.layout_right_side() + sil) - (vir.layout_left_side() + sir) + distance;
            if (shift > 0) {
                move_subtree(ancestor(vil, v, default_ancestor), v, shift);
                sir = sir + shift;
                sor = sor + shift;
            }
            sil += vil.mod;
            sir += vir.mod;
            sol += vol.mod;
            sor += vor.mod;
        }

        if (vil.right() && !vor.right()) {
            vor.thread = vil.right();
            vor.mod += sil - sor;
        }
        else {
            if (vir.left() && !vol.left()) {
                vol.thread = vir.left();
                vol.mod += sir - sol;
            }
            default_ancestor = v;
        }
    }
    return default_ancestor;
}

var move_subtree = function(wl, wr, shift) {
    let subtrees = wr.sib_index - wl.sib_index;
    wr.change -= shift / subtrees;
    wr.shift += shift;
    wl.change += shift / subtrees;
    wr.x += shift;
    wr.mod += shift;
}

var execute_shifts = function(v) {
    let shift = 0;
    let change = 0;
    for (let i = v.children.length - 1; i != 0 ; --i) {
        let w = v.child(i);
        w.x += shift;
        w.mod += shift;
        change += change;
        shift += w.shift + change;
    }
}

var ancestor = function(vil, v, default_ancestor) {
    if (v.parent.has_child(vil.ancestor)) {
        return vil.ancestor;
    }
    else {
        return default_ancestor;
    }
}

var second_walk = function(v, m = 0, min) {
    v.x += m;
    if (min === undefined || v.x < min) {
        min = v.x;
    }

    for (let edge of v.children) {
        min = second_walk(edge.target, m + v.mod, min);
    }
}

var layout_tree = function(root) {
    first_walk(root, 10);
    second_walk(root);

    iter_all(n => n.pos_x = n.x);
}




var load_nodes = function() {
    let data = JSON.parse(_node_data);

    _styles = data["styles"];
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
        ctx.translate(-g_pan_x, -g_pan_y);
        iter_all(n => n.draw(ctx));
        ctx.restore();
    }
}

var mainloop = function(canvas) {
    draw_all(canvas);
}

var start_limetree = function() {
    load_nodes();

    let canvas = document.getElementById('tree_canvas');
    canvas.width  = window.innerWidth * 0.99;
    canvas.height = window.innerHeight * 0.98;

    let ctx = canvas.getContext('2d');

    iter_all(n => n.measure_self(ctx));
    layout_tree(_root_node);
    
    draw_all(canvas);
}


const _node_data = `{"nodes": [{"production": "global_list", "type": null, "value": null, "id": 0, "line": -1, "attr": {}, "c": [{"production": "pipeline", "type": null, "value": null, "id": 1, "line": 1, "attr": {}, "c": [{"production": null, "type": "IDENT", "value": "_1997", "id": 2, "line": 1, "attr": {}, "c": []}, {"production": "component_contents", "type": null, "value": null, "id": 3, "line": -1, "attr": {}, "c": [{"production": "Gets", "type": null, "value": null, "id": 4, "line": 2, "attr": {}, "c": [{"production": "staged_vardecl", "type": null, "value": null, "id": 5, "line": 2, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "f[", "id": 6, "line": 2, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 7, "line": 2, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "f_color:", "id": 8, "line": 2, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 9, "line": -1, "attr": {}, "c": []}, {"production": "index", "type": null, "value": null, "id": 10, "line": -1, "attr": {}, "c": [{"production": null, "type": "INTEGER", "value": "0", "id": 11, "line": 2, "attr": {}, "c": []}]}]}]}, {"production": "Gets", "type": null, "value": null, "id": 12, "line": 3, "attr": {}, "c": [{"production": "staged_vardecl", "type": null, "value": null, "id": 13, "line": 3, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "v[", "id": 14, "line": 3, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 15, "line": 3, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "v_color:", "id": 16, "line": 3, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 17, "line": -1, "attr": {}, "c": []}, {"production": "index", "type": null, "value": null, "id": 18, "line": -1, "attr": {}, "c": []}]}]}, {"production": "staged_vardecl", "type": null, "value": null, "id": 19, "line": 4, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "a[", "id": 20, "line": 4, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 21, "line": 4, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "a_color:", "id": 22, "line": 4, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 23, "line": -1, "attr": {}, "c": [{"production": "typeref", "type": null, "value": null, "id": 24, "line": 4, "attr": {}, "c": [{"production": null, "type": "IDENT", "value": "vec4", "id": 25, "line": 4, "attr": {}, "c": []}]}]}, {"production": "index", "type": null, "value": null, "id": 26, "line": -1, "attr": {}, "c": [{"production": null, "type": "INTEGER", "value": "1", "id": 27, "line": 4, "attr": {}, "c": []}]}]}]}]}]}, {"production": "Gets", "type": null, "value": null, "id": 28, "line": 8, "attr": {}, "c": [{"production": "vardecl", "type": null, "value": null, "id": 29, "line": 8, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "pi:", "id": 30, "line": 8, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 31, "line": -1, "attr": {}, "c": []}, {"production": "index", "type": null, "value": null, "id": 32, "line": -1, "attr": {}, "c": []}]}, {"production": null, "type": "FLOAT", "value": "3.14", "id": 33, "line": 8, "attr": {}, "c": []}]}]}]}]}], "styles": [], "links": [], "label_keys": ["production", "type"], "payload_objects": ["attr"]}`