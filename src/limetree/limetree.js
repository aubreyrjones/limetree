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



var DEFERRED_MOVE_MODE = true;

var PROFILE_COLLISION_MODE = true && DEFERRED_MOVE_MODE;

var MOVE_INNER_MODE = true;


function sleep(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
}

function debug_step() {
    draw_all_configured();
    return sleep(200);
}

var finishedLayout = false;

const exrp = p => (1.5**p) * (0.15 ** (1 - p));

const RANK_SEPARATION = 60.0;
const BOX_W_MARGIN = 4;

const W_SEPARATION = 5;
const SUBTREE_W_SEPARATION = 10;
const SUBTREE_W_GEOMETRIC_FACTOR = 1;

const BOX_TOP_OFFSET = 26;
const BOX_HEIGHT = BOX_TOP_OFFSET + 10;

var LAYOUT_RECURSION_COUNTER = 0;
var DELTA_SUM_COUNTER = 0;
var LEFT_SIDE_COUNTER = 0;
var RIGHT_SIDE_COUNTER = 0;
var MOVE_COUNTER = 0;
var PROFILE_UPDATES = 0;
var PROFILE_BUILDING = 0;
var PROFILE_QUERIES = 0;
var PROFILE_QUERIES_SUB = 0;

var _next_node_id = 999;
var _all_nodes = {};
var _root_node = null;
var _rank_lists = new Array();
var _rank_wave = new Array();

// holds which profile owns each rank at each time.
var _rank_profile_table = new Array();

function rank_profile_row(rank) {
    let slen = _rank_profile_table.length;
    for (let i = 0; i <= (rank - slen); i++) {
        _rank_profile_table.push(new Array());
    }
    return _rank_profile_table[rank];
}

function rank_profile_left(v) {
    if (v.rankorder <= 0) return null;
    return rank_profile_row(v.rank)[v.rankorder - 1];
}

function rank_profile_right(v) {
    let row = rank_profile_row(v.rank);
    if (v.rankorder + 1 >= row.length) return null;
    return row[v.rankorder + 1];
}




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

var g_pan_x = -1800;
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
        this.tag_profile = false;
        this.left_parent_depth_at_layout = -1;
        this.left_sib_debug_depth = -1;
        

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

        this.nodeNeighborSeparation = NaN;
        this.minSeparationToLeftwardCousins = NaN;
        this.minSeparationToUnrelated = NaN;

        this.leftEdgeByRank = new Array(); // int -> RANK ORDER
        this.rightEdgeByRank = new Array(); // int -> RANK ORDER

        this.rightProfile = new Array();
        this.leftProfile = new Array();
    }

    left_edge(rank) {
        return rank_list(rank)[this.leftEdgeByRank[rank - this.rank]];
    }

    right_edge(rank) {
        return rank_list(rank)[this.rightEdgeByRank[rank - this.rank]];
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

        PROFILE_BUILDING++;

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
        rank_profile_row(this.rank).push(null); // just for book keeping for now.


        // subtree extrema
        this.leftEdgeByRank = new Array();
        this.rightEdgeByRank = new Array();
        this.leftEdgeByRank.push(this.rankorder); // our own level.
        this.rightEdgeByRank.push(this.rankorder);

        this.leftProfile.push(this.x); // ultimately meaningless, and will be reassigned, but whatever.
        this.rightProfile.push(this.x + this.boxwidth);

        if (!this.leaf()) {
            let depthCount = this.maxdepth - this.rank; // must be non-zero for non-leaf
            for (let i = 0; i < depthCount; i++) {
                let r = i + this.rank + 1;
                let edges = this.sigma(r);
                this.leftEdgeByRank.push(edges['l']);
                this.rightEdgeByRank.push(edges['r']);

                this.leftProfile.push(null);
                this.rightProfile.push(null);
            }
        }

        // visual layout
        this.pos_y = this.rank * RANK_SEPARATION;

        return this.maxdepth;
    }

    claim_own_profile() {
        rank_profile_row(this.rank)[this.rankorder] = this;
    }

    // set pointers
    dominate_rank_profile() {
        for (let edgeNode of this.subtree_left_edge()) {
            rank_profile_row(edgeNode.rank)[edgeNode.rankorder] = this;
        }

        for (let edgeNode of this.subtree_right_edge()) {
            rank_profile_row(edgeNode.rank)[edgeNode.rankorder] = this;
        }
    }

    // actual numerical profile
    right_profile_for_rank(rank) {
        if (rank < this.rank || rank > this.maxdepth) return null;
        return this.rightProfile[rank - this.rank];
    }

    right_profile_xformed(rank) {
        let natural = this.right_profile_for_rank(rank);
        if (natural == null) return null;

        let sum = 0;// this.delta_sum();

        if (this.non_tagging_delta_sum() - this.delta != 0) {
            console.log("Nonelocal delta on right query! mine, total", this.delta, this.non_tagging_delta_sum());
        }

        return natural + sum;
    }

    // actual numerical profile
    set_right_profile(rank, value) {
        this.rightProfile[rank - this.rank] = value;
    }

    // actual numerical profile
    move_right_profile(rank, delta) {
        this.rightProfile[rank - this.rank] += delta;
    }


    // actual numerical profile
    left_profile_for_rank(rank) {
        if (rank < this.rank || rank > this.maxdepth) return null;
        return this.leftProfile[rank - this.rank];
    }

    left_profile_xformed(rank) {
        let natural = this.left_profile_for_rank(rank);
        if (natural == null) return null;

        let sum = 0; //this.delta_sum();

        if (this.non_tagging_delta_sum() - this.delta != 0) {
            console.log("Nonelocal delta on left query! mine, total", this.delta, this.non_tagging_delta_sum());
        }

        return natural + sum;
    }

    // actual numerical profile
    set_left_profile(rank, value) {
        this.leftProfile[rank - this.rank] = value;
    }

    // actual numerical profile
    move_left_profile(rank, delta) {
        this.leftProfile[rank - this.rank] += delta;
    }

    // actual numerical profile
    move_whole_profile(delta) {
        for (let i = 0; i < this.rightProfile.length; i++) {
            PROFILE_UPDATES++;
            this.rightProfile[i] += delta;
        }

        for (let i = 0; i < this.leftProfile.length; i++) {
            this.leftProfile[i] += delta;
        }
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

        if ((tagged || tagged2 || tagged3 || tagged4 || tagged_common)) {
            

            // if (tagged2) {
            //     ctx.strokeStyle = "blue";
            //     ctx.strokeRect(this.pos_x - 8, this.top() - 8, this.boxwidth + 16, BOX_HEIGHT + 16);
            // }
            
        }

        if (tagged) {
            ctx.lineWidth = 4;
            ctx.strokeStyle = "red";
            ctx.strokeRect(this.pos_x - 4, this.top() - 4, this.boxwidth + 8, BOX_HEIGHT + 8);
        }

        if (tagged3) {
            ctx.lineWidth = 4;
            ctx.strokeStyle = "blue";
            ctx.strokeRect(this.pos_x - 4, this.top() - 4, this.boxwidth + 8, BOX_HEIGHT + 8);
        }
        
        if (false && tagged_common) {
            // if (this.non_tagging_delta_sum() == 0) {
            //     ctx.setLineDash([5, 5]);
            // }
            if (this.last_common <= this.lastMoveStep) {
                //ctx.setLineDash([5, 5]);
            }

            ctx.lineWidth = 4;
            ctx.strokeStyle = "orange";
            ctx.strokeRect(this.pos_x - 16, this.top() - 16, this.boxwidth + 32, BOX_HEIGHT + 32);
            ctx.setLineDash([]);
        }

        if (false && this.last_common > 0) {
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

        if (this.tag) this.tag--;
        this.tag2 = false;
        if (this.tag3) this.tag3--;
        this.tag4 = false;

        if (!finishedLayout) {
            this.highlight = false;
        }

        if (this.tag_profile) {
            draw_node_profile(ctx, this);
            this.tag_profile--;
        }
    }
}


async function n1_lda_skew_tree(node, parent_skew) {
    if (node.leaf()) {
        await debug_step(); // DEBUG
        node.x += parent_skew;
        return;
    }

    let naturalPosition = (node.child(0).x + node.child(-1).layout_natural_right()) / 2.0;
    naturalPosition -= node.halfw();

    console.log(node.label, naturalPosition, node.x);

    let skew = node.x - naturalPosition;
    node.x += parent_skew;

    await debug_step(); // DEBUG
    for (let e of Array.from(node.children).reverse()) {
        await _lda_skew_tree(e.target, parent_skew + skew);
    }
}

async function _lda_skew_tree(node, parent_skew) {
    let skew = 0;
    if (node.leaf()) {
        await debug_step(); // DEBUG
        node.x += parent_skew;
        return;
    }


    let naturalPosition = (node.child(0).x + node.child(-1).layout_natural_right()) / 2.0;
    naturalPosition -= node.halfw();

    node.x = naturalPosition;

    await debug_step(); // DEBUG
    for (let e of node.children) {
        await _lda_skew_tree(e.target, parent_skew + skew);
    }    
}

//  ***************************************************************

var move_tree_deferred = function(root, amount) {
    //root.delta += amount; // this doesn't work with the profile caching
    root.x += amount;

    for (let e of root.children) {
        e.target.delta += amount;
    }

    MOVE_COUNTER++;
    root.moveCount++;
    root.lastMoveStep = LAYOUT_RECURSION_COUNTER;
}

function make_patch(amount, stoprank) {
    return {
        'delta' : amount,
        'stop' : stoprank
    }
}

function ranksep(rank, separation) {
    return {"rank" : rank, "sep": separation};
}

async function _lda_layout(node, rank_margins, profile_patches, parent_left_depth, left_sibling_depth) {
    node.rightProfile = Array.from(rank_margins); // DEBUG
    node.left_parent_depth_at_layout = parent_left_depth;
    node.left_sib_debug_depth = left_sibling_depth;
    let marginSeparation;

    if (profile_patches[node.rank] != null) {
        let patch = profile_patches[node.rank];
        rank_margins[node.rank] += patch.delta;
        if (patch.stop != node.rank) {
            profile_patches[node.rank + 1] = patch;
        }
        profile_patches[node.rank] = null;
    }

    // these cases set up the margins, and measure separations from previous nodes and subtrees for leaves. Inner nodes will overwrite these measurements.
    // this is all mixed together basically because the margin updates and the separation measurements are easiest done right next to each other
    if (node.rank > 0 && node.sib_index == 0) { // start of a new subtree
        let nextStart = rank_margins[node.rank - 1] + node.parent.childIdeals[0]; // get the "best" place to put the next node based on its parents' left margin    

        if (rank_margins[node.rank] == null) { // virgin rank
            rank_margins[node.rank] = nextStart; // just set the ideal as the margin

            marginSeparation = 1000000; //there's no left margin, we could move leftward infinitely.
        }
        else { // there's something to the left
            let startMargin = rank_margins[node.rank];
            rank_margins[node.rank] = Math.max(rank_margins[node.rank], nextStart); // either the ideal spot, or as far leftward as allowed by current rank margin.
            marginSeparation = rank_margins[node.rank] - startMargin; // we could move leftward to butt up against our leftward neighbor.
        }
    }
    else if(node.rank > 0 && node.sib_index > 0) {
        // if we're a sibling and a leaf, we're going to be laid out absolutely and correctly the first time
        // we cannot move leftward toward our immediate sibling
        // if we're not a leaf, we'll deal with it later on.
        marginSeparation = 0;
    }

    // how far between us and the leftward profile at layout?
    node.nodeNeighborSeparation = marginSeparation;
    
    if (node.leaf()) {
        // how much separation does this node have beteen itself and any node that isn't a leftward descendant of its parent?
        // this exclusion principle is only between leftward siblings, 
        // these cases are only true for leaves
        if (node.maxdepth <= parent_left_depth) {
            node.minSeparationToLeftwardCousins = ranksep(node.rank, marginSeparation);
            node.minSeparationToUnrelated = null;
        }
        else {
            node.minSeparationToUnrelated = marginSeparation;
            node.minSeparationToLeftwardCousins = null;
        }
    
        node.x = rank_margins[node.rank];
        rank_margins[node.rank] += node.boxwidth;
        if (node.parent && node.sib_index == node.parent.count() - 1) {
            rank_margins[node.rank] += SUBTREE_W_SEPARATION;
        }
        else {
            rank_margins[node.rank] += W_SEPARATION;
        }
        await debug_step(); // DEBUG
        return;
    }

    // our left child has the first chance to set minimums.
    // We run it with the parent left depth, because by definition this node defines
    // our first stab into the left profile, and we ourselves have claimed no
    // ranks
    await _lda_layout(node.child(0), rank_margins, profile_patches, parent_left_depth, left_sibling_depth);
    let minProfileDistanceToUnrelated = node.child(0).minSeparationToUnrelated;
    //let minProfileDistanceToNodeCousins = node.child(0).minSeparationToLeftwardCousins; // these are actually this-node cousins, they just start out identical to the left child.

    let claimedDepth = node.child(0).maxdepth;

    for (let i = 1; i < node.count(); i++) {
        let c = node.child(i);
        await _lda_layout(c, rank_margins, profile_patches, claimedDepth, node.child(i - 1).maxdepth);
        
        if (c.minSeparationToUnrelated != null) {
            let slipDistance = c.minSeparationToUnrelated;
            if (slipDistance > 0) {
                console.log("contraction");
                move_tree_deferred(c, -slipDistance);
                await debug_step(); // DEBUG
                profile_patches[c.rank] = make_patch(-slipDistance, c.maxdepth);
            }
        }

        if (c.maxdepth > claimedDepth) claimedDepth = c.maxdepth;
    }

    if (minProfileDistanceToUnrelated == null) {
        minProfileDistanceToUnrelated = 0;
    }

    node.leftProfile = Array.from(rank_margins); // DEBUG

    let midpoint = (node.child(0).x + node.child(-1).layout_natural_right()) / 2.0;
    midpoint -= node.halfw();

    node.x = midpoint; // the Math.max here is to deal with a JavaScript rounding error that propagates into a logic error.
    let centeringSeparation = node.x - rank_margins[node.rank]; // x must 0 or rightward of its starting location, as all children are strung out rightward.
    rank_margins[node.rank] = node.x + node.boxwidth;

    if (node.parent && node.sib_index == node.parent.count() - 1) {
        rank_margins[node.rank] += SUBTREE_W_SEPARATION;
    }
    else {
        rank_margins[node.rank] += W_SEPARATION;
    }

    node.nodeNeighborSeparation = marginSeparation + centeringSeparation; //Math.max(marginSeparation, centeringSeparation); // either the natural place, or the centered place, whichever is bigger (including infinity).

    node.minSeparationToUnrelated = Math.min(node.nodeNeighborSeparation, minProfileDistanceToUnrelated);
    //node.minSeparationToLeftwardCousins = Math.min(node.nodeNeighborSeparation, minProfileDistanceToNodeCousins);

    await debug_step(); // DEBUG
}

async function layout_tree(root) {
    let before = Date.now();

    //_layout(root, W_SEPARATION);  

    let rank_margins = new Array(root.maxdepth + 1);
    rank_margins[0] = 0;

    let patch_array = new Array();
    patch_array.push(null);

    for (let i = 1; i <= root.maxdepth + 1; i++) {
        rank_margins[i] = null;
        patch_array.push(null);
    }
    await _lda_layout(root, rank_margins, patch_array, 0, 0);
    //await _lda_skew_tree(root, 0);

    let after = Date.now();
    _layout_runtime = after - before;


    root.resolve_delta(0.0);

    iter_all(n => n.pos_x = n.x);
    finishedLayout = true;
    draw_all_configured();
}

// *********************************************************************************

function draw_node_profile(ctx, n) {
    for (let rank = 0; rank <= n.maxdepth; rank++) {
        ctx.strokeStyle = 'orange';
        ctx.lineWidth = 6;

        let rightProfileX = n.rightProfile[rank];
        if (rightProfileX == null) continue;

        ctx.beginPath();
        ctx.moveTo(rightProfileX, rank * RANK_SEPARATION - BOX_TOP_OFFSET);
        ctx.lineTo(rightProfileX, rank * RANK_SEPARATION - BOX_TOP_OFFSET + BOX_HEIGHT);
        ctx.stroke();


        let leftProfileX = n.leftProfile[rank];
        if (leftProfileX == null) continue;

        ctx.strokeStyle = 'cyan';
        ctx.beginPath();
        ctx.moveTo(leftProfileX, rank * RANK_SEPARATION - BOX_TOP_OFFSET);
        ctx.lineTo(leftProfileX, rank * RANK_SEPARATION - BOX_TOP_OFFSET + BOX_HEIGHT);
        ctx.stroke();
    }
}


function NOT_draw_node_profile(ctx, n) {
    for (let rank = n.rank; rank <= n.maxdepth; rank++) {
        ctx.strokeStyle = 'orange';
        ctx.lineWidth = 6;

        let rightProfile = n.right_profile_for_rank(rank);
        if (rightProfile == null) {
            //console.log("no right profile");
        }

        let leftProfile = n.left_profile_for_rank(rank);
        if (leftProfile == null) {
            //console.log("no left profile");
        }

        let rightProfileX = rightProfile;//+ n.non_tagging_delta_sum();
        let leftProfileX = leftProfile;//+ n.non_tagging_delta_sum();

        ctx.beginPath();
        ctx.moveTo(rightProfileX, rank * RANK_SEPARATION - BOX_TOP_OFFSET);
        ctx.lineTo(rightProfileX, rank * RANK_SEPARATION - BOX_TOP_OFFSET + BOX_HEIGHT);
        ctx.stroke();

        ctx.strokeStyle = 'cyan';

        // ctx.beginPath();
        // ctx.moveTo(leftProfileX, rank * RANK_SEPARATION - BOX_TOP_OFFSET);
        // ctx.lineTo(leftProfileX, rank * RANK_SEPARATION - BOX_TOP_OFFSET + BOX_HEIGHT);
        // ctx.stroke();
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

function copy_subtree_profile(v) {
    PROFILE_UPDATES++;
    let leftChild = v.child(0);
    v.set_left_profile(v.rank + 1, leftChild.left_profile_for_rank(v.rank + 1) + leftChild.delta);

    let rightChild = v.child(-1);
    v.set_right_profile(v.rank + 1, rightChild.right_profile_for_rank(v.rank + 1) + rightChild.delta);

    for (let i = v.rank + 2; i <= v.maxdepth; i++) { // not my rank, and not my children's rank either
        PROFILE_UPDATES++;
        for (let e of Array.from(v.children).reverse()) {
            let c = e.target;
            let childProfile = c.right_profile_for_rank(i);
            if (childProfile == null) continue;
            v.set_right_profile(i, childProfile + c.delta);
            break;
        }

        for (let e of v.children) {
            let c = e.target;
            let childProfile = c.left_profile_for_rank(i);
            if (childProfile == null) continue;
            v.set_left_profile(i, childProfile + c.delta);
            break;
        }
    }
}

function _layout(v, distance) {
    LAYOUT_RECURSION_COUNTER++;
    v.placedStep = LAYOUT_RECURSION_COUNTER;

    let separationDistance = W_SEPARATION;
    if (v.sib_index == 0) {
        console.log("Placing with tree separation.", v.label, v.id);
        separationDistance = SUBTREE_W_SEPARATION;
    }

    if (v.rankorder > 0) {
        if (PROFILE_COLLISION_MODE) {
            v.x = rank_profile_left(v).right_profile_xformed(v.rank) + separationDistance;
        }
        else {
            v.x = rank_left(v).layout_right_side() + separationDistance;
        }
        let common = find_common(v, rank_left(v));
        common.tag_common++;
        common.last_common = LAYOUT_RECURSION_COUNTER;
    }
    else {
        v.x = 0.0;
    }

    v.set_left_profile(v.rank, v.x);
    v.set_right_profile(v.rank, v.x + v.boxwidth);
    v.claim_own_profile();

    //await debug_step(); // DEBUG
    
    if (v.leaf()) {
        mark_wave(v);
        return;
    }

    // inner node
    let cCount = v.count();
    for (let i = 0; i < cCount; i++) {
        let c = v.child(i);
        //await _layout(c, distance); // DEBUG
        _layout(c, distance);
    }

    // stack between and above leaves
    let midpoint = (v.child(0).x + v.child(-1).layout_natural_right()) / 2.0;
    let natural = midpoint - v.halfw();
    v.x = natural; // set the natural midpoint, but we'll still adjust farther along
    
    v.set_left_profile(v.rank, v.x);
    v.set_right_profile(v.rank, v.x + v.boxwidth);
    
    let lefthandMargin = 0;
    let lefthand = PROFILE_COLLISION_MODE ? rank_profile_left(v) : rank_left(v);
    
    if (lefthand) {
        if (PROFILE_COLLISION_MODE) {
            lefthandMargin = lefthand.right_profile_xformed(v.rank) + separationDistance;
        }
        else {
            lefthandMargin = lefthand.layout_right_side() + separationDistance;
        }
    }

    let wantedMove = lefthandMargin - natural;

    copy_subtree_profile(v);

    do_constrained_move(v, wantedMove, false);

    if (MOVE_INNER_MODE) {
        for (let e of v.children.slice(0).reverse()) {
            let c = e.target;
            //let stress = v.layout_left_side() + v.childIdeals[c.sib_index] - c.layout_left_side();
            let stress = v.x - v.delta + v.childIdeals[c.sib_index] - c.x - c.delta;
            if (stress > 0) {
                do_constrained_move(c, stress, true);
            }
        }
        // I think this is maybe unnecessary... the right-hand profile can't move, and the left-hand profile
        // is never needed again. No... maybe it is... if we're the right-hand subchild of a new getting
        // laid out.
        copy_subtree_profile(v);
    }
   

    v.dominate_rank_profile();
    //v.tag_common = 0; // reset the counter now that we're "in place".

    mark_wave(v);
    //await debug_step(); // DEBUG
    return v;
}

function constrain_by_left_profile(v, wantedMove) {
    PROFILE_QUERIES++;

    console.log("constraining left, moving", v.label, v.id);

    let commons = new Set(); // profiling only.

    let leftEdge = v.subtree_left_edge();

    for (let i = 0; i < leftEdge.length; i++) {
        PROFILE_QUERIES_SUB++;
        let leftProfileRoot = rank_profile_left(leftEdge[i]);
        if (!leftProfileRoot) {
            //console.log("no left root.");
            continue;
        }

        leftProfileRoot.tag = 5;
        let common = find_common(v, rank_left(v));
        if (!commons.has(common)) {
            common.tag_common++;
            common.last_common = LAYOUT_RECURSION_COUNTER;
            commons.add(common);
        }

        console.log("left, right", leftProfileRoot.right_edge(v.rank + i).label, v.left_edge(v.rank + i).label);

        let leftmargin = leftProfileRoot.right_profile_xformed(v.rank + i);
        if (leftProfileRoot.right_edge(v.rank + i).parent == leftEdge[i].parent) { 
            leftmargin += W_SEPARATION;
        }
        else {
            console.log("subtree separation left");
            leftmargin += SUBTREE_W_SEPARATION;
        }
        //leftmargin += W_SEPARATION;

        let targetX = v.left_profile_for_rank(v.rank + i) + wantedMove;

        let overlap = targetX - leftmargin;
            
        if (overlap < 0) {
            wantedMove -= overlap;
        }
    }

    return wantedMove;
}

function constrain_by_right_profile(v, wantedMove) {
    PROFILE_QUERIES++;

    let commons = new Set(); // profiling only.

    let rightEdge = v.subtree_right_edge();

    for (let i = 0; i < rightEdge.length; i++) {
        PROFILE_QUERIES_SUB++;
        let rightProfileRoot = rank_profile_right(rightEdge[i]);
        if (!rightProfileRoot) {
            //console.log("no right root.");
            continue;
        }

        rightProfileRoot.tag = 5;
        let common = find_common(v, rank_right(v));
        if (!commons.has(common)) {
            common.tag_common++;
            common.last_common = LAYOUT_RECURSION_COUNTER;
            commons.add(common);
        }

        let rightMargin = rightProfileRoot.left_profile_xformed(v.rank + i);

        if (rightProfileRoot.left_edge(v.rank + i).parent == rightEdge[i].parent) { 
            rightMargin -= W_SEPARATION;
        }
        else {
            console.log("subtree separation right");
            rightMargin -= SUBTREE_W_SEPARATION;
        }

        let targetRightEdge = v.right_profile_xformed(v.rank + i) + wantedMove;

        let overlap = targetRightEdge - rightMargin;

        if (overlap > 0) {
            wantedMove -= overlap;
        }
    }

    return wantedMove;
}

function do_constrained_move(v, wantedMove, doRightCheck = true) {
    const nodeLocalEdgeLists = true;

    v.tag3 = 5;
    

    if (wantedMove == 0) { 
        return 0; 
    }
    else if (wantedMove < 0) { // we're moving left
        if (PROFILE_COLLISION_MODE) {
            wantedMove = constrain_by_left_profile(v, wantedMove);
        }
        else {
            let leftEdge;
            if (nodeLocalEdgeLists) {
                leftEdge = v.subtree_left_edge();
            } 
            else { 
                leftEdge = wavefront_subtree_left_edge(v) 
            };
            wantedMove = constrain_by_left_edge(leftEdge, wantedMove);
        }
    }
    else if (doRightCheck && wantedMove > 0) {
        if (PROFILE_COLLISION_MODE) {
            wantedMove = constrain_by_right_profile(v, wantedMove);
        }
        else {
            let rightEdge;
            if (nodeLocalEdgeLists) {
                rightEdge = v.subtree_right_edge();
            }
            else {
                rightEdge = wavefront_subtree_right_edge(v);;
            }
            wantedMove = constrain_by_right_edge(rightEdge, wantedMove);
        }
    }

    const deferred = DEFERRED_MOVE_MODE;
    if (deferred) {
        move_tree_deferred(v, wantedMove);
    }
    else {
        move_tree(v, wantedMove);
    }

    v.move_whole_profile(wantedMove);

    return wantedMove; // return the amount actually moved.
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
    PROFILE_QUERIES++;
    let commons = new Set();

    for (let v of edge_list) {
        PROFILE_QUERIES_SUB++;

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

    //commons.forEach( n => n.highlight_edges("red"));

    return amount;
}

function constrain_by_right_edge(edge_list, amount) {
    PROFILE_QUERIES++;
    let commons = new Set();

    for (let v of edge_list) {
        PROFILE_QUERIES_SUB++;
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




var move_tree = function(v, amount) {
    MOVE_COUNTER++;
    v.tag4 = true;
    v.lastMoveStep = LAYOUT_RECURSION_COUNTER;

    v.x += amount;
    for (let edge of v.children) {
        move_tree(edge.target, amount);
    }
}

var _layout_runtime = -1;


// UI

var xform_point = function(_x, _y) {
    return {
        x: _x / g_scale + g_pan_x ,
        y: _y / g_scale+ g_pan_y
    }
}

var _cur_x = 0;
var _cur_y = 0;

var _user_dragging = false;
var _drag_pan_x = 0;
var _drag_pan_y = 0;
var _user_drag_start_x = 0;
var _user_drag_start_y = 0;

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

    // if (_displayed_node) {
    //     _displayed_node.highlight_edges(false);
    // }

    _displayed_node = n;
    //_displayed_node.highlight_edges("orange", "cyan");
    if (finishedLayout) {
        draw_all_configured();
    }

    let idealDifference = NaN;
    if (n.parent) {
        idealDifference = n.parent.childIdeals[n.sib_index] + n.parent.x - n.x;
    }

    let info_div = document.getElementById("node_info");
    info_div.innerText = "";
    let extra = {
        "x" : n.x,
        "delta" : n.delta,
        "left sep" : n.nodeNeighborSeparation,
        "cousin sep" : n.minSeparationToLeftwardCousins,
        "rank" : n.rank,
        "unrelated sep" : n.minSeparationToUnrelated,
        "parent wave" : n.left_parent_depth_at_layout,
        "left sibling depth" : n.left_sib_debug_depth
    };
    // let extra = {
    //     "delta" : n.delta, 
    //     "deltasum" : n.non_tagging_delta_sum(),
    //     "x" : n.x,
    //     "id" : n.id,
    //     "stress" : idealDifference,
    //     "redge" : n.x + n.boxwidth,
    //     "node moves" : n.moveCount,
    //     "placed at" : n.placedStep,
    //     "last move" : n.lastMoveStep,
    //     "last common" : n.last_common,
    //     "common count" : n.tag_common,
    //     "depth" : n.maxdepth, 
    //     "n nodes" : Object.keys(_all_nodes).length,
    //     "sum count" : DELTA_SUM_COUNTER,
    //     "profile updates" : PROFILE_UPDATES,
    //     "preprocessing" : PROFILE_BUILDING,
    //     "queries" : PROFILE_QUERIES,
    //     "query subs" : PROFILE_QUERIES_SUB,
    //     "left count" : LEFT_SIDE_COUNTER,
    //     "right count" : RIGHT_SIDE_COUNTER,
    //     "total moves" : MOVE_COUNTER,
    //     "runtime" : _layout_runtime
    // };
    layout_obj(info_div, n.label || n.id, n.payload, extra);
}

// Startup


var load_nodes = function(ctx) {
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

    iter_all(n => n.measure_self(ctx));
    _root_node.rank_self(0, new Set());
    iter_all(n => n.calculate_ideal_child_positions());
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

        if (_displayed_node) {
            draw_node_profile(ctx, _displayed_node);
        }
        ctx.restore();
    }
}

var draw_all_configured;

var start_limetree = function() {
    let canvas = document.getElementById('tree_canvas');
    let ctx = canvas.getContext('2d'); // we need this first to measure nodes.

    load_nodes(ctx);
    //set_node_data(_root_node);

    
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

    

    draw_all_configured = _ => draw_all(canvas);

    layout_tree(_root_node);
    
    
    draw_all_configured();
}

// parse trees
//const _node_data = `{"nodes": [{"production": "global_list", "type": null, "value": null, "id": 0, "line": -1, "attr": {}, "c": [{"production": "pipeline", "type": null, "value": null, "id": 1, "line": 1, "attr": {}, "c": [{"production": null, "type": "IDENT", "value": "_1997", "id": 2, "line": 1, "attr": {}, "c": []}, {"production": "component_contents", "type": null, "value": null, "id": 3, "line": -1, "attr": {}, "c": [{"production": "Gets", "type": null, "value": null, "id": 4, "line": 2, "attr": {}, "c": [{"production": "vardecl", "type": null, "value": null, "id": 5, "line": 2, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "gl_Position:", "id": 6, "line": 2, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 7, "line": -1, "attr": {}, "c": []}, {"production": "index", "type": null, "value": null, "id": 8, "line": -1, "attr": {}, "c": []}]}, {"production": "MMult", "type": null, "value": null, "id": 9, "line": 3, "attr": {}, "c": [{"production": "MMult", "type": null, "value": null, "id": 10, "line": 3, "attr": {}, "c": [{"production": "MMult", "type": null, "value": null, "id": 11, "line": 3, "attr": {}, "c": [{"production": "staged_vardecl", "type": null, "value": null, "id": 12, "line": 3, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "u[", "id": 13, "line": 3, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 14, "line": 3, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "projMatrix:", "id": 15, "line": 3, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 16, "line": -1, "attr": {}, "c": [{"production": "typeref", "type": null, "value": null, "id": 17, "line": 3, "attr": {}, "c": [{"production": null, "type": "IDENT", "value": "mat4", "id": 18, "line": 3, "attr": {}, "c": []}]}]}, {"production": "index", "type": null, "value": null, "id": 19, "line": -1, "attr": {}, "c": []}]}]}, {"production": "staged_vardecl", "type": null, "value": null, "id": 20, "line": 4, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "u[", "id": 21, "line": 4, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 22, "line": 4, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "viewMatrix:", "id": 23, "line": 4, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 24, "line": -1, "attr": {}, "c": [{"production": "typeref", "type": null, "value": null, "id": 25, "line": 4, "attr": {}, "c": [{"production": null, "type": "IDENT", "value": "mat4", "id": 26, "line": 4, "attr": {}, "c": []}]}]}, {"production": "index", "type": null, "value": null, "id": 27, "line": -1, "attr": {}, "c": []}]}]}]}, {"production": "staged_vardecl", "type": null, "value": null, "id": 28, "line": 5, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "u[", "id": 29, "line": 5, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 30, "line": 5, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "modelMatrix:", "id": 31, "line": 5, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 32, "line": -1, "attr": {}, "c": [{"production": "typeref", "type": null, "value": null, "id": 33, "line": 5, "attr": {}, "c": [{"production": null, "type": "IDENT", "value": "mat4", "id": 34, "line": 5, "attr": {}, "c": []}]}]}, {"production": "index", "type": null, "value": null, "id": 35, "line": -1, "attr": {}, "c": []}]}]}]}, {"production": "staged_vardecl", "type": null, "value": null, "id": 36, "line": 6, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "a[", "id": 37, "line": 6, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 38, "line": 6, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "position:", "id": 39, "line": 6, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 40, "line": -1, "attr": {}, "c": [{"production": "typeref", "type": null, "value": null, "id": 41, "line": 6, "attr": {}, "c": [{"production": null, "type": "IDENT", "value": "vec4", "id": 42, "line": 6, "attr": {}, "c": []}]}]}, {"production": "index", "type": null, "value": null, "id": 43, "line": -1, "attr": {}, "c": [{"production": null, "type": "INTEGER", "value": "0", "id": 44, "line": 6, "attr": {}, "c": []}]}]}]}]}]}, {"production": "Gets", "type": null, "value": null, "id": 45, "line": 8, "attr": {}, "c": [{"production": "staged_vardecl", "type": null, "value": null, "id": 46, "line": 8, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "f[", "id": 47, "line": 8, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 48, "line": 8, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "f_color:", "id": 49, "line": 8, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 50, "line": -1, "attr": {}, "c": []}, {"production": "index", "type": null, "value": null, "id": 51, "line": -1, "attr": {}, "c": [{"production": null, "type": "INTEGER", "value": "0", "id": 52, "line": 8, "attr": {}, "c": []}]}]}]}, {"production": "Gets", "type": null, "value": null, "id": 53, "line": 9, "attr": {}, "c": [{"production": "staged_vardecl", "type": null, "value": null, "id": 54, "line": 9, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "v[", "id": 55, "line": 9, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 56, "line": 9, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "v_color:", "id": 57, "line": 9, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 58, "line": -1, "attr": {}, "c": []}, {"production": "index", "type": null, "value": null, "id": 59, "line": -1, "attr": {}, "c": []}]}]}, {"production": "staged_vardecl", "type": null, "value": null, "id": 60, "line": 10, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "a[", "id": 61, "line": 10, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 62, "line": 10, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "a_color:", "id": 63, "line": 10, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 64, "line": -1, "attr": {}, "c": [{"production": "typeref", "type": null, "value": null, "id": 65, "line": 10, "attr": {}, "c": [{"production": null, "type": "IDENT", "value": "vec4", "id": 66, "line": 10, "attr": {}, "c": []}]}]}, {"production": "index", "type": null, "value": null, "id": 67, "line": -1, "attr": {}, "c": [{"production": null, "type": "INTEGER", "value": "1", "id": 68, "line": 10, "attr": {}, "c": []}]}]}]}]}]}, {"production": "Gets", "type": null, "value": null, "id": 69, "line": 14, "attr": {}, "c": [{"production": "vardecl", "type": null, "value": null, "id": 70, "line": 14, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "pi:", "id": 71, "line": 14, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 72, "line": -1, "attr": {}, "c": []}, {"production": "index", "type": null, "value": null, "id": 73, "line": -1, "attr": {}, "c": []}]}, {"production": null, "type": "FLOAT", "value": "3.14", "id": 74, "line": 14, "attr": {}, "c": []}]}]}]}]}], "styles": [], "edges": [], "links": [], "label_keys": ["production", "type"], "payload_objects": ["attr"]}`;
const _node_data = `{"nodes": [{"production": "global_list", "type": null, "value": null, "id": 0, "line": -1, "attr": {}, "c": [{"production": "pipeline", "type": null, "value": null, "id": 1, "line": 1, "attr": {}, "c": [{"production": null, "type": "IDENT", "value": "_1997", "id": 2, "line": 1, "attr": {}, "c": []}, {"production": "component_contents", "type": null, "value": null, "id": 3, "line": -1, "attr": {}, "c": [{"production": "Gets", "type": null, "value": null, "id": 4, "line": 2, "attr": {}, "c": [{"production": "staged_vardecl", "type": null, "value": null, "id": 5, "line": 2, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "f[", "id": 6, "line": 2, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 7, "line": 2, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "f_color:", "id": 8, "line": 2, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 9, "line": -1, "attr": {}, "c": []}, {"production": "index", "type": null, "value": null, "id": 10, "line": -1, "attr": {}, "c": [{"production": null, "type": "INTEGER", "value": "0", "id": 11, "line": 2, "attr": {}, "c": []}]}]}]}, {"production": "Gets", "type": null, "value": null, "id": 12, "line": 3, "attr": {}, "c": [{"production": "staged_vardecl", "type": null, "value": null, "id": 13, "line": 3, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "v[", "id": 14, "line": 3, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 15, "line": 3, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "v_color:", "id": 16, "line": 3, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 17, "line": -1, "attr": {}, "c": []}, {"production": "index", "type": null, "value": null, "id": 18, "line": -1, "attr": {}, "c": []}]}]}, {"production": "staged_vardecl", "type": null, "value": null, "id": 19, "line": 4, "attr": {}, "c": [{"production": null, "type": "STAGEREF", "value": "a[", "id": 20, "line": 4, "attr": {}, "c": []}, {"production": "vardecl", "type": null, "value": null, "id": 21, "line": 4, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "a_color:", "id": 22, "line": 4, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 23, "line": -1, "attr": {}, "c": [{"production": "typeref", "type": null, "value": null, "id": 24, "line": 4, "attr": {}, "c": [{"production": null, "type": "IDENT", "value": "vec4", "id": 25, "line": 4, "attr": {}, "c": []}]}]}, {"production": "index", "type": null, "value": null, "id": 26, "line": -1, "attr": {}, "c": [{"production": null, "type": "INTEGER", "value": "1", "id": 27, "line": 4, "attr": {}, "c": []}]}]}]}]}]}, {"id": "blahblahblah", "!label": "freestanding"}, {"id": "blahblahblah2", "!label": "fs2"}, {"production": "Gets", "type": null, "value": null, "id": 28, "line": 8, "attr": {}, "c": [{"production": "vardecl", "type": null, "value": null, "id": 29, "line": 8, "attr": {}, "c": [{"production": null, "type": "VARDECL", "value": "pi:", "id": 30, "line": 8, "attr": {}, "c": []}, {"production": "type", "type": null, "value": null, "id": 31, "line": -1, "attr": {}, "c": []}, {"production": "index", "type": null, "value": null, "id": 32, "line": -1, "attr": {}, "c": []}]}, {"production": null, "type": "FLOAT", "value": "3.14", "id": 33, "line": 8, "attr": {}, "c": []}]}]}]}]}], "styles": [], "edges": [], "links": [], "label_keys": ["production", "type"], "payload_objects": ["attr"]}`

// random graphs
//const _node_data = `{"nodes": [{"!id": 0, "!label": "WTOEAMTB", "children": [{"!id": 1, "!label": "QLKEI", "children": []}, {"!id": 2, "!label": "AJUFJREXABEVYR", "children": [{"!id": 3, "!label": "OMBTL", "children": [{"!id": 4, "!label": "BHEVDXD", "children": [{"!id": 5, "!label": "TNXVYJXRSQEP", "children": []}]}, {"!id": 6, "!label": "TKKRTNPHESO", "children": [{"!id": 7, "!label": "TTVPCFPUN", "children": [{"!id": 8, "!label": "VDHQX", "children": [{"!id": 9, "!label": "VCOTQT", "children": [{"!id": 10, "!label": "EFSNTSSVVYF", "children": [{"!id": 11, "!label": "OHJLMBCMTUFRN", "children": [{"!id": 12, "!label": "KXFWTACNPFV", "children": []}, {"!id": 13, "!label": "MDJOTOOHTO", "children": []}, {"!id": 14, "!label": "IFYQIOANGA", "children": []}, {"!id": 15, "!label": "LGRITMAFAONCU", "children": []}]}]}, {"!id": 16, "!label": "CHRIFGUYBQK", "children": [{"!id": 17, "!label": "XQLTIGFMXQNEGO", "children": []}, {"!id": 18, "!label": "KOIYCJPPJGBF", "children": [{"!id": 19, "!label": "WRVRBHDO", "children": []}]}, {"!id": 20, "!label": "IGIEQPGKU", "children": []}]}, {"!id": 21, "!label": "ADSGRHHKND", "children": [{"!id": 22, "!label": "LROVCAKXKLJDV", "children": [{"!id": 23, "!label": "ISBQKYMKDG", "children": []}, {"!id": 24, "!label": "AACVGDGX", "children": []}, {"!id": 25, "!label": "RETOOORNY", "children": []}]}, {"!id": 26, "!label": "XQCEI", "children": [{"!id": 27, "!label": "UOSXNKINKJ", "children": []}]}]}]}]}]}, {"!id": 28, "!label": "NQLVB", "children": []}, {"!id": 29, "!label": "PFVXSTCWBRDW", "children": [{"!id": 30, "!label": "BKCRKY", "children": [{"!id": 31, "!label": "MWBDWHDVMDSPX", "children": [{"!id": 32, "!label": "IJAVPIP", "children": [{"!id": 33, "!label": "RKDVK", "children": [{"!id": 34, "!label": "APEKAG", "children": []}, {"!id": 35, "!label": "WWKDEDJBY", "children": []}, {"!id": 36, "!label": "PUHKSUHBOCLAE", "children": []}, {"!id": 37, "!label": "OQMGE", "children": []}]}]}]}, {"!id": 38, "!label": "CICMRWCCQVGG", "children": [{"!id": 39, "!label": "NOSBWTPPK", "children": []}]}]}, {"!id": 40, "!label": "OQIFPJR", "children": [{"!id": 41, "!label": "MVNUEEIKYQKPXM", "children": [{"!id": 42, "!label": "CSUHUYDR", "children": [{"!id": 43, "!label": "JIKLRTFXPM", "children": [{"!id": 44, "!label": "OAREIEDKDYHN", "children": []}, {"!id": 45, "!label": "FRVJUMUPGT", "children": []}, {"!id": 46, "!label": "KXXSOGNFWASTJS", "children": []}]}, {"!id": 47, "!label": "WNUQWE", "children": [{"!id": 48, "!label": "IRDHSMWPNYF", "children": []}, {"!id": 49, "!label": "TIFPOVXO", "children": []}]}]}]}]}]}]}]}]}]}], "styles": [], "edges": [], "links": [], "label_keys": [], "payload_objects": []}`
//const _node_data = `{"nodes": [{"!id": 0, "!label": "RSWGTTVKPHAV", "children": [{"!id": 1, "!label": "UCOUGPLLGRK", "children": []}, {"!id": 2, "!label": "EXHCTEBVRXPA", "children": [{"!id": 3, "!label": "LRDXCQNOMIO", "children": [{"!id": 4, "!label": "YAFRWXMQMASYF", "children": [{"!id": 5, "!label": "TXWGKHRBPHAJN", "children": [{"!id": 6, "!label": "XKYTLED", "children": []}]}, {"!id": 7, "!label": "EOAFYTJYJGC", "children": [{"!id": 8, "!label": "LMWYXFQQDUV", "children": []}]}, {"!id": 9, "!label": "XDPDLPY", "children": [{"!id": 10, "!label": "KLWNSOQUBMJP", "children": [{"!id": 11, "!label": "GDVMUWR", "children": [{"!id": 12, "!label": "FXVSNRHKTPENWP", "children": [{"!id": 13, "!label": "QEEORNIG", "children": []}, {"!id": 14, "!label": "NXTKFSLXKEAUFU", "children": [{"!id": 15, "!label": "JBBMMS", "children": []}, {"!id": 16, "!label": "RMIMU", "children": []}]}, {"!id": 17, "!label": "LGOQGJAWFFIBL", "children": [{"!id": 18, "!label": "YNHSGIRYVJBBTQ", "children": []}, {"!id": 19, "!label": "NAMWW", "children": []}]}, {"!id": 20, "!label": "TMBNPNF", "children": []}]}, {"!id": 21, "!label": "WKCJQTDL", "children": [{"!id": 22, "!label": "YVLNWSEN", "children": [{"!id": 23, "!label": "GYMQNHEYXRLBT", "children": []}, {"!id": 24, "!label": "IEQNYQEUQLXRI", "children": []}, {"!id": 25, "!label": "YKKAEO", "children": []}]}, {"!id": 26, "!label": "YYBNBMU", "children": [{"!id": 27, "!label": "CDYHGNVPRJTUP", "children": []}]}]}]}, {"!id": 28, "!label": "UBNQLOITHQFGXX", "children": [{"!id": 29, "!label": "UPSRTMV", "children": [{"!id": 30, "!label": "BLODCPXFP", "children": [{"!id": 31, "!label": "VXDQCKAFKDP", "children": []}, {"!id": 32, "!label": "QPXLV", "children": []}]}, {"!id": 33, "!label": "BGJHDNGHBFNTE", "children": [{"!id": 34, "!label": "WVBHD", "children": []}, {"!id": 35, "!label": "KTWMAFMEOQCJF", "children": []}, {"!id": 36, "!label": "VCWSVPREY", "children": []}, {"!id": 37, "!label": "TITWKWICD", "children": []}]}]}, {"!id": 38, "!label": "SPPNKGY", "children": [{"!id": 39, "!label": "WILHQPS", "children": [{"!id": 40, "!label": "YRSOCLSBPK", "children": []}]}]}, {"!id": 41, "!label": "YDMHLCOVW", "children": [{"!id": 42, "!label": "TYBTLAQIRIF", "children": [{"!id": 43, "!label": "XBPUKIKMO", "children": []}]}, {"!id": 44, "!label": "ESDXTQOUBEIE", "children": [{"!id": 45, "!label": "VCRVNKSWDH", "children": []}, {"!id": 46, "!label": "VHQUADHIHROXB", "children": []}, {"!id": 47, "!label": "VVOLFMKEPRFNR", "children": []}]}]}]}, {"!id": 48, "!label": "XBHSCYAEAVQO", "children": [{"!id": 49, "!label": "ISLYQJLU", "children": []}]}]}]}]}]}]}]}], "styles": [], "edges": [], "links": [], "label_keys": [], "payload_objects": []}`
//const _node_data = `{"nodes": [{"!id": 0, "!label": "GNKSJGQIU", "children": [{"!id": 1, "!label": "EFXMBOKOOCFNM", "children": [{"!id": 2, "!label": "CFKEQFIRELJ", "children": [{"!id": 3, "!label": "YJCLHTACCEXLU", "children": [{"!id": 4, "!label": "BERPVRKVSAE", "children": [{"!id": 5, "!label": "HEKYFLLNQX", "children": []}, {"!id": 6, "!label": "ACFSGIFBIS", "children": [{"!id": 7, "!label": "DXHBEUR", "children": [{"!id": 8, "!label": "SIDWNWRKTMG", "children": [{"!id": 9, "!label": "LIAPJUWUOPXHY", "children": [{"!id": 10, "!label": "CEFRV", "children": []}, {"!id": 11, "!label": "FGTFDVAYL", "children": []}]}]}, {"!id": 12, "!label": "ENTYTAJF", "children": [{"!id": 13, "!label": "VGUYGUK", "children": [{"!id": 14, "!label": "STJGWJMGWA", "children": []}, {"!id": 15, "!label": "DFAGIKDKOUTIDU", "children": []}, {"!id": 16, "!label": "UMGYXNKWKQG", "children": []}]}]}, {"!id": 17, "!label": "WRSYWPVKLRWRF", "children": [{"!id": 18, "!label": "TBBNXHVASKYU", "children": []}, {"!id": 19, "!label": "XKSOEXG", "children": [{"!id": 20, "!label": "RXIGDCWCNXM", "children": []}, {"!id": 21, "!label": "SXLVXTWXKV", "children": []}, {"!id": 22, "!label": "AEEGCBNLTXJPS", "children": []}, {"!id": 23, "!label": "KXODUPYKVIX", "children": []}]}, {"!id": 24, "!label": "RISUSQ", "children": [{"!id": 25, "!label": "KUWOMCXGJYYC", "children": []}]}]}, {"!id": 26, "!label": "WPNVAFGRGMHS", "children": [{"!id": 27, "!label": "THRRIXEJDXQF", "children": [{"!id": 28, "!label": "DMOMHALPMTB", "children": []}]}, {"!id": 29, "!label": "PGWCIKHFO", "children": [{"!id": 30, "!label": "UBGFCAYCOBVI", "children": []}, {"!id": 31, "!label": "PVSFQEQO", "children": []}, {"!id": 32, "!label": "TREJYE", "children": []}, {"!id": 33, "!label": "JBNGPHIUEGWM", "children": []}]}, {"!id": 34, "!label": "PHMYX", "children": [{"!id": 35, "!label": "HEAPLBAQAQLYEG", "children": []}]}]}]}, {"!id": 36, "!label": "GEMFW", "children": []}]}]}, {"!id": 37, "!label": "UEBOBJ", "children": [{"!id": 38, "!label": "BOYEGFGSUO", "children": [{"!id": 39, "!label": "YKCUHWGUW", "children": [{"!id": 40, "!label": "LGNJQ", "children": [{"!id": 41, "!label": "BAAJRVFUNLRLO", "children": [{"!id": 42, "!label": "FNJPHJSGDYQUC", "children": []}, {"!id": 43, "!label": "PHOVNN", "children": []}, {"!id": 44, "!label": "QWMHFDEKPHITP", "children": []}, {"!id": 45, "!label": "EHFXAWN", "children": []}]}, {"!id": 46, "!label": "SIUPXVNPMFIAAS", "children": [{"!id": 47, "!label": "ERCVGSJKM", "children": []}, {"!id": 48, "!label": "EHSYJLHGHYXLVR", "children": []}, {"!id": 49, "!label": "TEWGPLWSKKF", "children": []}]}]}]}]}]}]}]}]}]}], "styles": [], "edges": [], "links": [], "label_keys": [], "payload_objects": []}`
//const _node_data = `{"nodes": [{"!id": 0, "!label": "WNEOUTYH", "children": [{"!id": 1, "!label": "YXPPULM", "children": [{"!id": 2, "!label": "QMIPOBJPEMYYKLBEWOJNKRTTMFON", "children": [{"!id": 3, "!label": "OEMDVQJMPAJFBB", "children": [{"!id": 4, "!label": "UDAARBFI", "children": []}, {"!id": 5, "!label": "REIOECEX", "children": [{"!id": 6, "!label": "EUWAXWIWQIWL", "children": []}, {"!id": 7, "!label": "XUKYLAJYELNJCKFOEDAEGRWYYRW", "children": [{"!id": 8, "!label": "YVOGWUHYWAKBGDWLESHOPXRIG", "children": []}, {"!id": 9, "!label": "BNQWKTGPRQGYUMDTE", "children": [{"!id": 10, "!label": "BMAEDOMMDUNJGKCJEXGQJGS", "children": []}, {"!id": 11, "!label": "CXEFGYKDUMVIENGDIEPFJMY", "children": [{"!id": 12, "!label": "COEHIBCCUXDVOYESEWRDSV", "children": []}, {"!id": 13, "!label": "OKQAHNDTPNUDCACB", "children": []}, {"!id": 14, "!label": "WDDJDSJJCSTAHRXPBNB", "children": [{"!id": 15, "!label": "TOFOPBSOVYDMWATXYW", "children": []}, {"!id": 16, "!label": "VKNIXQKEFQDGKIGERSKIDXBBP", "children": []}, {"!id": 17, "!label": "LCKUMAPLYKUSYSVHFQYYCGTTRSM", "children": []}, {"!id": 18, "!label": "POIMEIAMEXAPWPJGVGKQCDJ", "children": []}]}]}]}, {"!id": 19, "!label": "TBDFEWWWBYXBFIGG", "children": []}, {"!id": 20, "!label": "NPKMIXXSPIFMKHA", "children": [{"!id": 21, "!label": "NLBKPBHOVO", "children": []}, {"!id": 22, "!label": "PEODUIRDRIKUYLTBCEGJITX", "children": [{"!id": 23, "!label": "LUMCOVIHECNTVMNOCAXULBNGGB", "children": [{"!id": 24, "!label": "LEYSVFX", "children": []}, {"!id": 25, "!label": "PWDFPCUCSNUNPFNOD", "children": []}, {"!id": 26, "!label": "HAUIYJQWQGIXUBEUJQ", "children": []}, {"!id": 27, "!label": "QYLORCKJQ", "children": []}, {"!id": 28, "!label": "BLXCQNGPAYRORQDM", "children": []}, {"!id": 29, "!label": "SSSIYWKYEWUFHID", "children": []}, {"!id": 30, "!label": "RBNQJRBDXMOS", "children": []}]}, {"!id": 31, "!label": "XSIUAHQSE", "children": []}, {"!id": 32, "!label": "GKXBCJSFBNJCENOVBGTGAXOERBC", "children": []}, {"!id": 33, "!label": "WPNOBCICSTVGJTDFH", "children": []}, {"!id": 34, "!label": "DPQHWMKWAMEX", "children": []}, {"!id": 35, "!label": "FLXPUKLNATAP", "children": []}]}, {"!id": 36, "!label": "LJHYNKSHVCEKGGE", "children": [{"!id": 37, "!label": "KVRPQLNUQUOGIAJCM", "children": []}, {"!id": 38, "!label": "LALMREWGLGC", "children": [{"!id": 39, "!label": "KVQKNCCHLUHWRGEHQVGTXMV", "children": []}, {"!id": 40, "!label": "ATWNTOGRGGTTVGORC", "children": []}, {"!id": 41, "!label": "DLPUBKDVCTBCCCLDWQNYOEPOF", "children": []}, {"!id": 42, "!label": "VRBFEWQU", "children": []}, {"!id": 43, "!label": "MSXARMGNFGAHCYKWJRIHI", "children": []}]}, {"!id": 44, "!label": "BGOLRWSOHRUIJCLOPDYNOW", "children": []}, {"!id": 45, "!label": "WYLKALKBCKIIWX", "children": []}, {"!id": 46, "!label": "LEWADDOEHYQXOHIHYR", "children": []}, {"!id": 47, "!label": "QCMBVKKH", "children": [{"!id": 48, "!label": "WJLUDVWLSRVIUEBLWUTRVHFDMYTE", "children": []}, {"!id": 49, "!label": "GUHNJECC", "children": []}, {"!id": 50, "!label": "ASYGURJSTPURNXHFAOLNNH", "children": []}, {"!id": 51, "!label": "OJAXHGKUVVJAOGWADOOYD", "children": []}, {"!id": 52, "!label": "QULGYD", "children": []}]}]}, {"!id": 53, "!label": "HOVELKGCAQJAQABTOEMPOIBEXQV", "children": []}, {"!id": 54, "!label": "KVFHLQCNINTNPYHLR", "children": []}, {"!id": 55, "!label": "ENKGOHHGDJQAATCTIITXJGDBIL", "children": []}, {"!id": 56, "!label": "JANSQKBFFNHNSXYS", "children": []}]}, {"!id": 57, "!label": "JMTWKAVMV", "children": []}]}, {"!id": 58, "!label": "OKXWWRIQYYINLKHATOQLRAYJWTOJ", "children": [{"!id": 59, "!label": "KJTNM", "children": []}, {"!id": 60, "!label": "IIDSIYLGBAPFYQDHKNOCFIW", "children": []}, {"!id": 61, "!label": "PSSJCTGDAKPQEU", "children": []}, {"!id": 62, "!label": "JGNYBFUQHCF", "children": []}, {"!id": 63, "!label": "TEDCLERMNOTAHNDAURQSMRQLQDPN", "children": []}, {"!id": 64, "!label": "BRMAEBVJ", "children": [{"!id": 65, "!label": "LTHSDXWSWXXJIFKNUEUTTTEFSMO", "children": []}]}, {"!id": 66, "!label": "QMTOFGGQYGMULIN", "children": [{"!id": 67, "!label": "WFINTGSJLSDXHONPSFD", "children": []}, {"!id": 68, "!label": "QCEHOJRWNKLFCPXXSD", "children": [{"!id": 69, "!label": "TDSBNJPIBXDM", "children": [{"!id": 70, "!label": "XQUFMKYSTPPQNIXYCDRSJOWIHKYK", "children": []}, {"!id": 71, "!label": "XBJOCOWOCLISCAPIUNWK", "children": []}, {"!id": 72, "!label": "XIFSOBHVUINOCF", "children": []}, {"!id": 73, "!label": "PBEIRYIBBLWLJTQBNAIYHHGBL", "children": []}]}, {"!id": 74, "!label": "QMECNJJWAPXSKXBSOLHBALI", "children": []}, {"!id": 75, "!label": "FMWJTJRU", "children": []}]}]}]}, {"!id": 76, "!label": "QTNTOCHXMMQDTSKXIPYRYCL", "children": [{"!id": 77, "!label": "NIXPREHI", "children": [{"!id": 78, "!label": "USCWXTIJJAJKXOFL", "children": []}]}, {"!id": 79, "!label": "GSFABUIMVQQP", "children": []}, {"!id": 80, "!label": "BTQOMOVBWUTDHAHTFHFUHNAY", "children": []}, {"!id": 81, "!label": "POMQT", "children": []}, {"!id": 82, "!label": "BQWNMSPAKMMYJANFBGRULKRKWJIKS", "children": []}]}, {"!id": 83, "!label": "JXTSCPUTBU", "children": []}, {"!id": 84, "!label": "PLBGSQQMQERSJJXMYLDA", "children": [{"!id": 85, "!label": "BDSCHRXDCAFFOQEFDGTXQSUW", "children": [{"!id": 86, "!label": "LUYRJE", "children": []}, {"!id": 87, "!label": "OQJXFHLRIJ", "children": []}, {"!id": 88, "!label": "OXYBLUAWGFN", "children": [{"!id": 89, "!label": "BMRDVLWVGDNUUPBGIDUGORK", "children": []}, {"!id": 90, "!label": "YQUMXCDBSYDCY", "children": []}]}, {"!id": 91, "!label": "IXOCSQMDIBUMTGFBOJA", "children": [{"!id": 92, "!label": "DXIMMTLNNVJFXSBSUBJ", "children": []}, {"!id": 93, "!label": "CFFQHXUURRSKMNHKE", "children": []}, {"!id": 94, "!label": "IQUJRVXTSETENHPSEUKGNC", "children": []}, {"!id": 95, "!label": "ENHKARENLPOTWOLEJFILHONUOPLG", "children": []}, {"!id": 96, "!label": "TJHIYAEMM", "children": []}]}, {"!id": 97, "!label": "VHBWTWPXCSXBMIIDI", "children": [{"!id": 98, "!label": "GTPDLNJCOLDOPLXFSNJQRWPS", "children": []}, {"!id": 99, "!label": "COGCGVABCCSCLA", "children": [{"!id": 100, "!label": "YVIHNEJWILXUCDMFCCLI", "children": []}, {"!id": 101, "!label": "UVHRN", "children": []}]}, {"!id": 102, "!label": "RKABBSUYVBMYKLCYNOYOXPHJWX", "children": []}, {"!id": 103, "!label": "CLFFEUFCBDE", "children": []}]}, {"!id": 104, "!label": "YABEMFODWUUSFDIXMVTWOFUM", "children": [{"!id": 105, "!label": "FDYURVNWQMBIUEHRSAJNAP", "children": []}, {"!id": 106, "!label": "OLCTNRNQM", "children": []}, {"!id": 107, "!label": "TNOUBM", "children": []}, {"!id": 108, "!label": "ASCLENCPWJRFATIJSUNNVVYVGT", "children": []}, {"!id": 109, "!label": "SMGNUUOTCHUBSAVGBJQYOLMFLERX", "children": []}, {"!id": 110, "!label": "HCYTGHMISIQDFBVDFPRG", "children": []}]}]}, {"!id": 111, "!label": "LWJVCIONAVYXVIDWXDS", "children": []}, {"!id": 112, "!label": "NUGTUGJQQYQXDKMUBSUWRM", "children": []}]}]}, {"!id": 113, "!label": "MRHEMEIEQHBRFNQOUV", "children": [{"!id": 114, "!label": "QSLMOMLOCJLFKAFIPFPCYJFX", "children": [{"!id": 115, "!label": "VLWRXXGJRXGTTUBVKNGBMYYGKSV", "children": []}, {"!id": 116, "!label": "HQFRRVJFDVRFPYNPTUBMHIQ", "children": []}, {"!id": 117, "!label": "RHLNECNJYEJUITQLR", "children": [{"!id": 118, "!label": "EUNATUGKPLDGHNHUMTEMPMCSJ", "children": []}, {"!id": 119, "!label": "SKROLRDNXVN", "children": []}, {"!id": 120, "!label": "TALRDODCYPDRVQNE", "children": []}, {"!id": 121, "!label": "WYNSSETDOEJQVBYYQQLSP", "children": [{"!id": 122, "!label": "XJHPRF", "children": []}, {"!id": 123, "!label": "LTINOKVCPKVGUJIWEYPRJVDXRS", "children": [{"!id": 124, "!label": "CILRJHRVU", "children": []}, {"!id": 125, "!label": "CHQLVFTFHKXAMGY", "children": []}, {"!id": 126, "!label": "SVNHS", "children": []}, {"!id": 127, "!label": "FKYMGDSL", "children": []}, {"!id": 128, "!label": "HSBOOIEYRWETWDSRGPHH", "children": []}, {"!id": 129, "!label": "WNSHLXBJBVPQUCSVLQLYPQPSN", "children": []}]}, {"!id": 130, "!label": "BVGPWQUDIEFTHKXWIYSJGUUHNS", "children": []}, {"!id": 131, "!label": "OAGSPVIRWWKLEWJEOUGASE", "children": []}, {"!id": 132, "!label": "SGLQVKUDDNKV", "children": []}]}, {"!id": 133, "!label": "OQSAJMRDMTASPPPOCKGSLGUBVCGV", "children": []}, {"!id": 134, "!label": "DLYHKPQOSRPTH", "children": []}]}]}]}, {"!id": 135, "!label": "IYFQO", "children": []}, {"!id": 136, "!label": "QCSSMDPEOXLKULCGIFDY", "children": [{"!id": 137, "!label": "GCGCHRPRDND", "children": [{"!id": 138, "!label": "ASVIBYEOSNUKTMENNFKGLVKAMK", "children": []}, {"!id": 139, "!label": "WWRXKOMEDCDAQMMAXSQG", "children": []}, {"!id": 140, "!label": "BWVYOJ", "children": []}, {"!id": 141, "!label": "ORYXTPVLFMKQXH", "children": []}, {"!id": 142, "!label": "SQSWPTPFUPCWDSRWDCEEQJ", "children": []}, {"!id": 143, "!label": "BTCOVSPHQHXQLHLQFNSDLJWCMU", "children": []}]}, {"!id": 144, "!label": "TNNLJ", "children": [{"!id": 145, "!label": "CUHFNOXLSBSUUNLUITVGSXDUUGV", "children": []}, {"!id": 146, "!label": "POHKQTAPXJUHDRGQTRK", "children": [{"!id": 147, "!label": "CHXBYCOEHPSPKMTKQBGR", "children": []}]}, {"!id": 148, "!label": "OQFDCLMTTOYVQYTERTXXG", "children": []}, {"!id": 149, "!label": "AFOHOGGQWFULJDYVGKXAGVL", "children": []}]}]}]}]}]}]}], "styles": [], "edges": [], "links": [], "label_keys": [], "payload_objects": []}`
//const _node_data = `{"nodes": [{"!id": 0, "!label": "HKEQOD", "children": [{"!id": 1, "!label": "WHUTN", "children": [{"!id": 2, "!label": "LWXYDNN", "children": [{"!id": 3, "!label": "AQQQKBE", "children": []}, {"!id": 4, "!label": "LPOCLW", "children": [{"!id": 5, "!label": "TPSSPPQ", "children": []}, {"!id": 6, "!label": "OHUOH", "children": []}, {"!id": 7, "!label": "GXXTOHV", "children": []}, {"!id": 8, "!label": "SEBGC", "children": [{"!id": 9, "!label": "DWUHB", "children": [{"!id": 10, "!label": "HGKOLC", "children": []}, {"!id": 11, "!label": "UBYNK", "children": [{"!id": 12, "!label": "OYILUSE", "children": []}, {"!id": 13, "!label": "RHNDRV", "children": []}, {"!id": 14, "!label": "TIFDYHV", "children": []}, {"!id": 15, "!label": "EFGYNN", "children": []}]}, {"!id": 16, "!label": "NQPWNVY", "children": []}]}, {"!id": 17, "!label": "KYBICBQ", "children": []}, {"!id": 18, "!label": "GMTRJ", "children": [{"!id": 19, "!label": "TSUTU", "children": [{"!id": 20, "!label": "SXTDBDG", "children": []}]}, {"!id": 21, "!label": "MDLHT", "children": []}]}, {"!id": 22, "!label": "TDWHX", "children": [{"!id": 23, "!label": "KLLLCQ", "children": [{"!id": 24, "!label": "GLDDEQM", "children": []}, {"!id": 25, "!label": "LGMQD", "children": []}, {"!id": 26, "!label": "DCTNIOW", "children": []}, {"!id": 27, "!label": "CKVEP", "children": []}]}]}]}]}, {"!id": 28, "!label": "QQNFJ", "children": [{"!id": 29, "!label": "IOBRA", "children": []}, {"!id": 30, "!label": "KHWNOQ", "children": []}, {"!id": 31, "!label": "NIWUIOL", "children": [{"!id": 32, "!label": "HFKIJWO", "children": [{"!id": 33, "!label": "WWTGJP", "children": [{"!id": 34, "!label": "VPVFR", "children": []}, {"!id": 35, "!label": "FYWTG", "children": [{"!id": 36, "!label": "LIXABWO", "children": []}, {"!id": 37, "!label": "UXVSKU", "children": []}]}, {"!id": 38, "!label": "IGMQOU", "children": []}, {"!id": 39, "!label": "AYVYJFD", "children": []}]}, {"!id": 40, "!label": "FSLUSI", "children": [{"!id": 41, "!label": "CTIPU", "children": []}, {"!id": 42, "!label": "IFBPOK", "children": []}, {"!id": 43, "!label": "GXHED", "children": []}]}]}, {"!id": 44, "!label": "ROVXSIX", "children": []}]}, {"!id": 45, "!label": "JFYHTY", "children": [{"!id": 46, "!label": "FNXPF", "children": []}, {"!id": 47, "!label": "BJHIW", "children": [{"!id": 48, "!label": "KLSPM", "children": [{"!id": 49, "!label": "YCWAQUO", "children": []}, {"!id": 50, "!label": "BGMKQ", "children": []}, {"!id": 51, "!label": "DTUKC", "children": []}]}, {"!id": 52, "!label": "DCVVAT", "children": [{"!id": 53, "!label": "QNPRXPM", "children": []}]}]}, {"!id": 54, "!label": "MQCJWL", "children": []}, {"!id": 55, "!label": "DDAODHU", "children": [{"!id": 56, "!label": "HISUVA", "children": []}, {"!id": 57, "!label": "RJPSDL", "children": []}, {"!id": 58, "!label": "WNEER", "children": [{"!id": 59, "!label": "TGUKSLX", "children": []}, {"!id": 60, "!label": "RQIRAQ", "children": []}, {"!id": 61, "!label": "EUUMRN", "children": []}]}]}]}]}, {"!id": 62, "!label": "KEHDG", "children": [{"!id": 63, "!label": "VIEXV", "children": [{"!id": 64, "!label": "YAKNDF", "children": [{"!id": 65, "!label": "YFHFOX", "children": [{"!id": 66, "!label": "VUXYYK", "children": []}, {"!id": 67, "!label": "LHPWHF", "children": []}, {"!id": 68, "!label": "UADSABQ", "children": []}]}, {"!id": 69, "!label": "AMKMJU", "children": [{"!id": 70, "!label": "MGRLUL", "children": [{"!id": 71, "!label": "YXMBS", "children": []}, {"!id": 72, "!label": "MNDRJ", "children": []}, {"!id": 73, "!label": "KARYO", "children": []}]}, {"!id": 74, "!label": "IUISK", "children": []}]}]}]}]}]}, {"!id": 75, "!label": "AITRES", "children": []}]}, {"!id": 76, "!label": "KRVHCNN", "children": []}, {"!id": 77, "!label": "CGKDU", "children": []}, {"!id": 78, "!label": "GVIVKOB", "children": [{"!id": 79, "!label": "WBVHPP", "children": [{"!id": 80, "!label": "QXQRYH", "children": []}]}, {"!id": 81, "!label": "ULRATN", "children": [{"!id": 82, "!label": "LOFIYY", "children": [{"!id": 83, "!label": "TEXDP", "children": [{"!id": 84, "!label": "MIAMSK", "children": [{"!id": 85, "!label": "JTSPC", "children": []}, {"!id": 86, "!label": "HXDGOG", "children": [{"!id": 87, "!label": "APFOIV", "children": []}, {"!id": 88, "!label": "HUYWBIR", "children": []}, {"!id": 89, "!label": "ENURA", "children": []}]}]}, {"!id": 90, "!label": "GCVALAD", "children": [{"!id": 91, "!label": "RCBUTSF", "children": []}, {"!id": 92, "!label": "QWGYC", "children": []}]}, {"!id": 93, "!label": "PWUUOY", "children": []}, {"!id": 94, "!label": "PCFVLWB", "children": [{"!id": 95, "!label": "CNEWTY", "children": []}, {"!id": 96, "!label": "QRWCTTS", "children": []}]}]}, {"!id": 97, "!label": "VXNLVXX", "children": [{"!id": 98, "!label": "KTEGEWP", "children": []}, {"!id": 99, "!label": "UAKVX", "children": []}, {"!id": 100, "!label": "LXFIFLU", "children": []}, {"!id": 101, "!label": "JQXSSWW", "children": [{"!id": 102, "!label": "UDVHFWL", "children": [{"!id": 103, "!label": "XCIIE", "children": [{"!id": 104, "!label": "EITPGBF", "children": []}]}]}, {"!id": 105, "!label": "JVKVYQC", "children": [{"!id": 106, "!label": "JBEVUE", "children": [{"!id": 107, "!label": "PXRLPXA", "children": []}, {"!id": 108, "!label": "RHDBAD", "children": []}]}]}]}]}, {"!id": 109, "!label": "ROGOVC", "children": [{"!id": 110, "!label": "OASTQ", "children": [{"!id": 111, "!label": "KNYXAT", "children": []}, {"!id": 112, "!label": "SRLBSF", "children": []}, {"!id": 113, "!label": "MYLYSN", "children": []}, {"!id": 114, "!label": "VUWBH", "children": [{"!id": 115, "!label": "PUSCG", "children": [{"!id": 116, "!label": "AXALX", "children": []}, {"!id": 117, "!label": "NBQFNDG", "children": []}]}]}]}, {"!id": 118, "!label": "GDRNYW", "children": []}, {"!id": 119, "!label": "XDLWVQ", "children": [{"!id": 120, "!label": "EWWQNO", "children": []}]}, {"!id": 121, "!label": "UQGNRA", "children": [{"!id": 122, "!label": "HJOLR", "children": [{"!id": 123, "!label": "DVAXQEX", "children": []}, {"!id": 124, "!label": "VPVWWX", "children": []}, {"!id": 125, "!label": "CPTFYSC", "children": []}]}, {"!id": 126, "!label": "VLSFJN", "children": [{"!id": 127, "!label": "WPEOH", "children": [{"!id": 128, "!label": "JBKPO", "children": []}]}, {"!id": 129, "!label": "FDJLOLA", "children": []}]}, {"!id": 130, "!label": "SXNJXC", "children": [{"!id": 131, "!label": "YMWEKDA", "children": []}]}, {"!id": 132, "!label": "HQEVF", "children": [{"!id": 133, "!label": "LIMFFM", "children": []}, {"!id": 134, "!label": "MFPLQBJ", "children": []}, {"!id": 135, "!label": "YAEQP", "children": [{"!id": 136, "!label": "WNGXN", "children": []}, {"!id": 137, "!label": "BMEOFRL", "children": []}, {"!id": 138, "!label": "IXKWR", "children": []}]}]}]}]}]}, {"!id": 139, "!label": "AMCBTVV", "children": [{"!id": 140, "!label": "RRWOI", "children": [{"!id": 141, "!label": "YDCBXC", "children": [{"!id": 142, "!label": "MRBUR", "children": []}, {"!id": 143, "!label": "KGFIGJH", "children": []}, {"!id": 144, "!label": "BMUHX", "children": []}]}]}]}, {"!id": 145, "!label": "SQAMNH", "children": [{"!id": 146, "!label": "SBQFMV", "children": [{"!id": 147, "!label": "KSAKNAW", "children": [{"!id": 148, "!label": "VPEFWCC", "children": []}, {"!id": 149, "!label": "GXUSGB", "children": [{"!id": 150, "!label": "NXLBG", "children": [{"!id": 151, "!label": "UEABSIL", "children": [{"!id": 152, "!label": "OOUVLEU", "children": []}]}, {"!id": 153, "!label": "JKCSJY", "children": []}, {"!id": 154, "!label": "BXKUVBR", "children": []}]}, {"!id": 155, "!label": "SIVJEW", "children": [{"!id": 156, "!label": "HVMFE", "children": []}, {"!id": 157, "!label": "AXGJR", "children": []}, {"!id": 158, "!label": "QYARSF", "children": [{"!id": 159, "!label": "IOGHS", "children": []}]}, {"!id": 160, "!label": "UGGSH", "children": []}]}, {"!id": 161, "!label": "UPDYSCF", "children": [{"!id": 162, "!label": "HRNCDE", "children": []}]}]}, {"!id": 163, "!label": "EPMUGD", "children": [{"!id": 164, "!label": "NQYNB", "children": []}, {"!id": 165, "!label": "KXXUQPU", "children": []}, {"!id": 166, "!label": "KIOPYRE", "children": []}, {"!id": 167, "!label": "PAFOBD", "children": []}]}]}, {"!id": 168, "!label": "NHLMX", "children": [{"!id": 169, "!label": "GYBYTK", "children": []}, {"!id": 170, "!label": "MLYGPAU", "children": [{"!id": 171, "!label": "XNJFJQO", "children": [{"!id": 172, "!label": "GYTRXX", "children": [{"!id": 173, "!label": "TLBCAF", "children": []}]}, {"!id": 174, "!label": "OOKVHDB", "children": [{"!id": 175, "!label": "IUROT", "children": []}, {"!id": 176, "!label": "JDKIL", "children": []}, {"!id": 177, "!label": "OAERT", "children": []}]}]}, {"!id": 178, "!label": "JXPMXXW", "children": []}, {"!id": 179, "!label": "MIVSG", "children": []}]}, {"!id": 180, "!label": "YWWDF", "children": []}]}, {"!id": 181, "!label": "AOEUMYX", "children": []}, {"!id": 182, "!label": "DWKASC", "children": []}]}, {"!id": 183, "!label": "KILFOM", "children": []}, {"!id": 184, "!label": "MHBRRVQ", "children": [{"!id": 185, "!label": "XDDHSBQ", "children": []}, {"!id": 186, "!label": "LWNOW", "children": []}, {"!id": 187, "!label": "LUGQFJ", "children": []}]}, {"!id": 188, "!label": "VSPGSK", "children": [{"!id": 189, "!label": "TBCBR", "children": []}]}]}]}, {"!id": 190, "!label": "WRYEKOU", "children": [{"!id": 191, "!label": "JMXNU", "children": [{"!id": 192, "!label": "YEEHW", "children": [{"!id": 193, "!label": "QQNDHIB", "children": [{"!id": 194, "!label": "KNSBCI", "children": []}, {"!id": 195, "!label": "WKMDGJ", "children": [{"!id": 196, "!label": "HJCOG", "children": []}, {"!id": 197, "!label": "YCOCEA", "children": []}, {"!id": 198, "!label": "JUTAOHV", "children": []}]}, {"!id": 199, "!label": "COVPE", "children": [{"!id": 200, "!label": "QOCMOGU", "children": []}, {"!id": 201, "!label": "NTEKUOT", "children": []}, {"!id": 202, "!label": "EOTMS", "children": [{"!id": 203, "!label": "DMVMY", "children": [{"!id": 204, "!label": "QELTYJU", "children": []}, {"!id": 205, "!label": "XKEBAK", "children": []}]}, {"!id": 206, "!label": "JCQNGBO", "children": [{"!id": 207, "!label": "YWHUQ", "children": []}]}, {"!id": 208, "!label": "FCHDRWR", "children": []}]}]}]}]}, {"!id": 209, "!label": "APNIBNS", "children": [{"!id": 210, "!label": "MMXIBE", "children": [{"!id": 211, "!label": "VBWATC", "children": []}, {"!id": 212, "!label": "RPGFCE", "children": [{"!id": 213, "!label": "EONQQ", "children": []}, {"!id": 214, "!label": "YRKIDE", "children": []}, {"!id": 215, "!label": "XCYCAQD", "children": []}]}, {"!id": 216, "!label": "FLLRJG", "children": [{"!id": 217, "!label": "JHGDMW", "children": []}, {"!id": 218, "!label": "QXBARW", "children": []}]}, {"!id": 219, "!label": "WVRQLR", "children": []}]}]}]}]}]}]}], "styles": [], "edges": [], "links": [], "label_keys": [], "payload_objects": []}`
//const _node_data = `{"nodes": [{"!id": 0, "!label": "YWYJI", "children": [{"!id": 1, "!label": "QTPBKWD", "children": [{"!id": 2, "!label": "JOWUH", "children": [{"!id": 3, "!label": "DWOYHEP", "children": [{"!id": 4, "!label": "CFIPKBF", "children": [{"!id": 5, "!label": "YXBJAIN", "children": [{"!id": 6, "!label": "GFJFNYX", "children": [{"!id": 7, "!label": "NBCSNI", "children": []}, {"!id": 8, "!label": "ALAWAWA", "children": [{"!id": 9, "!label": "YLMPCGD", "children": []}, {"!id": 10, "!label": "NEXRMM", "children": []}, {"!id": 11, "!label": "VGLAK", "children": []}]}]}]}, {"!id": 12, "!label": "ORMOGU", "children": []}, {"!id": 13, "!label": "IRYENPN", "children": [{"!id": 14, "!label": "NKHAG", "children": []}, {"!id": 15, "!label": "FDVKXW", "children": []}, {"!id": 16, "!label": "UFRLO", "children": [{"!id": 17, "!label": "CCBCF", "children": [{"!id": 18, "!label": "COJBP", "children": []}, {"!id": 19, "!label": "JYXVR", "children": []}]}, {"!id": 20, "!label": "TDYHLEE", "children": []}, {"!id": 21, "!label": "GVSOVY", "children": []}]}]}, {"!id": 22, "!label": "CUVTOIA", "children": [{"!id": 23, "!label": "UXLUL", "children": []}, {"!id": 24, "!label": "IPUPU", "children": []}, {"!id": 25, "!label": "IPPIXG", "children": [{"!id": 26, "!label": "HTFREL", "children": []}]}]}]}, {"!id": 27, "!label": "HEJBYUH", "children": [{"!id": 28, "!label": "OWGKL", "children": [{"!id": 29, "!label": "UIYGEO", "children": []}, {"!id": 30, "!label": "HCTQLIY", "children": [{"!id": 31, "!label": "KNOHDH", "children": []}, {"!id": 32, "!label": "TCFVX", "children": []}, {"!id": 33, "!label": "TAGCPN", "children": []}, {"!id": 34, "!label": "PJKOEEF", "children": []}]}, {"!id": 35, "!label": "KUESYJB", "children": []}, {"!id": 36, "!label": "MOHRDH", "children": []}]}, {"!id": 37, "!label": "KQRPPY", "children": []}, {"!id": 38, "!label": "GUDXCT", "children": [{"!id": 39, "!label": "KTOFKXD", "children": []}]}]}, {"!id": 40, "!label": "PIOIPW", "children": []}]}, {"!id": 41, "!label": "XTVOD", "children": [{"!id": 42, "!label": "ELJDIE", "children": []}, {"!id": 43, "!label": "PAPUJL", "children": [{"!id": 44, "!label": "WKYFME", "children": [{"!id": 45, "!label": "FUBWF", "children": []}]}, {"!id": 46, "!label": "BMOHBGT", "children": [{"!id": 47, "!label": "BNYARXB", "children": []}, {"!id": 48, "!label": "DILJGP", "children": [{"!id": 49, "!label": "NDSOVKT", "children": [{"!id": 50, "!label": "RGXNWCC", "children": [{"!id": 51, "!label": "YULBJUV", "children": [{"!id": 52, "!label": "WWFDR", "children": [{"!id": 53, "!label": "MSYAHNO", "children": []}, {"!id": 54, "!label": "XCTIIBB", "children": []}, {"!id": 55, "!label": "XERPDO", "children": []}, {"!id": 56, "!label": "TWAJU", "children": []}]}, {"!id": 57, "!label": "KDYLPQ", "children": []}, {"!id": 58, "!label": "IQBCYH", "children": []}]}]}]}]}, {"!id": 59, "!label": "OAKBNT", "children": [{"!id": 60, "!label": "WCMFAVU", "children": []}]}, {"!id": 61, "!label": "UMTYC", "children": []}]}, {"!id": 62, "!label": "LXPTXD", "children": [{"!id": 63, "!label": "OJJGDE", "children": []}]}]}, {"!id": 64, "!label": "LDRFQHV", "children": [{"!id": 65, "!label": "UDITF", "children": [{"!id": 66, "!label": "CCBIP", "children": []}]}, {"!id": 67, "!label": "BJJWXT", "children": [{"!id": 68, "!label": "QNJYHQN", "children": [{"!id": 69, "!label": "BUHULM", "children": [{"!id": 70, "!label": "UXYCFS", "children": []}, {"!id": 71, "!label": "YJQMQ", "children": []}]}, {"!id": 72, "!label": "KOEGTX", "children": []}]}, {"!id": 73, "!label": "USPYE", "children": [{"!id": 74, "!label": "FQFWFCY", "children": [{"!id": 75, "!label": "HTIDCV", "children": []}, {"!id": 76, "!label": "OFMYB", "children": []}, {"!id": 77, "!label": "LFVPP", "children": []}, {"!id": 78, "!label": "BHPAL", "children": [{"!id": 79, "!label": "GLQSCIY", "children": [{"!id": 80, "!label": "WJTKQIW", "children": []}, {"!id": 81, "!label": "YUJJAN", "children": []}, {"!id": 82, "!label": "AYGUPPD", "children": []}, {"!id": 83, "!label": "HYTVV", "children": []}]}, {"!id": 84, "!label": "MMRMWY", "children": []}, {"!id": 85, "!label": "XTGYJF", "children": []}]}]}, {"!id": 86, "!label": "WCQBQ", "children": []}, {"!id": 87, "!label": "CDSLX", "children": []}]}]}, {"!id": 88, "!label": "VMGBRQE", "children": []}, {"!id": 89, "!label": "QBHEM", "children": [{"!id": 90, "!label": "DFVDYO", "children": [{"!id": 91, "!label": "UHVMWN", "children": []}, {"!id": 92, "!label": "DTYEY", "children": []}, {"!id": 93, "!label": "MQHDGA", "children": []}]}, {"!id": 94, "!label": "AMVOC", "children": [{"!id": 95, "!label": "FDDSO", "children": []}, {"!id": 96, "!label": "PIBSROY", "children": [{"!id": 97, "!label": "IFQABT", "children": []}, {"!id": 98, "!label": "WSAQFVP", "children": []}, {"!id": 99, "!label": "RSKPJ", "children": [{"!id": 100, "!label": "NHHEE", "children": []}, {"!id": 101, "!label": "UQCXSB", "children": [{"!id": 102, "!label": "MYKUDNH", "children": []}]}, {"!id": 103, "!label": "MCTSWPY", "children": [{"!id": 104, "!label": "JIPPQM", "children": []}, {"!id": 105, "!label": "GKMNLIT", "children": []}, {"!id": 106, "!label": "JGKLJ", "children": []}]}]}, {"!id": 107, "!label": "KPWVX", "children": [{"!id": 108, "!label": "HQVST", "children": [{"!id": 109, "!label": "SNAKP", "children": []}, {"!id": 110, "!label": "IBSVUVQ", "children": [{"!id": 111, "!label": "TIRJIN", "children": []}]}]}]}]}, {"!id": 112, "!label": "GLHSPDY", "children": []}, {"!id": 113, "!label": "UPIWF", "children": [{"!id": 114, "!label": "BGANOK", "children": [{"!id": 115, "!label": "EBONJR", "children": []}]}, {"!id": 116, "!label": "XUPHUY", "children": []}, {"!id": 117, "!label": "SJUUYVM", "children": []}, {"!id": 118, "!label": "WAVPGH", "children": [{"!id": 119, "!label": "NTMEULL", "children": []}, {"!id": 120, "!label": "CQCSTVS", "children": [{"!id": 121, "!label": "NASFXJP", "children": []}, {"!id": 122, "!label": "YQARVO", "children": []}]}]}]}]}, {"!id": 123, "!label": "GBYJU", "children": [{"!id": 124, "!label": "QBHUNY", "children": []}, {"!id": 125, "!label": "PRLMPF", "children": []}, {"!id": 126, "!label": "HIFESBQ", "children": [{"!id": 127, "!label": "XTFFCP", "children": []}, {"!id": 128, "!label": "JUJCHK", "children": [{"!id": 129, "!label": "GUPSDL", "children": []}, {"!id": 130, "!label": "QYYNFS", "children": []}]}, {"!id": 131, "!label": "PXRPHR", "children": []}]}, {"!id": 132, "!label": "TIJYRY", "children": []}]}]}]}, {"!id": 133, "!label": "PJQJJOC", "children": [{"!id": 134, "!label": "QXULP", "children": []}]}]}, {"!id": 135, "!label": "INIIKD", "children": [{"!id": 136, "!label": "ODKHKQI", "children": [{"!id": 137, "!label": "QBNAS", "children": [{"!id": 138, "!label": "OGENI", "children": [{"!id": 139, "!label": "HOSSGP", "children": []}, {"!id": 140, "!label": "MBJXG", "children": [{"!id": 141, "!label": "UTYQG", "children": [{"!id": 142, "!label": "FXMNW", "children": []}, {"!id": 143, "!label": "VVLOB", "children": [{"!id": 144, "!label": "BOKNDIL", "children": []}, {"!id": 145, "!label": "DUDTRIW", "children": []}, {"!id": 146, "!label": "YFXEM", "children": []}]}]}, {"!id": 147, "!label": "IHDAYWU", "children": []}]}, {"!id": 148, "!label": "BVEGC", "children": []}, {"!id": 149, "!label": "RSPIW", "children": []}]}, {"!id": 150, "!label": "JRFQUI", "children": []}, {"!id": 151, "!label": "JLBAY", "children": []}, {"!id": 152, "!label": "IQKSXS", "children": [{"!id": 153, "!label": "RRNBO", "children": [{"!id": 154, "!label": "RXNTIJW", "children": []}, {"!id": 155, "!label": "WJPOPS", "children": []}, {"!id": 156, "!label": "MKCTWT", "children": []}, {"!id": 157, "!label": "OKIYPQJ", "children": []}]}, {"!id": 158, "!label": "XMGQD", "children": [{"!id": 159, "!label": "IHSOMGQ", "children": []}, {"!id": 160, "!label": "PPRPFL", "children": [{"!id": 161, "!label": "EYLIRGX", "children": []}, {"!id": 162, "!label": "KGWTYUY", "children": []}, {"!id": 163, "!label": "OBSQL", "children": []}]}, {"!id": 164, "!label": "FOJFDKC", "children": [{"!id": 165, "!label": "YNDHD", "children": []}, {"!id": 166, "!label": "PRTUS", "children": []}, {"!id": 167, "!label": "AYJJA", "children": [{"!id": 168, "!label": "PHBYCTG", "children": []}, {"!id": 169, "!label": "QRUBRX", "children": []}, {"!id": 170, "!label": "BQVBK", "children": [{"!id": 171, "!label": "CKRWS", "children": []}, {"!id": 172, "!label": "SRHITWC", "children": []}]}, {"!id": 173, "!label": "UVRDU", "children": []}]}]}, {"!id": 174, "!label": "FIRJP", "children": []}]}, {"!id": 175, "!label": "TBQXGU", "children": []}]}]}, {"!id": 176, "!label": "QECNRRE", "children": [{"!id": 177, "!label": "RFBXG", "children": [{"!id": 178, "!label": "NMCJF", "children": []}, {"!id": 179, "!label": "NFARD", "children": []}, {"!id": 180, "!label": "YJPNH", "children": []}]}, {"!id": 181, "!label": "ACYKLHI", "children": [{"!id": 182, "!label": "IXXPD", "children": []}, {"!id": 183, "!label": "HWOYE", "children": []}, {"!id": 184, "!label": "BYXGVA", "children": [{"!id": 185, "!label": "GIXPD", "children": []}]}, {"!id": 186, "!label": "UOMWSN", "children": []}]}, {"!id": 187, "!label": "QCAJQ", "children": [{"!id": 188, "!label": "LKSTTAN", "children": [{"!id": 189, "!label": "OXKSMDF", "children": []}, {"!id": 190, "!label": "CVCTG", "children": []}, {"!id": 191, "!label": "HFVEVO", "children": []}, {"!id": 192, "!label": "KUPSWA", "children": []}]}, {"!id": 193, "!label": "UATCR", "children": []}]}]}, {"!id": 194, "!label": "RBPJP", "children": [{"!id": 195, "!label": "MVMMOH", "children": [{"!id": 196, "!label": "KYVEI", "children": []}]}, {"!id": 197, "!label": "TBWRV", "children": []}, {"!id": 198, "!label": "PPNLGY", "children": [{"!id": 199, "!label": "OVHWM", "children": [{"!id": 200, "!label": "GKTDSK", "children": []}, {"!id": 201, "!label": "XJCLEFY", "children": []}]}, {"!id": 202, "!label": "UIBYLM", "children": []}, {"!id": 203, "!label": "DUNBCY", "children": []}, {"!id": 204, "!label": "JKARO", "children": [{"!id": 205, "!label": "TFTVB", "children": [{"!id": 206, "!label": "YYANTW", "children": []}]}, {"!id": 207, "!label": "JWVFSQ", "children": []}]}]}, {"!id": 208, "!label": "RFVKXI", "children": [{"!id": 209, "!label": "JLFJPM", "children": [{"!id": 210, "!label": "TYANKPG", "children": []}, {"!id": 211, "!label": "EHBDE", "children": []}, {"!id": 212, "!label": "MAENY", "children": []}, {"!id": 213, "!label": "PLPCC", "children": [{"!id": 214, "!label": "GCBYWFL", "children": []}]}]}, {"!id": 215, "!label": "KDYCDUA", "children": []}]}]}, {"!id": 216, "!label": "XIHPKI", "children": []}]}, {"!id": 217, "!label": "IAMXO", "children": []}]}, {"!id": 218, "!label": "FNMUC", "children": [{"!id": 219, "!label": "IHLRAML", "children": []}, {"!id": 220, "!label": "KFHDI", "children": []}, {"!id": 221, "!label": "AXKCD", "children": [{"!id": 222, "!label": "QFNXL", "children": [{"!id": 223, "!label": "FMUJMN", "children": []}, {"!id": 224, "!label": "DTDUUBT", "children": []}, {"!id": 225, "!label": "SSHNOB", "children": []}, {"!id": 226, "!label": "ABXKNFK", "children": []}]}, {"!id": 227, "!label": "HACGFN", "children": [{"!id": 228, "!label": "LWAID", "children": [{"!id": 229, "!label": "IGVJJLQ", "children": []}, {"!id": 230, "!label": "KHDQN", "children": []}]}, {"!id": 231, "!label": "BVGQVMA", "children": [{"!id": 232, "!label": "IXHAN", "children": [{"!id": 233, "!label": "IHGVBXJ", "children": [{"!id": 234, "!label": "QJKAF", "children": []}, {"!id": 235, "!label": "QBLFNO", "children": []}, {"!id": 236, "!label": "PQKGU", "children": []}]}, {"!id": 237, "!label": "DDEKKSO", "children": []}]}]}]}, {"!id": 238, "!label": "JTEQK", "children": [{"!id": 239, "!label": "QOWSC", "children": [{"!id": 240, "!label": "GFKEH", "children": []}]}]}]}, {"!id": 241, "!label": "SMPQL", "children": []}]}]}, {"!id": 242, "!label": "BFKOYX", "children": []}, {"!id": 243, "!label": "YABLOK", "children": [{"!id": 244, "!label": "NYLNL", "children": [{"!id": 245, "!label": "MQVTCP", "children": [{"!id": 246, "!label": "KEBLIH", "children": [{"!id": 247, "!label": "RMOQLS", "children": [{"!id": 248, "!label": "TOAXL", "children": []}, {"!id": 249, "!label": "TDSQPAS", "children": []}, {"!id": 250, "!label": "AJUBHD", "children": []}]}]}]}, {"!id": 251, "!label": "CNQHC", "children": [{"!id": 252, "!label": "CEPYVJP", "children": []}, {"!id": 253, "!label": "QLLMQ", "children": []}]}, {"!id": 254, "!label": "VVYYGAI", "children": []}]}]}, {"!id": 255, "!label": "IUMDVD", "children": [{"!id": 256, "!label": "RJSEVU", "children": [{"!id": 257, "!label": "HBBRQ", "children": [{"!id": 258, "!label": "RTABDL", "children": []}, {"!id": 259, "!label": "BGFVTW", "children": []}]}, {"!id": 260, "!label": "XSWTN", "children": [{"!id": 261, "!label": "JIWOI", "children": [{"!id": 262, "!label": "WJDUNE", "children": []}, {"!id": 263, "!label": "GIXCPN", "children": []}, {"!id": 264, "!label": "FXPPSAC", "children": [{"!id": 265, "!label": "NBPKWXE", "children": [{"!id": 266, "!label": "NFODVT", "children": []}, {"!id": 267, "!label": "TGOCC", "children": [{"!id": 268, "!label": "UXKPJG", "children": []}, {"!id": 269, "!label": "NEQWX", "children": []}, {"!id": 270, "!label": "FQVVE", "children": []}]}]}, {"!id": 271, "!label": "IYNBT", "children": []}]}]}, {"!id": 272, "!label": "DRBGN", "children": []}]}, {"!id": 273, "!label": "PDMPNPL", "children": [{"!id": 274, "!label": "QXUFCD", "children": [{"!id": 275, "!label": "PNHKNSV", "children": [{"!id": 276, "!label": "ECLHX", "children": []}, {"!id": 277, "!label": "EYCFA", "children": []}, {"!id": 278, "!label": "HBVUW", "children": [{"!id": 279, "!label": "PQAOWW", "children": []}, {"!id": 280, "!label": "XTVHXCJ", "children": [{"!id": 281, "!label": "KXCGUUI", "children": []}, {"!id": 282, "!label": "OVJAPQN", "children": [{"!id": 283, "!label": "PQOYWC", "children": []}, {"!id": 284, "!label": "DLQQB", "children": []}, {"!id": 285, "!label": "HISYUSM", "children": []}, {"!id": 286, "!label": "XCUUUYA", "children": []}]}, {"!id": 287, "!label": "JEKSVS", "children": [{"!id": 288, "!label": "KOYHQFV", "children": []}, {"!id": 289, "!label": "ECLER", "children": []}, {"!id": 290, "!label": "RNHUQQI", "children": []}]}, {"!id": 291, "!label": "GGTEXX", "children": [{"!id": 292, "!label": "QFESUO", "children": [{"!id": 293, "!label": "JDPYU", "children": []}, {"!id": 294, "!label": "JQCLNQ", "children": []}, {"!id": 295, "!label": "SRBHDQ", "children": []}, {"!id": 296, "!label": "PVHFS", "children": []}]}, {"!id": 297, "!label": "WNLRSHL", "children": []}, {"!id": 298, "!label": "IWYGK", "children": []}, {"!id": 299, "!label": "EPQCAGH", "children": []}]}]}, {"!id": 300, "!label": "THYBYAI", "children": [{"!id": 301, "!label": "HIXLVMR", "children": []}, {"!id": 302, "!label": "DSHMW", "children": []}, {"!id": 303, "!label": "DORBC", "children": []}, {"!id": 304, "!label": "VCTIYML", "children": []}]}]}, {"!id": 305, "!label": "EMYXHQK", "children": []}]}, {"!id": 306, "!label": "XKJOEM", "children": [{"!id": 307, "!label": "TJENDMK", "children": []}]}]}]}]}, {"!id": 308, "!label": "RSMJD", "children": [{"!id": 309, "!label": "UPVRH", "children": []}, {"!id": 310, "!label": "IBBKT", "children": [{"!id": 311, "!label": "PQPQKJ", "children": [{"!id": 312, "!label": "TXFLHRH", "children": [{"!id": 313, "!label": "AYUXQ", "children": [{"!id": 314, "!label": "VGJSTP", "children": []}]}, {"!id": 315, "!label": "CEKYA", "children": []}]}, {"!id": 316, "!label": "BEESWB", "children": [{"!id": 317, "!label": "WXPYIA", "children": []}, {"!id": 318, "!label": "IPIINA", "children": []}]}, {"!id": 319, "!label": "FVHXLP", "children": [{"!id": 320, "!label": "IHOKRQ", "children": [{"!id": 321, "!label": "POJYDT", "children": []}, {"!id": 322, "!label": "PDFCTCX", "children": [{"!id": 323, "!label": "BEOLI", "children": []}, {"!id": 324, "!label": "UOPROYD", "children": []}]}]}, {"!id": 325, "!label": "YXQQX", "children": []}, {"!id": 326, "!label": "GJNRLLH", "children": [{"!id": 327, "!label": "AUTJTLM", "children": []}, {"!id": 328, "!label": "IXDUMSE", "children": []}]}]}, {"!id": 329, "!label": "ORFHMQ", "children": []}]}, {"!id": 330, "!label": "PDRMJEU", "children": [{"!id": 331, "!label": "OTMFXI", "children": [{"!id": 332, "!label": "MXGLKJT", "children": [{"!id": 333, "!label": "TWPAQ", "children": [{"!id": 334, "!label": "EIOJD", "children": []}]}]}, {"!id": 335, "!label": "EKYNS", "children": [{"!id": 336, "!label": "UVNRA", "children": []}, {"!id": 337, "!label": "OHATHDT", "children": []}, {"!id": 338, "!label": "PCAFH", "children": []}]}, {"!id": 339, "!label": "BEAYF", "children": [{"!id": 340, "!label": "JPLOFJ", "children": []}, {"!id": 341, "!label": "HTHLN", "children": []}, {"!id": 342, "!label": "NLJJF", "children": []}, {"!id": 343, "!label": "UJVKYNT", "children": [{"!id": 344, "!label": "RXDST", "children": []}, {"!id": 345, "!label": "BWVYISB", "children": []}]}]}, {"!id": 346, "!label": "LVNGGR", "children": [{"!id": 347, "!label": "PCFMIC", "children": []}, {"!id": 348, "!label": "PSUNMGD", "children": [{"!id": 349, "!label": "PORLKD", "children": []}, {"!id": 350, "!label": "WONVS", "children": []}]}, {"!id": 351, "!label": "LAAMP", "children": [{"!id": 352, "!label": "GYRDL", "children": []}]}]}]}, {"!id": 353, "!label": "VTAKOP", "children": []}, {"!id": 354, "!label": "JFVXNPY", "children": []}, {"!id": 355, "!label": "PRCVSL", "children": [{"!id": 356, "!label": "HIEVMG", "children": [{"!id": 357, "!label": "PQEHBEF", "children": []}, {"!id": 358, "!label": "LSLXO", "children": [{"!id": 359, "!label": "TPRVAE", "children": []}, {"!id": 360, "!label": "JDUNLO", "children": [{"!id": 361, "!label": "FEBNNJ", "children": []}, {"!id": 362, "!label": "IPLMSQO", "children": []}]}, {"!id": 363, "!label": "KWCNY", "children": []}]}, {"!id": 364, "!label": "EYOTOM", "children": []}]}, {"!id": 365, "!label": "QVAAA", "children": []}]}]}]}, {"!id": 366, "!label": "HRGFRVG", "children": [{"!id": 367, "!label": "MORBGLC", "children": []}]}]}]}]}, {"!id": 368, "!label": "OGFMXD", "children": [{"!id": 369, "!label": "RLIWAWW", "children": [{"!id": 370, "!label": "QUMAJEL", "children": [{"!id": 371, "!label": "DDOJIA", "children": [{"!id": 372, "!label": "MKVBUW", "children": [{"!id": 373, "!label": "UYLUDE", "children": []}, {"!id": 374, "!label": "XBKUSR", "children": [{"!id": 375, "!label": "XFSHIA", "children": [{"!id": 376, "!label": "XPUWOWS", "children": []}, {"!id": 377, "!label": "UYGST", "children": [{"!id": 378, "!label": "UMRFFM", "children": []}]}]}, {"!id": 379, "!label": "XRJMKQN", "children": [{"!id": 380, "!label": "DLFTPF", "children": []}, {"!id": 381, "!label": "MTRNHU", "children": []}]}]}]}, {"!id": 382, "!label": "TLCFN", "children": []}, {"!id": 383, "!label": "RSSNEE", "children": []}, {"!id": 384, "!label": "PJBBYME", "children": []}]}]}, {"!id": 385, "!label": "CVGVCD", "children": [{"!id": 386, "!label": "KDUIMI", "children": []}]}, {"!id": 387, "!label": "EHUMU", "children": [{"!id": 388, "!label": "GILXI", "children": [{"!id": 389, "!label": "DLLCBXA", "children": []}]}, {"!id": 390, "!label": "WVYOEPP", "children": [{"!id": 391, "!label": "DNEHHJL", "children": [{"!id": 392, "!label": "BIFCI", "children": [{"!id": 393, "!label": "VWMTDE", "children": []}]}, {"!id": 394, "!label": "XWIQHS", "children": []}, {"!id": 395, "!label": "UVBUHXR", "children": []}, {"!id": 396, "!label": "ALEETGV", "children": []}]}, {"!id": 397, "!label": "SFYPW", "children": [{"!id": 398, "!label": "AOPUP", "children": []}, {"!id": 399, "!label": "CTSEPN", "children": [{"!id": 400, "!label": "RFLEINI", "children": [{"!id": 401, "!label": "WYBDRX", "children": []}]}, {"!id": 402, "!label": "JIUEKD", "children": []}, {"!id": 403, "!label": "YCXQSRF", "children": [{"!id": 404, "!label": "QRXOJGM", "children": []}, {"!id": 405, "!label": "RPFMG", "children": []}, {"!id": 406, "!label": "WMQTNSB", "children": [{"!id": 407, "!label": "QJFVB", "children": []}]}]}]}, {"!id": 408, "!label": "UYSVLB", "children": []}]}, {"!id": 409, "!label": "DNLTY", "children": [{"!id": 410, "!label": "LSVMKXP", "children": []}, {"!id": 411, "!label": "QFIFCYU", "children": []}, {"!id": 412, "!label": "PJCCVWR", "children": [{"!id": 413, "!label": "TEBMRT", "children": []}, {"!id": 414, "!label": "XGGOVGG", "children": []}]}, {"!id": 415, "!label": "UKHEHA", "children": []}]}]}, {"!id": 416, "!label": "JDHFFBX", "children": [{"!id": 417, "!label": "NLVAP", "children": [{"!id": 418, "!label": "TWBRLS", "children": []}]}, {"!id": 419, "!label": "OWWRDCA", "children": [{"!id": 420, "!label": "BFNNP", "children": []}, {"!id": 421, "!label": "NCPFX", "children": []}, {"!id": 422, "!label": "DOWDL", "children": [{"!id": 423, "!label": "MXHGMCQ", "children": [{"!id": 424, "!label": "WIEHD", "children": []}]}, {"!id": 425, "!label": "JDFFQ", "children": []}]}]}]}]}]}, {"!id": 426, "!label": "CEBRRX", "children": [{"!id": 427, "!label": "XOYIG", "children": [{"!id": 428, "!label": "LXKYM", "children": [{"!id": 429, "!label": "FPHWLDQ", "children": []}, {"!id": 430, "!label": "WSMJEW", "children": []}]}, {"!id": 431, "!label": "RDUYADY", "children": [{"!id": 432, "!label": "MWHYG", "children": [{"!id": 433, "!label": "FFPWH", "children": [{"!id": 434, "!label": "FENDYJL", "children": [{"!id": 435, "!label": "ROWXPU", "children": [{"!id": 436, "!label": "KSEASGN", "children": []}, {"!id": 437, "!label": "OORGKSM", "children": []}, {"!id": 438, "!label": "OJBETT", "children": [{"!id": 439, "!label": "YIKUUHC", "children": []}, {"!id": 440, "!label": "QHSKW", "children": []}]}, {"!id": 441, "!label": "AMMATJ", "children": []}]}, {"!id": 442, "!label": "IXHCBB", "children": []}, {"!id": 443, "!label": "TPOCWH", "children": []}, {"!id": 444, "!label": "FQSWR", "children": [{"!id": 445, "!label": "EGIDFHT", "children": []}, {"!id": 446, "!label": "YSBVW", "children": [{"!id": 447, "!label": "IQHGDBL", "children": []}, {"!id": 448, "!label": "IGCUA", "children": []}]}]}]}, {"!id": 449, "!label": "OGJXG", "children": [{"!id": 450, "!label": "LICSTL", "children": []}, {"!id": 451, "!label": "FJNUWO", "children": []}, {"!id": 452, "!label": "TNCUW", "children": []}]}, {"!id": 453, "!label": "SPIOLC", "children": [{"!id": 454, "!label": "FWTHHOO", "children": []}, {"!id": 455, "!label": "QDIFY", "children": []}]}]}, {"!id": 456, "!label": "EYSRC", "children": [{"!id": 457, "!label": "DIGRX", "children": [{"!id": 458, "!label": "VCHIC", "children": []}, {"!id": 459, "!label": "JCMCUM", "children": []}, {"!id": 460, "!label": "MULSU", "children": []}, {"!id": 461, "!label": "AUYSDE", "children": [{"!id": 462, "!label": "UWUIJNW", "children": []}, {"!id": 463, "!label": "PPJGYAM", "children": []}, {"!id": 464, "!label": "BYUMBR", "children": [{"!id": 465, "!label": "VWSLD", "children": []}, {"!id": 466, "!label": "PPEBUNQ", "children": []}]}, {"!id": 467, "!label": "HWBSER", "children": []}]}]}, {"!id": 468, "!label": "UCUVXM", "children": [{"!id": 469, "!label": "FKKFK", "children": [{"!id": 470, "!label": "JUCLAF", "children": []}, {"!id": 471, "!label": "SBRFU", "children": [{"!id": 472, "!label": "DWRQHNG", "children": [{"!id": 473, "!label": "JWBJRRX", "children": []}, {"!id": 474, "!label": "KSOLW", "children": []}]}]}, {"!id": 475, "!label": "TJNJL", "children": []}]}]}, {"!id": 476, "!label": "WQWBIWA", "children": [{"!id": 477, "!label": "IWGBF", "children": []}, {"!id": 478, "!label": "VNAJYUW", "children": []}, {"!id": 479, "!label": "ETTWQM", "children": [{"!id": 480, "!label": "YTDCEL", "children": [{"!id": 481, "!label": "CHKJYMS", "children": []}]}, {"!id": 482, "!label": "XDBFHU", "children": [{"!id": 483, "!label": "SKLPCTW", "children": []}, {"!id": 484, "!label": "YNJGTR", "children": []}, {"!id": 485, "!label": "RIQTN", "children": []}]}]}, {"!id": 486, "!label": "HCLCK", "children": []}]}]}]}, {"!id": 487, "!label": "CAIPGAO", "children": []}, {"!id": 488, "!label": "CBFPATT", "children": []}]}, {"!id": 489, "!label": "CXLYXLX", "children": [{"!id": 490, "!label": "GMNTE", "children": [{"!id": 491, "!label": "WAFRRY", "children": [{"!id": 492, "!label": "TNGSP", "children": []}, {"!id": 493, "!label": "WTRTPVK", "children": [{"!id": 494, "!label": "BOONA", "children": []}, {"!id": 495, "!label": "JKXAA", "children": []}, {"!id": 496, "!label": "KDCORH", "children": []}, {"!id": 497, "!label": "YFBMDCV", "children": []}]}, {"!id": 498, "!label": "EXQRQN", "children": []}, {"!id": 499, "!label": "ORPNDV", "children": [{"!id": 500, "!label": "SINJW", "children": []}, {"!id": 501, "!label": "GTWIK", "children": []}, {"!id": 502, "!label": "PNSOAE", "children": []}]}]}]}, {"!id": 503, "!label": "TPHIC", "children": [{"!id": 504, "!label": "POQIK", "children": []}, {"!id": 505, "!label": "RTMIIU", "children": [{"!id": 506, "!label": "FVKTXUW", "children": []}, {"!id": 507, "!label": "JJKGXFF", "children": []}, {"!id": 508, "!label": "QXTAT", "children": [{"!id": 509, "!label": "UEIHER", "children": []}, {"!id": 510, "!label": "AXQNWJ", "children": []}, {"!id": 511, "!label": "IORPNH", "children": []}]}, {"!id": 512, "!label": "ELFMMV", "children": [{"!id": 513, "!label": "VIKGDB", "children": []}, {"!id": 514, "!label": "KBOLVQU", "children": []}]}]}, {"!id": 515, "!label": "CWDYK", "children": []}, {"!id": 516, "!label": "OALUEQ", "children": [{"!id": 517, "!label": "RGLSGX", "children": [{"!id": 518, "!label": "ETKNW", "children": []}, {"!id": 519, "!label": "LDIDKC", "children": []}, {"!id": 520, "!label": "KOLUY", "children": [{"!id": 521, "!label": "RLQXXVU", "children": []}]}, {"!id": 522, "!label": "GUWVWH", "children": []}]}, {"!id": 523, "!label": "UEOTSB", "children": [{"!id": 524, "!label": "MYSTB", "children": [{"!id": 525, "!label": "BCLBTI", "children": []}, {"!id": 526, "!label": "LBMKRCA", "children": []}, {"!id": 527, "!label": "EAJEM", "children": []}, {"!id": 528, "!label": "CDPPQ", "children": []}]}, {"!id": 529, "!label": "FEQGJE", "children": [{"!id": 530, "!label": "RDXBQXS", "children": []}]}]}]}]}, {"!id": 531, "!label": "HPMIHFG", "children": [{"!id": 532, "!label": "DDRPX", "children": []}, {"!id": 533, "!label": "VKPHL", "children": [{"!id": 534, "!label": "JNYNM", "children": [{"!id": 535, "!label": "HIMNHM", "children": []}, {"!id": 536, "!label": "GKNVRDB", "children": []}, {"!id": 537, "!label": "BOXGCS", "children": []}, {"!id": 538, "!label": "VPNYUFO", "children": []}]}, {"!id": 539, "!label": "DPOIRHL", "children": []}]}, {"!id": 540, "!label": "GANIQ", "children": []}, {"!id": 541, "!label": "QPIVT", "children": []}]}, {"!id": 542, "!label": "RCLRYT", "children": []}]}, {"!id": 543, "!label": "WRROM", "children": [{"!id": 544, "!label": "MEHBE", "children": []}, {"!id": 545, "!label": "TQMWQ", "children": []}]}]}, {"!id": 546, "!label": "OEHSMHK", "children": []}]}, {"!id": 547, "!label": "SCVFKRG", "children": [{"!id": 548, "!label": "UQINFH", "children": [{"!id": 549, "!label": "HAACTU", "children": [{"!id": 550, "!label": "SFPGPLA", "children": [{"!id": 551, "!label": "QQWML", "children": [{"!id": 552, "!label": "COGVGCE", "children": []}]}, {"!id": 553, "!label": "YNTXA", "children": [{"!id": 554, "!label": "DDUWF", "children": []}, {"!id": 555, "!label": "FGOVIT", "children": []}]}, {"!id": 556, "!label": "IXILNS", "children": [{"!id": 557, "!label": "CJXUP", "children": []}, {"!id": 558, "!label": "NUSHBQJ", "children": [{"!id": 559, "!label": "QICKB", "children": []}]}]}]}, {"!id": 560, "!label": "WBAQPM", "children": [{"!id": 561, "!label": "IWGFQ", "children": [{"!id": 562, "!label": "EIUCYV", "children": []}]}, {"!id": 563, "!label": "DKPJPWR", "children": []}, {"!id": 564, "!label": "YXJCI", "children": []}]}, {"!id": 565, "!label": "RAYWLJD", "children": [{"!id": 566, "!label": "YIVWLTP", "children": []}, {"!id": 567, "!label": "WOJHU", "children": []}, {"!id": 568, "!label": "IEGBSX", "children": [{"!id": 569, "!label": "PNEPB", "children": [{"!id": 570, "!label": "XISXOSB", "children": []}, {"!id": 571, "!label": "TOAGEE", "children": []}]}, {"!id": 572, "!label": "GFYVBGN", "children": [{"!id": 573, "!label": "NJWABB", "children": [{"!id": 574, "!label": "QJQYVIF", "children": [{"!id": 575, "!label": "HPJKUDI", "children": []}, {"!id": 576, "!label": "OFBLKIM", "children": []}]}, {"!id": 577, "!label": "NAFNV", "children": []}, {"!id": 578, "!label": "HDMHW", "children": []}, {"!id": 579, "!label": "QEEPHTC", "children": [{"!id": 580, "!label": "COTQD", "children": []}, {"!id": 581, "!label": "YMWVBBS", "children": []}, {"!id": 582, "!label": "WINJAER", "children": []}]}]}, {"!id": 583, "!label": "FRJTALJ", "children": [{"!id": 584, "!label": "NQKKSTB", "children": []}, {"!id": 585, "!label": "UDQOH", "children": []}]}]}, {"!id": 586, "!label": "TJMCVK", "children": [{"!id": 587, "!label": "GJBDTF", "children": [{"!id": 588, "!label": "LNTWD", "children": []}]}, {"!id": 589, "!label": "TCURQ", "children": [{"!id": 590, "!label": "FLKQJDF", "children": [{"!id": 591, "!label": "NRVMH", "children": []}, {"!id": 592, "!label": "DSWFGFD", "children": []}, {"!id": 593, "!label": "EHMER", "children": []}]}]}]}]}, {"!id": 594, "!label": "EDLKYF", "children": [{"!id": 595, "!label": "FBYKD", "children": [{"!id": 596, "!label": "MWLQA", "children": []}, {"!id": 597, "!label": "RJHDRAE", "children": []}]}, {"!id": 598, "!label": "YMSUJA", "children": [{"!id": 599, "!label": "GSUVM", "children": []}]}]}]}]}]}]}]}]}], "styles": [], "edges": [], "links": [], "label_keys": [], "payload_objects": []}`

const example_node_data = `{
    "nodes" : [
        {
            "!id" : 0,
            "1" : {"!id" : 1},
            "2" : {
                "!id" : 2,
                "big" : {"!label" : "hairy hippopotamus"}
            },
            "3" : {"!id" : 3}
        }
    ],
    "links" : [],
    "styles" : {}
}`