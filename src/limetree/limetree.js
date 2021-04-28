"use strict";


const RANK_SEPARATION = 80.0;
const BOX_W_MARGIN = 4;
const W_SEPARATION = 20;

var _next_node_id = 999;
var _all_nodes = {};
var _rank_lists = new Array();

var g_pan_x = -500;
var g_pan_y = -50;
var g_scale = 1.0;

var rank_list = function(rank) {
    let slen = _rank_lists.length;
    for (let i = 0; i <= (rank - slen); i++) {
        _rank_lists.push(new Array());
    }
    return _rank_lists[rank];
}

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

class LiveNode {
    constructor(o, rank) {
        // Payload, general tree pointers, and style information.
        this.parent = null;
        this.rank = rank;
        this.rankorder = 0;
        this.payload = {};
        this.children = new Array();
        this.pos_x = -1;
        this.pos_y = RANK_SEPARATION * this.rank;
        this.boxwidth = 100;
        this.sib_index = -1;

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

        let rl = rank_list(this.rank); 
        this.rankorder = rl.length
        rl.push(this);

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

                if (k[0] !== '@' && o[k] instanceof Object) {
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
        this.x = 0.0; //layout position, copied over to pos_x when ready.
        this.thread = null;
        this.mod = 0.0;
        this.ancestor = this;
        this.change = 0.0;
        this.shift = 0.0;
        this.lefmost_sibling = this;
    }

    add_child(edge_name, c) {
        let childIndex = this.children.length;
        c.childIndex = childIndex;
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

    right_side() {
        return this.pos_x + this.boxwidth;
    }

    left_side() {
        return this.pos_x;
    }

    layout_left_side() {
        return this.x;
    }

    layout_right_side() {
        return this.x + this.boxwidth;
    }

    child(index) {
        if (index >= this.children.length) {
            return null;
        }
        else if (index < 0) {
            index = this.children.length + index;
        }

        return this.children[index].target;
    }

    count() {
        return this.children.length;
    }

    leaf() {
        if (this.children.length) { return false; }
        return false;
    }

    next_left() {
        if (this.children.length > 0) {
            return this.child(0);
        }
        else {
            return this.thread;
        }
    }

    left() {
        if (!this.parent || this.sib_index < 1) { return null; }

        return this.parent.child(this.sib_index - 1);
    }

    leftmost_sib() {
        if (!this.parent || this.sib_index == 0) { return null; }

        return this.parent.child(0);
    }

    right() {
        let l = this.children.length;
        if (l > 0) {
            return this.child(l - 1);
        }
        else {
            return this.thread;
        }
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

var first_walk = function(v, distance = 1.0) {
    if (v.leaf()) {
        if (v.lefmost_sibling()) {
            v.x = v.left_sib().x + distance;
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
        first_walk(c);
        default_ancestor = apportion(c, default_ancestor, distance);
    }
    execute_shifts(v);

    let midpoint = (v.child(0).layout_left_side() + v.child(-1).layout_right_side()) / 2.0;
    let ell = v.child(0);
    let arr = v.child(-1);
    let w = v.left_sib();
    if (w) {
        v.x = w.x + distance;
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
            shift = (vil.x + sil) - (vir.x + sir) + distance;
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

var disperse_rank = function(rank) {
    let rl = _rank_lists[rank];
    let widthSum = 0;
    for (let n of rl) {
        n.pos_x = widthSum;
        widthSum += n.boxwidth + W_SEPARATION;
    }
}

var load_nodes = function() {
    let data = JSON.parse(_node_data);

    let rval = { 
        styles : data["styles"], 
        roots : new Array()
    }

    for (let o of data["roots"]) {
        rval.roots.push(new LiveNode(o, 0));
    }

    return rval;
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
    for (let i = 0; i < _rank_lists.length; i++) {
        disperse_rank(i);
    }

    draw_all(canvas);
}


let _styles = {};
let _node_label_keys = ["production", "type"];

const _node_data = `{
    "roots" : [
        {
            "production": "global_list",
            "type": null,
            "value": null,
            "id": 0,
            "line": -1,
            "@attr": {},
            "c": [
             {
              "production": "pipeline",
              "type": null,
              "value": null,
              "id": 1,
              "line": 1,
              "@attr": {},
              "c": [
               {
                "production": null,
                "type": "IDENT",
                "value": "_1997",
                "id": 2,
                "line": 1,
                "@attr": {},
                "c": []
               },
               {
                "production": "component_contents",
                "type": null,
                "value": null,
                "id": 3,
                "line": -1,
                "@attr": {},
                "c": [
                 {
                  "production": "Gets",
                  "type": null,
                  "value": null,
                  "id": 4,
                  "line": 2,
                  "@attr": {},
                  "c": [
                   {
                    "production": "staged_vardecl",
                    "type": null,
                    "value": null,
                    "id": 5,
                    "line": 2,
                    "@attr": {},
                    "c": [
                     {
                      "production": null,
                      "type": "STAGEREF",
                      "value": "f[",
                      "id": 6,
                      "line": 2,
                      "@attr": {},
                      "c": []
                     },
                     {
                      "production": "vardecl",
                      "type": null,
                      "value": null,
                      "id": 7,
                      "line": 2,
                      "@attr": {},
                      "c": [
                       {
                        "production": null,
                        "type": "VARDECL",
                        "value": "f_color:",
                        "id": 8,
                        "line": 2,
                        "@attr": {},
                        "c": []
                       },
                       {
                        "production": "type",
                        "type": null,
                        "value": null,
                        "id": 9,
                        "line": -1,
                        "@attr": {},
                        "c": []
                       },
                       {
                        "production": "index",
                        "type": null,
                        "value": null,
                        "id": 10,
                        "line": -1,
                        "@attr": {},
                        "c": [
                         {
                          "production": null,
                          "type": "INTEGER",
                          "value": "0",
                          "id": 11,
                          "line": 2,
                          "@attr": {},
                          "c": []
                         }
                        ]
                       }
                      ]
                     }
                    ]
                   },
                   {
                    "production": "Gets",
                    "type": null,
                    "value": null,
                    "id": 12,
                    "line": 3,
                    "@attr": {},
                    "c": [
                     {
                      "production": "staged_vardecl",
                      "type": null,
                      "value": null,
                      "id": 13,
                      "line": 3,
                      "@attr": {},
                      "c": [
                       {
                        "production": null,
                        "type": "STAGEREF",
                        "value": "v[",
                        "id": 14,
                        "line": 3,
                        "@attr": {},
                        "c": []
                       },
                       {
                        "production": "vardecl",
                        "type": null,
                        "value": null,
                        "id": 15,
                        "line": 3,
                        "@attr": {},
                        "c": [
                         {
                          "production": null,
                          "type": "VARDECL",
                          "value": "v_color:",
                          "id": 16,
                          "line": 3,
                          "@attr": {},
                          "c": []
                         },
                         {
                          "production": "type",
                          "type": null,
                          "value": null,
                          "id": 17,
                          "line": -1,
                          "@attr": {},
                          "c": []
                         },
                         {
                          "production": "index",
                          "type": null,
                          "value": null,
                          "id": 18,
                          "line": -1,
                          "@attr": {},
                          "c": []
                         }
                        ]
                       }
                      ]
                     },
                     {
                      "production": "staged_vardecl",
                      "type": null,
                      "value": null,
                      "id": 19,
                      "line": 4,
                      "@attr": {},
                      "c": [
                       {
                        "production": null,
                        "type": "STAGEREF",
                        "value": "a[",
                        "id": 20,
                        "line": 4,
                        "@attr": {},
                        "c": []
                       },
                       {
                        "production": "vardecl",
                        "type": null,
                        "value": null,
                        "id": 21,
                        "line": 4,
                        "@attr": {},
                        "c": [
                         {
                          "production": null,
                          "type": "VARDECL",
                          "value": "a_color:",
                          "id": 22,
                          "line": 4,
                          "@attr": {},
                          "c": []
                         },
                         {
                          "production": "type",
                          "type": null,
                          "value": null,
                          "id": 23,
                          "line": -1,
                          "@attr": {},
                          "c": [
                           {
                            "production": "typeref",
                            "type": null,
                            "value": null,
                            "id": 24,
                            "line": 4,
                            "@attr": {},
                            "c": [
                             {
                              "production": null,
                              "type": "IDENT",
                              "value": "vec4",
                              "id": 25,
                              "line": 4,
                              "@attr": {},
                              "c": []
                             }
                            ]
                           }
                          ]
                         },
                         {
                          "production": "index",
                          "type": null,
                          "value": null,
                          "id": 26,
                          "line": -1,
                          "@attr": {},
                          "c": [
                           {
                            "production": null,
                            "type": "INTEGER",
                            "value": "1",
                            "id": 27,
                            "line": 4,
                            "@attr": {},
                            "c": []
                           }
                          ]
                         }
                        ]
                       }
                      ]
                     }
                    ]
                   }
                  ]
                 },
                 {
                  "production": "Gets",
                  "type": null,
                  "value": null,
                  "id": 28,
                  "line": 8,
                  "@attr": {},
                  "c": [
                   {
                    "production": "vardecl",
                    "type": null,
                    "value": null,
                    "id": 29,
                    "line": 8,
                    "@attr": {},
                    "c": [
                     {
                      "production": null,
                      "type": "VARDECL",
                      "value": "pi:",
                      "id": 30,
                      "line": 8,
                      "@attr": {},
                      "c": []
                     },
                     {
                      "production": "type",
                      "type": null,
                      "value": null,
                      "id": 31,
                      "line": -1,
                      "@attr": {},
                      "c": []
                     },
                     {
                      "production": "index",
                      "type": null,
                      "value": null,
                      "id": 32,
                      "line": -1,
                      "@attr": {},
                      "c": []
                     }
                    ]
                   },
                   {
                    "production": null,
                    "type": "FLOAT",
                    "value": "3.14",
                    "id": 33,
                    "line": 8,
                    "@attr": {},
                    "c": []
                   }
                  ]
                 }
                ]
               }
              ]
             }
            ]
           }
           
           
    ],
    "links" : [
        ["left", "right"]
    ],
    "styles" : {
        "missing_type" : {
            "bgcolor" : "#ff4444",
            "fill" : false
        }
    }
}`
