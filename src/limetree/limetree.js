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
    constructor(o, rank, parent) {
        this.parent = parent;
        this.thread = null;
        this.rank = rank;
        this.rankorder = 0;
        this.payload = {};
        this.children = new Array();
        this.pos_x = 0;
        this.mod = 0;
        this.pos_y = RANK_SEPARATION * this.rank;
        this.boxwidth = 100;
        if ("!id" in o) {
            this.id = o["!id"];
        } 
        else if ("id" in o) {
            this.id = o["id"];
        }
        else {
            this.id = next_node_id();
        }
        this.font = '24px sans-serif';
        
        _all_nodes[this.id] = this;

        let rl = rank_list(this.rank); 
        this.rankorder = rl.length
        rl.push(this);
       
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
                                this.add_child(child_key, new LiveNode(sub_o, rank + 1, this));
                            }
                        }
                    }
                    else {
                        this.add_child(my_key, new LiveNode(o[k], rank + 1, this));
                    }
                }
                else {
                    // regular payload value
                    this.payload[my_key] = o[k];
                }
            }
        }

        for (let k of _node_label_keys) {
            if (o[k]) {
                this.label = o[k];
                break;
            }
        }
    }

    add_child(edge_name, c) {
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

    next_left() {
        if (this.children.length > 0) {
            return this.children[0].target;
        }
        else {
            return this.thread;
        }
    }

    next_right() {
        let l = this.children.length;
        if (l > 0) {
            return this.children[l - 1].target;
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

const _node_label_keys = ["production", "type"];

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
