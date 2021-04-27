"use strict";

const FRAMERATE = 30;
const FRAMETIME = 1.0 / FRAMERATE;
const FRAME_MS = FRAMETIME * 1000;
const RANK_SEPARATION = 80.0;


var _next_node_id = 999;
var _all_nodes = {};
var _rank_lists = new Array();

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

class LiveNode {
    constructor(o, rank) {
        this.rank = rank;
        this.rankorder = 0;
        this.payload = {};
        this.children = {}
        this.pos_x = 400.0;
        this.pos_y = 50 + RANK_SEPARATION * this.rank;
        this.vel = 0.0;  // we only have X-axis velocity
        this.F = 0.0;    // ... and force
        this.boxwidth = 100;
        
        _all_nodes[this.id || next_node_id()] = this;

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
                let my_key = k;

                if (k[0] !== '@' && o[k] instanceof Object) {
                    if (o[k] instanceof Array) {
                        for (let i = 0; i < o[k].length; i++) {
                            let sub_o = o[k][i];
                            if (sub_o instanceof Object) {
                                let child_key = my_key + "[" + i + "]";
                                this.children[child_key] = new LiveNode(sub_o, rank + 1);
                            }
                        }
                    }
                    else {
                        this.children[my_key] = new LiveNode(o[k], rank + 1);
                    }
                }
                else {
                    // regular payload value
                    this.payload[my_key] = o[k];
                }
            }
        }
    }

    next_step() {
        this.vel *= 0.9; // don't know if we want to damp velocity like that yet.
        this.F = 0.0;
    }

    center() {
        return this.right_side() - (this.boxwidth / 2);
    }

    right_side() {
        return this.pos_x + this.boxwidth;
    }

    /**
     * Recursively calculate and accumulate the restorative parent/child force.
    */
    restorative() {
        for (let ck in this.children) {
            let c = this.children[ck];
            let diff = c.center() - this.center();
            let F = diff; //maybe gonna get cooler later
            this.F += F / (1 + this.rank);
            c.F -= F;// * (1 + this.rank);
            c.restorative();
        }
    }

    /**
     * Apply repulsive force between this node and all nodes
     * on the same rank to the right of this node.
    */
    separative() {
        let rl = rank_list(this.rank);
        for (let i = this.rankorder + 1; i < rl.length; i++) {
            let sister = rl[i];
            let diff = (sister.pos_x - 4) - (this.pos_x + this.boxwidth);
            let f;
            if (diff < 0) {
                f = -diff * 5;
            }
            else {
                if (diff < 0.001) { diff = 0.001; } // just get rid of epsilon
                f = 800.0 / diff;
            }
            self.F -= f;
            sister.F += f;
        }
    }

    integrate(dt) {
        this.vel += this.F * dt; // everything with unit weight
        this.pos_x += this.vel * dt;

        for (let ck in this.children) {
            this.children[ck].integrate(dt);
        }
    }

    draw(ctx) {
        ctx.font = '24px sans-serif';
        
        
        let label = this.label || this.id;
        let labelWidth = ctx.measureText(label).width;
        this.boxwidth = labelWidth + 8;

        ctx.strokeStyle = 'black';
        for (let ck in this.children) {
            let c = this.children[ck];
            ctx.beginPath();
            ctx.moveTo(this.center(), this.pos_y);
            ctx.lineTo(c.center(), c.pos_y);
            ctx.stroke();
        }

        
        ctx.fillStyle = 'rgb(200, 200, 200)';
        ctx.fillRect(this.pos_x - 4, this.pos_y - 25, this.boxwidth, 24 + 12);
        ctx.fillStyle = 'black';
        ctx.fillText(label, this.pos_x, this.pos_y);
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

var separate_ranks = function() {
    for (let rl of _rank_lists) {
        for (let n of rl) {
            n.separative();
        }
    }
}

var iter_all = function(f) {
    for (let nk in _all_nodes) {
        f(_all_nodes[nk]);
    }
}

var _timestep = function(dt) {
    iter_all(n => n.next_step());
    separate_ranks();
    for (let root of rank_list(0)) {
        root.restorative();
    }
    iter_all(n => n.integrate(dt));
}

var draw_all = function(canvas) {
    
    if (canvas.getContext) {
        var ctx = canvas.getContext('2d');
        ctx.clearRect(0, 0, canvas.width, canvas.height);
        iter_all(n => n.draw(ctx));
    }
}

var mainloop = function(canvas) {
    _timestep(FRAMETIME);
    draw_all(canvas);
}

var start_limetree = function() {
    load_nodes();

    let canvas = document.getElementById('tree_canvas');
    canvas.width  = window.innerWidth * 0.99;
    canvas.height = window.innerHeight * 0.98;
    
    setInterval(_ => mainloop(canvas), FRAME_MS);
}

let _node_data = `{
    "roots" : [
        {
            "!id" : "root",
            "!label" : "Root",
            "msg" : "I'm",
            "@payload_obj" : {
                "foo" : "bar"
            },
            "1:left" : {
                "!id" : "left",
                "!label" : "Left",
                "msg" : "a"
            },
            "2:right" : {
                "!id" : "right",
                "!label" : "Right",
                "!style" : "missing_type",
                "msg" : "teapot."    
            },
            "3:other" : {
                "!id" : "other",
                "!label" : "Other",
                "!style" : "missing_type",
                "msg" : "teapot."    
            }
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
