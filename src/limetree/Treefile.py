import json

EPSILON = 0.01

_id_counter = 999

def _next_id() -> str:
    global _id_counter
    _id_counter += 1
    return str(_id_counter)

def payload_keys(obj: dict):
    return filter(lambda k: k[0] not in ('!',), obj.keys())

def split_sorted_key(k: str):
    s = k.split(':', 1)
    if len(s) == 2: return s[1]
    else: return k
    

class Edge:
    def __init__(self, name, target):
        self.name = name
        self.target = target
    pass


class SimState:
    def __init__(self):
        self.pos = 0.0
        self.vel = 0.0
        self.force = 0.0
        self.rankorder = 0
        self.active = True

    def start_step(self):
        #self.vel = 0.0
        self.force = 0.0        

    def integrate(self, dt):
        self.vel += self.force * dt  # everything weighs 1
        self.pos += self.vel * dt

    def restorative(self, child_state: 'SimState'):
        '''
        Get the restorative force between parent and child.
        
        This depends only on their relative positions.
        '''
        diff = child_state.pos - self.pos
        f = diff    # maybe it'll be something cool and complicated, so leave the var.
        self.force += f
        child_state.force -= f

    def separating(self, sister: 'SimState'):
        '''
        Computes the amount of leftward force on this state,
        and the amount of rightward force on the sister state.
        '''
        if self.rankorder < sister.rankorder:
            diff = sister.pos - self.pos
        else:
            raise RuntimeError("Node repulsion the wrong way round.")
        
        if diff < EPSILON: # this intentionally covers the case of them being on the wrong side of each other
            diff = 0.25
        
        f = 1.0 / diff**2
        self.force -= f
        sister.force += f

    @staticmethod
    def apply_separating(rank: list):
        for i in range(len(rank)):
            for j in range(i, len(rank)):
                rank[i].state.separating(rank[j])


class LayoutNode:
    def __init__(self, obj, treefile, rank = 0):
        self.id = str(obj['!id']) if '!id' in obj else _next_id()
        self.label = obj.get('!label', self.id)
        self.style = obj.get('!style', 'default')
        self.children = []
        self.payload = {}
        self.rank = rank
        self.state = SimState()
        self.collapsed = False
        treefile.reg_node(self)

        for pk in sorted(payload_keys(obj)):
            sub = obj[pk]
            key = split_sorted_key(pk)
            if isinstance(sub, dict) and pk[0] != '@': # child node
                self.append_child(key, LayoutNode(sub, treefile, rank + 1))
            if isinstance(sub, list) and pk[0] != '@': # list of child nodes
                for i, c in enumerate(sub):
                    if isinstance(c, dict):
                        self.append_child(f'{key}[{i}]', LayoutNode(c, treefile, rank + 1))
            else:
                self.payload[key] = sub

    def kids(self):
        for edge in self.children:
            yield edge.target

    def subtree(self):
        for k in self.kids():
            for st in k.subtree():
                yield st
        
        yield self

    def __repr__(self):
        return self.id

    def append_child(self, edgename, child: 'LayoutNode'):
        self.children.append(Edge(edgename, child))

    def apply_restorative(self, parent_state = None):
        if parent_state:
            parent_state.restorative(self.state)

        for k in self.kids(): k.apply_restorative(self.state)

    def position(self, x_scale, rank_step):
        return (self.state.pos * x_scale, self.rank * rank_step)


class Treefile:
    def __init__(self, roots, links, styles):
        self.styles = styles
        self.allnodes = {}
        self.ranks = []
        self.roots = [LayoutNode(r, self) for r in roots]
    
    def reg_node(self, n):
        if n.id in self.allnodes:
            raise RuntimeError('Attempting to create node for existing id: ' + n.id)
    
        self.allnodes[n.id] = n
        
        while len(self.ranks) <= n.rank:
            self.ranks.append([])
        
        ranklist = self.ranks[n.rank]
        n.state.rankorder = len(ranklist)
        ranklist.append(n)
    
    def step_sim(self):
        for r in self.roots:
            for n in r.subtree():
                n.state.start_step()
            
            r.apply_restorative()
        
        for r in self.roots:
            for n in r.subtree():
                n.state.integrate(1.0 / 6.0)
    
    def all_nodes(self):
        for r in self.roots:
            for n in r.subtree():
                yield n


def load_treefile(filepath):
    with open(filepath) as tf:
        treejson = json.load(tf)
        return Treefile(treejson['roots'], treejson['links'], treejson['styles'])
    

if __name__ == '__main__':
    import sys
    tf = load_treefile(sys.argv[1])
    print(tf.ranks)
    for i in range(100):
        tf.step_sim()