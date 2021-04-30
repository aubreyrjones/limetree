import random
import json

MIN_NAME_LENGTH = 5
MAX_NAME_LENGTH = 15
MAX_CHILDREN = 5
MAX_DEPTH = 10

MAX_NODE_COUNT = 50
cur_node_count = 0

random.seed()

def no_naughty(w):
    for bad_word in BAD_WORDS:
        if bad_word in w:
             return False
    return True

def rand_name():
    while True:
        l = random.randrange(MIN_NAME_LENGTH, MAX_NAME_LENGTH)
        w = "".join([chr(random.randrange(ord('A'), ord('Z'))) for i in range(l)])
        if no_naughty(w): return w

def rand_node(depth = 0):
    if depth >= MAX_DEPTH: return None

    global cur_node_count
    if cur_node_count >= MAX_NODE_COUNT:
        return
    rval = {}
    rval['!id'] = cur_node_count
    cur_node_count += 1
    rval["!label"] = rand_name()

    
    nchildren = random.randrange(0, MAX_CHILDREN)
    rval["children"] = []
    for i in range(nchildren):
        c = rand_node(depth + 1)
        if not c: return rval
        rval["children"].append(c)

    return rval


limedict = {}
limedict['nodes'] = [rand_node()]
limedict['styles'] = []
limedict['edges'] = []
limedict['links'] = []
limedict['label_keys'] = []
limedict['payload_objects'] = []
print(json.dumps(limedict))
