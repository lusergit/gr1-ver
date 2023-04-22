def repeatable(model, region):
    reach = reachable(model)
    recur = reach & region
    while model.count_states(recur) > 0:
        new = model.pre(recur)
        pre_reach = new
        while model.count_states(new) > 0:
            pre_reach = pre_reach + new
            if recur.entailed(pre_reach):
                return recur, pre_reach
            new = model.pre(new) - pre_reach
        recur = recur & pre_reach
    return None

# Find a cycle where fs hold, but no g ever hold
def find_witness(model, cycle, gs):
    # TODO
    return 1
    
def loop_set(model, recur, pre_reach):
    new = model.post(recur) & pre_reach
    # loop-visited states
    r = recur + new
    while model.count_states(new) > 0:
        r = r + new
        new = model.post(new) & pre_reach
        new = new - r
    return r


def try_loop(model, inters):
    # if the intersection is empty, return None, no cycle
    if model.count_states(inters) == 0:
        return None
    s = model.pick_one_state_random(inters)
    new = (model.post(s) & inters) - s # ensure len >= 1
    r = new + s
    while model.count_states(new) > 0:
        if s.entailed(new):
            return inters
        new = model.post(new) & inters
        new = new - r
        r = r + new
    return None

# Find all the cycles in the model where each `fs` eventually hold
def find_cycle(model, fs):
    # trova recur, pre_reach per ogni formula
    bls = list(map(lambda f: repeatable(model, f), fs))
    # Se ci sono dei set con None, significa che non ci sono loop che
    # verificano una formula => le ipotesi sono false e quindi
    # l'implicazione è vera
    if bls.count(None) > 0:
        return None

    loop_sets = map(lambda x : loop_set(model, x[0], x[1]), bls)
    inters = reduce(lambda x, acc : x & acc, loop_sets)
    # Now, either the intersection is still a loop set or not, try to
    # build a loop, if it succeeds, the is a loopset, if not is not
    # anymore (there are missing pieces)
    return try_loop(model, inters)

# spec in gr1 form
def check_explain_gr1_spec_impl(spec):
    model = pynusmv.glob.prop_database().master.bddFsm
    reach = reachable(model)

    # find fs and gs from formula
    fs, gs = parse_gr1(spec)
    # And build the respective bdds
    fs = list(map(lambda f : spec_to_bdd(model, f), fs))
    gs = list(map(lambda g : spec_to_bdd(model, g), gs))

    bls_f = list(map(lambda f : check_fg(model, reach, f), fs))
    bls_g = list(map(lambda g : check_fg(model, reach, g), gs))

    # If one or more hypotesis are not respected, the conlcusion is
    # true
    if bls_f.count(None) > 0:
        return False

    if bls_g.count(None) > 0:
        return True

    print(f"bls_f: {bls_f}\tbls_g: {bls_g}")
    ft = ~reduce(lambda x,acc : x + acc, bls_f)
    gt = ~reduce(lambda x,acc : x + acc, bls_g)

    sect = ft & gt

    b1 = list(map(lambda f : f.entailed(sect), fs))
    b2 = list(map(lambda f : f.entailed(sect), gs))
    print(f"b1: {b1}\tb2: {b2}")
    
    return False

# Build the loop set (set of all the loops) starting from the recur
# and prereach sets. /recur/ is the set of all /cadidates to start the
# loop/: a.k.a. nodes where the property holds, pre-reach is a sub
# region that contains all the potential nodes in the loop.
# def loop_set(model, recur, pre_reach):
#     # recur = recur * pre_reach
#     new = (model.post(recur) * pre_reach) - recur
#     # loop-visited states
#     r = recur + new
#     while not is_empty(model, new):
#         r = r + new
#         new = (model.post(new) * pre_reach) - r
#     return r
def loop_set(model, recur, pre_reach):
    s = model.pick_one_state_random(recur)
    while True:
        new = model.post(s) * pre_reach
        r = new
        while not is_empty(model, new):
            r = r + new
            new = (model.post(new) * pre_reach) - r
        r = r * recur
        if s.entailed(r):
            return r + s
        s = model.pick_one_state_random(r)

def init_path(model, loops):
    reach = model.init
    new = model.init
    sect = new & loops
    # Forward loops = loops & reachable(model) # Inutile perchè se un
    # nodo nel loop non è reachable allora non è nel loop.
    while is_empty(model, sect):
        new = model.post(new) - reach
        reach = reach + new
        sect = reach & loops
    # found forward path, start from sect
    path = sect
    new = sect
    cond = path & model.init
    while is_empty(model, cond):
        new = model.pre(new) & reach
        path = path + new
        cond = path & model.init
    return path


def check_fg(model, reachable, fbdd):
    # Input: model, reachable states, bdd rapresenting the formula f
    # in G(F(f)). The forumla is respected iff F(G(not f)) is /not/
    # respected
    ret = repeatable(model, fbdd)
    if ret == None:
        return None
    recur, pre_reach = ret
    loops = loop_set(model, recur, pre_reach)
    init = init_path(model, loops)
    # Return all the nodes that respect F(G(not f))
    return ~(init + loops)
