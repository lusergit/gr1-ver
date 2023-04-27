#!/bin/env python3
import pynusmv
import sys
import pynusmv
import sys
from pynusmv_lower_interface.nusmv.parser import parser 
from collections import deque
from functools import reduce

specTypes = { 
    'LTLSPEC': parser.TOK_LTLSPEC, 'CONTEXT': parser.CONTEXT, 'IMPLIES': parser.IMPLIES, 'IFF': parser.IFF, 
    'OR': parser.OR, 'XOR': parser.XOR, 'XNOR': parser.XNOR, 'AND': parser.AND, 'NOT': parser.NOT, 
    'ATOM': parser.ATOM, 'NUMBER': parser.NUMBER, 'DOT': parser.DOT, 'NEXT': parser.OP_NEXT,
    'OP_GLOBAL': parser.OP_GLOBAL, 'OP_FUTURE': parser.OP_FUTURE, 'UNTIL': parser.UNTIL,
    'EQUAL': parser.EQUAL,'NOTEQUAL': parser.NOTEQUAL,'LT': parser.LT,'GT': parser.GT,'LE': parser.LE,
    'GE': parser.GE,'TRUE': parser.TRUEEXP,'FALSE': parser.FALSEEXP
}

basicTypes = {
    parser.ATOM, parser.NUMBER, parser.TRUEEXP, parser.FALSEEXP, parser.DOT, parser.EQUAL,
    parser.NOTEQUAL, parser.LT, parser.GT, parser.LE, parser.GE
}

booleanOp = {
    parser.AND, parser.OR, parser.XOR, parser.XNOR, parser.IMPLIES, parser.IFF
}

def spec_to_bdd(model, spec):
    """
    Given a formula `spec` with no temporal operators, returns a BDD equivalent to
    the formula, that is, a BDD that contains all the states of `model` that
    satisfy `spec`
    """
    bddspec = pynusmv.mc.eval_simple_expression(model, str(spec))
    return bddspec

def is_boolean_formula(spec):
    """
    Given a formula `spec`, checks if the formula is a boolean combination of base
    formulas with no temporal operators. 
    """
    if spec.type in basicTypes:
        return True
    if spec.type == specTypes['NOT']:
        return is_boolean_formula(spec.car)
    if spec.type in booleanOp:
        return is_boolean_formula(spec.car) and is_boolean_formula(spec.cdr)
    return False

def is_GF_formula(spec):
    """
    Given a formula `spec` checks if the formula is of the form GF f, where f is a 
    boolean combination of base formulas with no temporal operators 
    """
    # check if formula is of type GF f_i
    if spec.type != specTypes['OP_GLOBAL']:
        return False
    spec = spec.car
    if spec.type != specTypes['OP_FUTURE']:
        return False
    return is_boolean_formula(spec.car)


def create_set_of_formulas(spec):
    """
    Given a formula `spec` of the form
    
                    (GF f_1 & ... & GF f_n) 
    
    where f_1, ..., f_n are boolean combination of basic formulas, returns the set of 
    formulas {f_1, ..., f_n}. 
    If `spec` is not in the required form, then the result is None.
    """
    f_set = set()
    working = deque()
    working.append(spec)
    while working:
        # next formula to analyse
        head = working.pop()
        if head.type == specTypes['AND']:
            # push conjuncts into the queue
            working.append(head.car)
            working.append(head.cdr)
        else:
            # check if it is a GF-formula
            if not is_GF_formula(head):
                return None
            # add boolean formula to the set
            f_set.add(head.car.car)
    return f_set

def parse_gr1(spec):
    """
    Visit the syntactic tree of the formula `spec` to check if it is a GR(1) formula,
    that is wether the formula is of the form
    
                    (GF f_1 & ... & GF f_n) -> (GF g_1 & ... & GF g_m)
    
    where f_1, ..., f_n, g_1, ..., g_m are boolean combination of basic formulas.
    
    If `spec` is a GR(1) formula, the result is a pair where the first element  is the 
    set of formulas {f_1, ..., f_n} and the second element is the set {g_1, ..., g_m}.
    If `spec` is not a GR(1) formula, then the result is None.
    """
    # the root of a spec should be of type CONTEXT
    if spec.type != specTypes['CONTEXT']:
        return None
    # the right child of a context is the main formula
    spec = spec.cdr
    # the root of a GR(1) formula should be of type IMPLIES
    if spec.type != specTypes['IMPLIES']:
        return None
    # Create the set of formulas for the lhs of the implication
    f_set = create_set_of_formulas(spec.car)
    if f_set == None:
        return None
    # Create the set of formulas for the rhs of the implication
    g_set = create_set_of_formulas(spec.cdr)
    if g_set == None:
        return None
    return (f_set, g_set)


def reacheability(fsm):
    reach = fsm.init
    new = fsm.init
    while fsm.count_states(new) != 0 :
        new = fsm.post(new) - reach
        reach = reach + new
    return reach


def GF(spec, reach):
    """check weather the model, in the `reach` subset verifies

    G ( F (spec)).

    If it does, it returns the set of frontiers calculated

    """
    fsm = pynusmv.glob.prop_database().master.bddFsm
    if not reach:
        return None
    recur = reach * spec
    while (fsm.count_states(recur) != 0):
        reach = pynusmv.dd.BDD.false()
        new = fsm.pre(recur)
        news = [new, recur]
        while (fsm.count_states(new) != 0):
            reach = reach + new 
            if recur.entailed(reach):
                return news
            new = (fsm.pre(new)) - reach
            news = [new] + news
        recur = recur * reach
    return None

def FG(spec, reach, recur):
    """check weather the model, in the `reach` subset verifies F ( G
    (spec)). If it does, it returns the set of frontiers calculated

    """
    fsm = pynusmv.glob.prop_database().master.bddFsm
    # reach = reacheability(fsm)
    if not reach:
        return None
    recur = recur * spec
    while (fsm.count_states(recur) != 0):
        reach = pynusmv.dd.BDD.false()
        new = fsm.pre(recur) * spec
        news = [new, recur]
        while (fsm.count_states(new) != 0):
            reach = reach + new 
            if recur.entailed(reach): # recur == reach
                return news
            new = (fsm.pre(new) * spec) - reach
            news = [new] + news
        recur = recur * reach
    return None
    

def loops(frontiers):
    """Returns the /reach/ set build from the frontiers given as
    input, this is useful in the forward phase to restrict more and
    more the set /reach/ in the FG and GF algotihms

    """
    if not frontiers:
        return None
    fsm = pynusmv.glob.prop_database().master.bddFsm
    frontiers = list(reversed(frontiers)) # recur all'inizio, poi post
    reach = frontiers[0]
    new = frontiers[0]
    for el in frontiers[1:]:
        new = fsm.post(new) * el
        new = new - reach
        reach = reach + new
    return reach



def head_to(s):
    """Return the path from the initial states to the state `state`,
    supposing it is reachable

    """
    fsm = pynusmv.glob.prop_database().master.bddFsm
    # forward phase
    init = fsm.init
    new = init
    reach = init
    frontiers = []
    # forward
    while not s.entailed(new):
        frontiers.append(new)
        new = fsm.post(new) - reach
        reach = reach + new

    path = [s]
    curr = s
    # backward
    for back in reversed(frontiers):
        pre_set = fsm.pre(curr) * back
        curr = fsm.pick_one_state(pre_set)
        path = [curr] + path
    return path

def counterexample(frontiers):
    """Given a list of frontiers of the FG algorithm, build
    alazo-shaped execution that starts from the model initial states
    and loops over the states given by the frontiers

    """
    fsm = pynusmv.glob.prop_database().master.bddFsm
    recur = frontiers[-1]
    frontiers = frontiers[:-1]
    reach = reduce(lambda x,acc: x+acc, frontiers) # * reacheability(fsm)
    s = fsm.pick_one_state(recur)
    while True:
        r = pynusmv.dd.BDD.false()
        new = fsm.post(s) * reach
        r_front = [new]
        while not fsm.count_states(new) == 0:
            r = r + new
            new = (fsm.post(new) * reach) - r
            r_front = r_front + [new]
        r = r * reach
        if s.entailed(r):
            i = 0
            for front in r_front:
                if s.entailed(front):
                    break
                i += 1
            path = head_to(s)
            curr = s
            n_path = []
            for new in reversed(range(i)):
                pred = fsm.pre(curr) * r_front[new]
                curr = fsm.pick_one_state(pred)
                path = path + [curr]
            path = path + [s]
            print(f"s: {s}")
            return list(reversed(path))
        else:
            s = fsm.pick_one_state(r)


# spec in gr1 form
def check_explain_gr1_spec_impl(spec):
    fsm = pynusmv.glob.prop_database().master.bddFsm
    reach = reacheability(fsm)

    # find fs and gs from formula
    fs, gs = parse_gr1(spec)

    loop_set_f = reacheability(fsm)
    for f in fs:
        bdd = spec_to_bdd(fsm, f)
        fronts_f = GF(bdd, loop_set_f)
        loop_set_f = loops(fronts_f)

    if loop_set_f:
        for g in gs:
            bdd = spec_to_bdd(fsm, g)
            bdd = ~bdd
            recur = fronts_f[-1]
            frontiers = FG(bdd, loop_set_f, recur)
            if frontiers:
                return False, counterexample(frontiers)

    return True, None


def check_explain_gr1_spec(spec):
    """
    Return whether the loaded SMV model satisfies or not the GR(1) formula
    `spec`, that is, whether all executions of the model satisfies `spec`
    or not. Return also an explanation for why the model does not satisfy
    `spec``, if it is the case, or `None` otherwise.

    The result is a tuple where the first element is a boolean telling
    whether `spec` is satisfied, and the second element is either `None` if the
    first element is `True``, or an execution of the SMV model violating `spec`
    otherwise. 

    The execution is a tuple of alternating states and inputs, starting
    and ending with a state. The execution is looping if the last state is somewhere 
    else in the sequence. States and inputs are represented by dictionaries
    where keys are state and inputs variable of the loaded SMV model, and values
    are their value.
    """
    if parse_gr1(spec) == None:
        return None
    return check_explain_gr1_spec_impl(spec)# pynusmv.mc.check_explain_ltl_spec(spec)


def compute_path(s, t):
    fsm = pynusmv.glob.prop_database().master.bddFsm
    inp_set = fsm.get_inputs_between_states(s, t)
    inp = fsm.pick_one_inputs(inp_set)
    return (inp, t)

def to_str(path):
    fsm = pynusmv.glob.prop_database().master.bddFsm
    tupath = (path[0],)
    # print(path)
    for s,t in zip(path, path[1:]):
        # print(tupath)
        comp = compute_path(s,t)
        tupath = tupath + comp
    # print(f"path: {tupath}")
    str_path = [el.get_str_values() for el in tupath]
    return str_path


if len(sys.argv) != 2:
    print("Usage:", sys.argv[0], "filename.smv")
    sys.exit(1)

pynusmv.init.init_nusmv()
filename = sys.argv[1]
pynusmv.glob.load_from_file(filename)
pynusmv.glob.compute_model()
type_ltl = pynusmv.prop.propTypes['LTL']
for prop in pynusmv.glob.prop_database():
    spec = prop.expr
    print(spec)
    if prop.type != type_ltl:
        print("property is not LTLSPEC, skipping")
        continue
    res = check_explain_gr1_spec(spec)
    # if res:
    #     print(to_str(res))
    # else:
    #     print("Property is respected")
    if res == None:
        print('Property is not a GR(1) formula, skipping')
    if res[0] == True:
        print("Property is respected")
    elif res[0] == False:
        print("Property is not respected")
        print("Counterexample:", tuple(to_str(res[1])))

pynusmv.init.deinit_nusmv()
