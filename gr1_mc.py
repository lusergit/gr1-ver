#!/bin/env python3

import pynusmv
import sys
from pynusmv_lower_interface.nusmv.parser import parser 
from collections import deque
from functools import reduce

specTypes = {'LTLSPEC': parser.TOK_LTLSPEC, 'CONTEXT': parser.CONTEXT,
    'IMPLIES': parser.IMPLIES, 'IFF': parser.IFF, 'OR': parser.OR, 'XOR': parser.XOR, 'XNOR': parser.XNOR,
    'AND': parser.AND, 'NOT': parser.NOT, 'ATOM': parser.ATOM, 'NUMBER': parser.NUMBER, 'DOT': parser.DOT,

    'NEXT': parser.OP_NEXT, 'OP_GLOBAL': parser.OP_GLOBAL, 'OP_FUTURE': parser.OP_FUTURE,
    'UNTIL': parser.UNTIL,
    'EQUAL': parser.EQUAL, 'NOTEQUAL': parser.NOTEQUAL, 'LT': parser.LT, 'GT': parser.GT,
    'LE': parser.LE, 'GE': parser.GE, 'TRUE': parser.TRUEEXP, 'FALSE': parser.FALSEEXP
}

basicTypes = {parser.ATOM, parser.NUMBER, parser.TRUEEXP, parser.FALSEEXP, parser.DOT,
              parser.EQUAL, parser.NOTEQUAL, parser.LT, parser.GT, parser.LE, parser.GE}
booleanOp = {parser.AND, parser.OR, parser.XOR, parser.XNOR, parser.IMPLIES, parser.IFF}

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

def reachable(model):
    reach = model.init
    new = model.init
    while model.count_states(new) > 0:
        new = model.post(new) - reach
        reach = reach + new
    return reach

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

    # Find the cycle that respects G(F(f_n)) for availabe n
    ft = find_cycle(model, fs) # find_false(find_cycle(fs), gs)
    gt = find_cycle(model, gs)

    if not ft:
        return True
    if not gt:
        return False
    print("ft: {}".format(ft))
    print("gt: {}".format(gt))
    # Check weather the intersection is not empty
    return ft <= gt


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
        print("here")
        return None
    return check_explain_gr1_spec_impl(spec)# pynusmv.mc.check_explain_ltl_spec(spec)

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
    print(res)
    # if res == None:
    #     print('Property is not a GR(1) formula, skipping')
    # if res[0] == True:
    #     print("Property is respected")
    # elif res[0] == False:
    #     print("Property is not respected")
    #     print("Counterexample:", res[1])

pynusmv.init.deinit_nusmv()
