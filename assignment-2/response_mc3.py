import sys
import pynusmv
from pynusmv_lower_interface.nusmv.parser import parser 

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
    
def parse(spec):
    """
    Visit the syntactic tree of the formula `spec` to check if it is a response formula,
    that is wether the formula is of the form
    
                    G (f -> F g)
    
    where f and g are boolean combination of basic formulas.
    
    If `spec` is a response formula, the result is a pair where the first element is the 
    formula f and the second element is the formula g. If `spec` is not a response 
    formula, then the result is None.
    """
    # the root of a spec should be of type CONTEXT
    if spec.type != specTypes['CONTEXT']:
        return None
    # the right child of a context is the main formula
    spec = spec.cdr
    # the root of a response formula should be of type OP_GLOBAL 
    if spec.type != specTypes['OP_GLOBAL']:
        return None
    # The formula in the scope of the G operator must be of type IMPLIES
    spec = spec.car
    if spec.type != specTypes['IMPLIES']:
        return None
    # Check if lhs of the implication is a formula with no temporal operators
    f_formula = spec.car
    if not is_boolean_formula(f_formula):
        return None
    # Check if rhs of the implication is a F g formula
    g_formula = spec.cdr
    if g_formula.type != specTypes['OP_FUTURE']:
        return None
    g_formula = g_formula.car
    if not is_boolean_formula(g_formula):
        return None
    return (f_formula, g_formula)

def compute_loop(model, s, frontiers):
    has_inputs = len(model.bddEnc.inputsVars) > 0

    # Phase 2.2: Building the self loop
    for k in range(len(frontiers)):
        if s <= frontiers[k]:
            break
    # frontiers[k] contains the loop knot

    path = [ s.get_str_values() ]
    curr = s

    for i in range(k - 1, -1, -1):

        old = curr
        pred = model.pre(curr) * frontiers[i]
        curr = model.pick_one_state(pred)
        
        if has_inputs:
            inputs = model.get_inputs_between_states(old, curr)
            path.insert(0, model.pick_one_inputs(inputs).get_str_values())
        else:
            path.insert(0, {})

        path.insert(0, curr.get_str_values())
    
    # Looping input
    if has_inputs:
        inputs = model.get_inputs_between_states(s, curr)
        path.insert(0, model.pick_one_inputs(inputs).get_str_values())
    else:
        path.insert(0, {})

    path.insert(0, s.get_str_values())
    return path

def compute_prefix(model, s):
    has_inputs = len(model.bddEnc.inputsVars) > 0
    # 2.3 Reaching the self loop
    
    # Insert inside frontiers the regions to reach s
    # [ init ... pre_s ]
    reached = model.init 
    frontiers = [reached]

    while (reached * s).is_false():
        next = model.post(reached) - reached
        frontiers.append(next)
        reached = reached + next

    path = []
    last = s
    # Construct the path traversing the frontiers in reverse
    for frontier in reversed(frontiers[:-1]):
        can_reach_last = model.pre(last)

        # The current state is one of the states that can reach last in
        # one step
        current_state = model.pick_one_state(frontier * can_reach_last)
        
        if has_inputs:
            inputs = model.get_inputs_between_states(current_state, last)
            path.insert(0, model.pick_one_inputs(inputs).get_str_values())
        else:
            path.insert(0, {})

        path.insert(0, current_state.get_str_values())

        last = current_state
        
    return path

def compute_counter_example(model: pynusmv.fsm.BddFsm, recur, pre_reach):
    for s in model.pick_all_states(recur):
        r = pynusmv.dd.BDD.false()
        new = model.post(s) * pre_reach

        frontiers = [new]

        while new.isnot_false():
            r = r + new
            new = model.post(new) * pre_reach
            new = new - r

            frontiers.append(new)
        
        r = r * recur
        if s <= r:
            return tuple(compute_prefix(model, s) + compute_loop(model, s, frontiers))

def check_explain_response_spec(spec):
    """
    Return whether the loaded SMV model satisfies or not the GR(1) formula
    `spec`, that is, whether all executions of the model satisfies `spec`
    or not. 
    """

    model = pynusmv.glob.prop_database().master.bddFsm
    react = parse(spec)
    if (react == None):
        return None
    
    f_spec, g_spec = react

    f_bdd = spec_to_bdd(model, f_spec)
    neg_g_bdd = spec_to_bdd(model, ~g_spec)

    reach = model.reachable_states
    recur = reach * neg_g_bdd * f_bdd

    while recur.isnot_false():
        pre_reach = pynusmv.dd.BDD.false()
        new = model.pre(recur) * neg_g_bdd

        while new.isnot_false():
            pre_reach = pre_reach + new
            if recur <= pre_reach:
                return (False, compute_counter_example(model, recur, pre_reach))
            new = (model.pre(new) - pre_reach) * neg_g_bdd
        recur = recur * pre_reach
    return (True, None)
    

def original_check(spec):
    if parse(spec) == None:
        return None
    return pynusmv.mc.check_explain_ltl_spec(spec)

if __name__ == "__main__":
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

        print("\n-- CUSTOM --")

        if prop.type != type_ltl:
            print("property is not LTLSPEC, skipping")
            continue
        res = check_explain_response_spec(spec)
        if res == None:
            print('Property is not a response formula, skipping')
        elif res[0] == True:
            print("Property is respected")
        elif res[0] == False:
            print("Property is not respected")
            print("Counterexample:", res[1])

        print("\n-- Original --")
        res = original_check(spec)
        if res == None:
            print('Property is not a response formula, skipping')
        elif res[0] == True:
            print("Property is respected")
        elif res[0] == False:
            print("Property is not respected")
            print("Counterexample:", res[1])
    
    pynusmv.init.deinit_nusmv()
