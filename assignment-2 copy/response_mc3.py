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
    # Check if the model uses inputs
    has_inputs = not not len(model.bddEnc.inputsVars)

    # Find the minimum value of k
    for k in range(len(frontiers)):
        if s <= frontiers[k]:
            break

    # Reconstruct the execution
    path = [ s.get_str_values() ]                       # Cycle execution
    current = s                                         # Current Value

    for i in range(k - 1, -1, -1):                    

        # Get a state that has a transition to current
        prev_states = model.pre(current) * frontiers[i]
        prev_state = model.pick_one_state(prev_states)
        
         # Get the input that caused the transition
        if has_inputs:
            trans_inputs = model.get_inputs_between_states(pre_states, current)
            input_values = model.pick_one_inputs(inputs).get_str_values()
            path.insert(0, input_values)
        else:
            path.insert(0, {})

        # Add the picked state
        path.insert(0, prev_state.get_str_values())

        # Update invariants
        current = prev_state                # Update the current state
        pre_states = model.pre(current)     # States that can reach current in one step
    
    # Get inputs that starts the loop
    if has_inputs:
        inputs = model.get_inputs_between_states(s, current)
        path.insert(0, model.pick_one_inputs(inputs).get_str_values())
    else:
        path.insert(0, {})

    # Add s at the beginning of the loop
    path.insert(0, s.get_str_values())

    return path

def compute_prefix(model, s):
    # Check if the model uses inputs
    has_inputs = not not len(model.bddEnc.inputsVars)

    reach = model.init                  # Already explored states
    new = model.init                    # States to explore

    frontiers = [reach]

    while (reach * s).is_false():       # Check if s is contained in reach

        new = model.post(new) - reach   # Find reachable states and remove already checked ones
        reach = reach + new             # Add new states to reach

        frontiers.append(new)           # Add reached region to frontiers

    # Build the path
    current = s

    pre_states = model.pre(current)
    path = [current.get_str_values()]

    # Interate over the frontiers starting from the second last
    for frontier in reversed(frontiers[:-1]):
        
        # Get a state that has a transition to current
        prev_state = model.pick_one_state(frontier * pre_states)     
        
        # Get the input that caused the transition
        if has_inputs:
            trans_inputs = model.get_inputs_between_states(pre_states, current)
            inpute_values = model.pick_one_inputs(inputs).get_str_values()
            path.insert(0, input_values)
        else:
            path.insert(0, {})

        # Add the picked state
        path.insert(0, prev_state.get_str_values())

        # Update invariants
        current = prev_state                # Update the current state
        pre_states = model.pre(current)     # States that can reach current in one step
        
    return path

def compute_counter_example(model, recur, pre_reach):
    """
    Return a list of alternating states in trace and inputs, starting
    with an inital state of the model and ending with a state already 
    present in the sequence. 
    States and inputs are represented by dictionaries where keys are state 
    and inputs variable of the loaded SMV model, and values are their value.
    """
    
    # Analyze each state of recur
    for s in model.pick_all_states(recur):

        r = pynusmv.dd.BDD.false()              # Reached states
        new = model.post(s) * pre_reach         # Newly valid state in post image  

        frontiers = [new]

        # Compute frontiers
        while new.isnot_false():
            r = r + new
            new = (model.post(new) * pre_reach) - r

            frontiers.append(new)
        
        r = r * recur

        if s <= r:
            prefix = compute_prefix(model, s)
            loop = compute_loop(model, s, frontiers)
            return tuple(prefix + loop)

def check_explain_response_spec(spec):
    """
    Return whether the loaded SMV model satisfies or not the GR(1) formula
    `spec`, that is, whether all executions of the model satisfies `spec`
    or not. 
    """

    # 1. Check the formula structure
    react = parse(spec)
    if (react == None):
        return None

    # 2. Setup the bdds
    model = pynusmv.glob.prop_database().master.bddFsm
    
    f_spec, g_spec = react

    f_bdd = spec_to_bdd(model, f_spec)                      # BDD for formula f
    neg_g_bdd = spec_to_bdd(model, ~g_spec)                 # BDD for formula ~g

    # 3. Cycle detection
    reach = model.reachable_states                          # Reachable states
    recur = reach * neg_g_bdd * f_bdd                       # Possible starting point for a cycle

    while recur.isnot_false():
        pre_reach = pynusmv.dd.BDD.false()                  # States that can reach recur
        new = model.pre(recur) * neg_g_bdd                  # Newly discovered states

        while new.isnot_false():

            pre_reach = pre_reach + new

            if recur <= pre_reach:
                # A cycle is found
                return (False, compute_counter_example(model, recur, pre_reach))

            new = (model.pre(new) - pre_reach) * neg_g_bdd  # Added only state where ~g is True

        recur = recur * pre_reach

    # The formula is satisfied by the model
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
