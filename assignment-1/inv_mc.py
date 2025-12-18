import pynusmv
import sys

def spec_to_bdd(model, spec):
    """
    Return the set of states of `model` satisfying `spec`, as a BDD.
    """
    bddspec = pynusmv.mc.eval_ctl_spec(model, spec)
    return bddspec

def default_check_explain_inv_spec(spec):
    """
    Return whether the loaded SMV model satisfies or not the invariant
    `spec`, that is, whether all reachable states of the model satisfies `spec`
    or not. Return also an explanation for why the model does not satisfy
    `spec``, if it is the case, or `None` otherwise.

    The result is a tuple where the first element is a boolean telling
    whether `spec` is satisfied, and the second element is either `None` if the
    first element is `True``, or an execution of the SMV model violating `spec`
    otherwise.

    The execution is a tuple of alternating states and inputs, starting
    and ennding with a state. States and inputs are represented by dictionaries
    where keys are state and inputs variable of the loaded SMV model, and values
    are their value.
    """
    ltlspec = pynusmv.prop.g(spec)
    res, trace = pynusmv.mc.check_explain_ltl_spec(ltlspec)
    return res, trace


def check_explain_inv_spec(spec):
    """
    Return whether the loaded SMV model satisfies or not the invariant
    `spec`, that is, whether all reachable states of the model satisfies `spec`
    or not. Return also an explanation for why the model does not satisfy
    `spec``, if it is the case, or `None` otherwise.

    The result is a tuple where the first element is a boolean telling
    whether `spec` is satisfied, and the second element is either `None` if the
    first element is `True``, or an execution of the SMV model violating `spec`
    otherwise.

    The execution is a tuple of alternating states and inputs, starting
    and ennding with a state. States and inputs are represented by dictionaries
    where keys are state and inputs variable of the loaded SMV model, and values
    are their value.
    """
    # 1. Setup the bdds
    spec_bdd = spec_to_bdd(model, spec)                 # Bdd of spec
    negated_spec_bdd = -spec_bdd                        # Bdd of ~spec

    model = pynusmv.glob.prop_database().master.bddFsm  # Model fsm

    # 2. Explore the regions
    reach = model.init                                  # Already explored states
    new = model.init                                    # States to explore

    trace = [reach]                                     # Trace used to save the execution

    while new.isnot_false() and not new.intersected(negated_spec_bdd):

        new = model.post(new) - reach                   # Remove the already checked states
        reach = reach + new                             # Consider them as reached

        trace.append(new)

    if (not new.intersected(spec_bdd)):
        # The formula is satisfied on every reachable state
        return (True, None)
    
    # 3. Build the counter-example
    invalid_states = new * phi                                  
    current_bad_state = model.pick_one_state(invalid_states)

    counter_example = [current_bad_state.get_str_values()]

    # Check if the model uses inputs
    has_inputs = not not len(model.bddEnc.inputsVars)

    # Interate over the trace starting from the second last
    for current_set in reversed(trace[:-1]):

        # Get a state that has a transition to current_bad_state
        pre_states = model.pre(current_bad_state)                       
        prev_state = model.pick_one_state(current_set * pre_states)

        # Get the input that caused the transition
        if has_inputs:
            trans_inputs = model.get_inputs_between_states(prev_state, current_bad_state)
            input_values = model.pick_one_inputs(trans_inputs).get_str_values()
            counter_example.insert(0, input_values)
        else:
            counter_example.insert(0, {})

        # Add the picked state
        counter_example.insert(0, prev_state.get_str_values())        

        current_bad_state = prev_state

    # The property is not an invariant, return a counter-example
    return (False, tuple(counter_example))

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage:", sys.argv[0], "filename.smv")
        sys.exit(1)

    pynusmv.init.init_nusmv()
    filename = sys.argv[1]
    pynusmv.glob.load_from_file(filename)
    pynusmv.glob.compute_model()
    invtype = pynusmv.prop.propTypes['Invariant']
    for prop in pynusmv.glob.prop_database():
        spec = prop.expr

        print("\n-- Custom --\n")

        if prop.type == invtype:
            print("Property", spec, "is an INVARSPEC.")
            res, trace = check_explain_inv_spec(spec)
            if res == True:
                print("Invariant is respected")
            else:
                print("Invariant is not respected")
                print(trace)
        else:
            print("Property", spec, "is not an INVARSPEC, skipped.")

        print("\n-- Original --\n")

        if prop.type == invtype:
            print("Property", spec, "is an INVARSPEC.")
            res, trace = default_check_explain_inv_spec(spec)
            if res == True:
                print("Invariant is respected")
            else:
                print("Invariant is not respected")
                print(trace)
        else:
            print("Property", spec, "is not an INVARSPEC, skipped.")

    pynusmv.init.deinit_nusmv()
