  #set document(author: "Luca Monetti", title: [Assignment 1])
  #set page(
    paper: "a4",
    margin: (x: 2.5cm, y: 3cm),
    header: (
      context {
        if here().page() > 1 {
          set text(size: 10pt, tracking: 0.5pt)
          stack(
            dir: ttb,
            spacing: 6pt,
            grid(
              columns: (1fr, 1fr),
              align(left, upper(context document.title)), align(right, upper(context document.author.first())),
            ),
            line(length: 100%, stroke: 0.5pt),
          )
        }
      }
    ),
    footer: context {
      if here().page() > 1 {
        align(center, text(size: 10pt, counter(page).display()))
      }
    },
  )

  #show raw.where(block: true): it => {
    let lines = it.text.split("\n")
    block(
      fill: luma(245),
      inset: 10pt,
      radius: 4pt,
      width: 100%,
      stroke: 0.5pt + luma(200),
      {
        grid(
          columns: (20pt, 1fr),
          gutter: 10pt,
          // Line numbers column
          ..range(0, lines.len())
            .map(i => (
              // 1. The Line Number
              align(right + horizon, text(fill: luma(150), font: "DejaVu Sans Mono", size: 9pt, str(i + 1))),
              // 2. The Code Line
              raw(lines.at(i), lang: it.lang),
            ))
            .flatten()
        )
      },
    )
  }


  #set text(font: "Libertinus Serif", size: 11pt)

  // -- Front Page

  #page(align(center + top)[

    #image("figures/unipd-logo.svg", width: 40%)

    #v(1.3em)
    #text(size: 34pt, weight: "bold", "University of Padua") \
    #v(10pt)
    #text(size: 14pt, [Department of Mathematics "Tullio Levi-Civita"])

    #v(15%)

    #text(size: 14pt, [Formal Methods for Cyber-Physical Systems])
    #v(-0.5em)
    #text(size: 26pt, weight: "bold", upper(context document.title))

    #v(1fr)

    #text(size: 12pt, context document.author.first() + " (Mat. 2199440)")

  ])

  #counter(page).update(1)

  = Part 1

  == Assignment

  The primary objective of the first part of the assignment is the implementation of a symbolic algorithm for invariant verification using BDDs (Binary Decision Diagrams) to interact with regions. Given a property, denoted as `spec`, the algorithm determines whether it holds for all reachable states of the loaded model. 

  If a specification is not an invariant of the model a counter-example must be returned. A counter-example is a `tuple` of alternating states and input that represent an actual execution of the system that start from an initial state and lead to a state that violates the specification.

  The output must be a tuple of 2 elements:
  - Result: a `boolean` value that is `True` if `spec` is an invariant, `False` otherwise.
  - Counter Example: `None` if `spec` is an invariant, a counter-example otherwise.

  == Logic

  An invariant of the model is a property $phi$ that holds for every reachable state. The verification process is built on this principle: to prove that $phi$ is an invariant of the system the algorithm must demonstrate that $not phi$ is unreachable from any initial state.

  That leads to two possible outcomes:
  - Invariant Holds: if the algorithm explores all the reachable states without finding one in which $not phi$ is `True` then $phi$ is an invariant of the model.
  - Violation: if the algorithm finds a reachable state where $not phi$ holds then the property $phi$ is not an invariant.


  == Implementation

  The verification process begins with the conversion of the specification `spec` into a BDD using the provided function `spec_to_bdd(model, spec)`. This allows for the application of symbolic algorithm for invariant verification.

  The algorithm proceeds through the following phases:
  - The sets `reach` and `new` are initialized with the model's initial states.
  - At each iteration, the set `new` is evaluated. If `new` is empty or violates the specification $phi$ then the exploration is complete.
  - If no violations are found and `new` is not empty the algorithm computes the post-image of `new`, removing all the already checked states. The newly discovered states are included in `reach`.
  - After the last iteration of the loop there are 2 cases:
    - If there is an invalid state inside `new` then the algorithm returns `False` and computes a counter-example.
    - If `new` is empty the specification $phi$ holds for every reachable state; therefore, it is an invariant.

  ```python
def check_explain_inv_spec(spec):
  # 1. Setup the bdds
  model = pynusmv.glob.prop_database().master.bddFsm      # Model fsm

  spec_bdd = spec_to_bdd(model, spec)                     # Bdd of spec
  negated_spec_bdd = -spec_bdd                            # Bdd of ~spec

  # 2. Explore the regions
  reach = model.init                                      # Already explored states
  new = model.init                                        # States to explore

  trace = [reach]                                         # Trace used to save the execution

  while new.isnot_false() and not new.intersected(negated_spec_bdd):

      # Find reachable states and remove already checked ones
      new = model.post(new) - reach                       
      reach = reach + new                                 # Add new states to reach

      trace.append(new)                                   # Add reached region to trace

  if (not new.intersected(negated_spec_bdd)):
      # The formula is satisfied on every reachable state
      return (True, None) 
  
  # 3. Build the counter-example
  counter_example = compute_counter_example(model, trace, negated_spec_bdd)

  # The property is not an invariant, return a counter-example
  return (False, tuple(counter_example))
  ```

  === Counter example generation

  When a specification is violated, a counter-example must be provided to demonstrate the failure.

  The algorithm maintains a `trace` list where each element represents the region reached in that iteration starting from the previous one. The execution is then reconstructed via backwards traversal.

  The function `compute_counter_example(model, trace, spec)` implements this operation through the following steps:
  - The algorithm picks a state `current` from the set of invalid states, computed by the intersection `trace[-1] * spec`, and inserts it into the `counter_example` list.
  - The `trace` is then traversed in reverse starting from the second-to-last element. At each iteration one state is selected from the current region and added, with the curresponding input, to `counter_example`.
  - The procedure returns a valid execution of the model that leads to an invalid state.

  ```python
def compute_counter_example(model, trace, neg_spec):
  invalid_states = trace[-1] * neg_spec                       # States that violate spec
  current = model.pick_one_state(invalid_states)              # Current considered value

  # States that can reach current in one step
  pre_states = model.pre(current)                                
  counter_example = [current.get_str_values()]                # Counter-example list

  # Check if the model uses inputs
  has_inputs = not not len(model.bddEnc.inputsVars)           

  # Interate over the trace starting from the second last
  for current_set in reversed(trace[:-1]):

      # Get a state that has a transition to current
      prev_state = model.pick_one_state(current_set * pre_states)     

      # Get the input that caused the transition
      if has_inputs:
          trans_inputs = model.get_inputs_between_states(prev_state, current)
          input_values = model.pick_one_inputs(trans_inputs).get_str_values()
          counter_example.insert(0, input_values)
      else:
          counter_example.insert(0, {})

      # Add the picked state
      counter_example.insert(0, prev_state.get_str_values())        

      # Update invariants
      current = prev_state
      pre_states = model.pre(current)

  return counter_example               
  ```

  == Correctness

  This section provides a formal demonstration of correctness for the implemented algorithm.
  The algorithm is composed of two main loops:
  - Reachable state exploration
  - Counter-example generation

  The correctness of each phase is demonstrated using the Loop invariant technique.

  === Exploration of the reachable states

  The exploration phase identifies all the reachable states while checking for property violations.

  ==== Loop invariants

  Three invariants are maintained throughout the execution in the first loop:
  - `reach`: representing the region of all the already reached states without duplicates.
  - `new`: represent the region of all the newly found reachable states.
  - `trace`: an ordered list where each element represents a region of all the states reached at each iteration.

  ==== Base case
  Initially `reach`,`new` and `trace` are initialized with the initial states of the model, therefore all invariants hold.

  ==== Inductive step
  The loop condition checks if `new` is not empty, in that case there are still new states to explore and the loop body is executed.

  For each iteration $i$:
  - `new` is updated by computing the post-image of the previous `new` and subtracting all the states that are already present in `reach`. Therefore `new` contains only states reachable from the $i - 1$ iteration region that are not already in `reach`.
  - `reach` is updated to include the current set `new`, therefore it contains all the reachable states found so far.
  - `trace` appends the current set `new`, therefore is a list of $i + 1$ elements representing all the regions reachable from the previous region.

  ==== Termination
  The loop invariants hold for the base case and for the inductive case. Therefore by induction the loop invariants hold for each iteration of the loop.

  Since the state space of the model is finite the algorithm will eventually explore all the reachable states. Therefore there are only two possible execution:

  + `new` becomes empty, all the reachable states have been explored and none of them violate the specification, so the algorithm returns `(True, None)`.
  + `new` intersected with `neg_spec_bdd` is not empty, there exists at least one newly reached state that violates the specification $phi$, so the algorithm returns `False` along with a counter-example.

  === Counter-example generation

  If a violation is detected, a second loop reconstructs a valid execution path from one initial state to the violating state.

  ==== Loop invariant

  Two invariants are maintained throughout the execution in the second loop:
  - `counter_example`: a list of alternating states and inputs representing a valid execution of the system that lead to an invalid state.
  - `current`: the current state being added to the counter-example list.

  ==== Base case
  Initially `current` is initialized with a state picked from the set of invalid states, therefore it is a state that violates the specification. The `counter_example` list is initialized with this state. Therefore the invariants hold.

  ==== Inductive step
  The algorithm iterates backwards through the `trace` list, starting from the second-to-last element. At each step $i$:
  - A predecessor state is selected from a list of states that are in `trace[i]` and can reach `current` in one transition.
  - `counter_example` is updated by prepending this predecessor and the corresponding input.
  - `current` is updated to this predecessor.

  ==== Termination
  The invariants hold for the base case and for the inductive case. Therefore by induction the loop invariants hold for each iteration of the loop.

  The trace list is finite, since the model is finite and the algorithm explores only reachable states. Therefore the loop will terminate after a finite number of steps. There are only one possible execution: the algorithm returns the `counter_example` list.

  #pagebreak()

  = Part 2

  == Assignment

  The second part of the assignment requires the implementation of a symbolic algorithm for the verification of a specific class of LTL formulas called _response formulas_. These formulas follow the structure:

  $ square (f -> diamond g) $

  In this context, both $f$ and $g$ are Boolean combinations of base formulas with no temporal operators.

  In the following pages will be described an implementation of the function `check_examplain_response_spec(spec)` that determines if the provided `spec` is satisfied by the loaded model.

  If a specification is not satisfied by the model a counter-example must be returned. A counter-example is a `tuple` of alternating states and input that represent an actual execution of the system that start from an initial state and lead to a state that violates the specification.

  The output must be a tuple of 2 elements:
  - Result: a `boolean` value that is `True` if `spec` is satisfied, `False` otherwise.
  - Counter Example: `None` if `spec` is satisfied, a counter-example otherwise.

  == Logic

  The algorithm addresses _response formula_, which are defined by the requirement:

  #align(center, [_Every time that $f$ occurs, $g$ must eventually happen at the same time or afterwards._])

  As a liveness property, a response formula is evaluated over infinite computations. To prove that the formula is falsified a counter-example that satisfies the negation of the property must be provided. A path in which $f$ holds but $g$ never happens again. 

  In a finite state system such path is composed of two section:
  + *Prefix*: A sequence of states leading to a state where $f$ is satisfied.
  + *Loop*: An infinite cycle originating from the prefix, within which $g$ is always `False`.

  == Implementation

  The verification process begins by validating the structure of the specification using the provided function `parse(spec)`. If the function returns `None`, the specification is not a valid response formula, and the procedure terminates.

  Once the structure is validated, the formulas $f$ and $not g$ are converted into BDDs using the provided function `spec_to_bdd(model, spec)`.

  == Iterative cycle detection

  The algorithm will operate only on the reachable states of the model, identified by `model.reachable_states`. The variable `recur` is initialized within this set, specifically to represent all reachable states where $f$ holds and $g$ is `False`.

  The algorithm then proceeds to identify a cycle where $g$ remains `False`:
  - At each iteration `recur` is evaluated. If `recur` is empty then a cycle is not found and the algorithm returns `(True, None)`.
  - Otherwise the algorithm compute `pre_reach`, which consists of all states capable of reaching the current `recur` in one or more transition. The set `new` is computed to identify states that remains part of a potential cycle.
  - If a cycle is found, the algorithm build a counter-example using the function `compute_counter_example(model, recur, pre_reach)`, which will be described in the next section.

  ```python
  def check_explain_response_spec(spec):
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
  ```

  === Counter example generation

  A counter-example is an execution of the system that leads to a state where the formula is not satisfied. It is composed of 2 parts:

  + *Prefix*: A sequence of states leading to a state where $f$ hold.
  + *Loop*: An infinite cycle in which $g$ is always `False`.

  These two parts are computed by `compute_prefix` and `compute_loop` and then combined.

  In the end the algorithm return an execution that start from an initial state, reach a state where $f$ holds and $g$ is `False` and then proceeds with a cycle whithin which $g$ is always `False`.

  ```python
  def compute_counter_example(model, recur, pre_reach):
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
  ```

  ==== Build the prefix

  The prefix is reconstructed by identifying a path from the initial state set to the specific state identified as the entry point of the cycle. This procedure follows the previously discussed symbolic reachability approach.

  Starting from model.init, the algorithm explores reachable states layer by layer. Each layer (or "frontier") is stored in a list until a frontier that contains the designated starting state of the cycle is reached.

  Once the target state is located the sequence is constructed by traversing the frontiers in reverse. The resulting sequence is then assembled into the final `tuple`.

  ```python
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
  ```

  ==== Build the loop

  The reconstruction of the infinite cycle is a more complex procedure that requires to identifying a sequence that begins and ends at the same state.

  The algorithm initially identify the minimum number of steps required to reach the state `s` within the candidate region.

  The algorithm mantains two invariants:
  - `path`: a sequence of alternating states and inputs.
  - `current`: the state currently being processed.

  At each iteration the algorithm select a predecessor state from the preceding frontier that can reach `current` in a single transition. The state is prepended to the output with its corresponding input.

  ```python
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
            inpute_values = model.pick_one_inputs(inputs).get_str_values()
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
  ```

  == Correctness

  This section provides a formal demonstration of correctness for the implemented algorithm.
  The algorithm is composed of three main loop that can be repeated in different functions:

  - Cycle identification
  - Breadth-First Search
  - Counter-example generation

  The correctness of Breadth-First Search and Counter Example generation are discussed in the previous part. The correctness of the cycle identification can be proved using the loop invariant technique.

  === Cycle identification

  The cycle identification phase identifies a set of states that violates the liveness property $G( f -> F g)$ by searching for a cycle where $f$ has occurred but $g$ never follows.

  ==== Loop invariants

  The cycle detection is done by an outer loop that reduces the set of potential states that can start a cycle and an inner loop that computes the set of states that can reach each of those states.

  Two main invariant are maintained in the inner loop:
  - `pre_reach`: represents the region of all states that can both reach the current `recur` set in one or more transition and satisfies $not g$. 
  - `new`: represent the region of all the newly found states that can both reach the current `recur` in one or more transition and satisfy $not g$.

  ==== Base case
  Initially `pre_reach` is empty and `new` is initialized to `model.pre(recur) * neg_g_bdd`. The invariants hold for the base case.

  ==== Inductive step
  The loop condition checks if `new` is not empty. In that case there are still states that can starts a cycle where $not g$ holds.

  For each iteration $i$:
  - `pre_reach` is updated to include `new`. It now contains all the states that can reach the current `recur` in one or more transition.
  - `new` is updated with the pre-image of the current `new` by subtracting states already in `pre_reach` and restrinting its value to those that respect `not_g_bdd` ($not g$). It now contains all the states that can reach the current `recur` in $i + 1$ steps.
  - If `recur` becoms a subset of `pre_reach` there is a cycle.

  ==== Termination
  The loop invariants hold for the base case and for the inductive case. Therefore by induction the loop invariants hold for each iteration of the loop.

  Since the state space of the model is finite the set of states `pre_reach` cannot grow indefinitely.

  Therefore there are only two possible execution:
  + `new` becomes empty. This means that the current `recur` cannot reach itself. The outer loop will reduce `recur` and tries again. If `recur` becomes empty the algorithm returns `(True, None)`.
  + If the condition `recur <= pre_reach` becomes true a cycle exists. The algorithm returns `False` along with a counter-example.
