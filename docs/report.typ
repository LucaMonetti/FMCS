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

  #text(size: 12pt, context document.author.first()) \

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

That leads to two possible outcome:
- Invariant Holds: if the algorithm explores all the reachable states without finding one in which $not phi$ is `True` then $phi$ is an invariant of the model.
- Violation: if the algorithm find a reachable state where $not phi$ holds then the property $phi$ is not an invariant.


== Implementation

The verification process begins with the conversion of the specification `spec` into a BDD using the provided function `spec_to_bdd(model, spec)`. This allows for the application of symbolic algorithm for invariant verification.

The algorithm proceeds through the following phases:
- The sets `reach` and `new` are initialized with the model's initial states.
- At each iteration, the set `new` is evaluated. If `new` is empty or violates the specification $phi$ then the exploration is complete.
- If no violations are found and `new` is not empty the algorithm computes the post-image of `new` removing all the already checked states. The newly discovered states are included in `reach`.
- After the last iteration of the loop there are 2 cases:
  - If there is an invalid state inside `new` then the algorithm returns `False` and computes a counter-example.
  - If `new` is empty the specification $phi$ holds for every reachable state; therefore, it is an invariant.

```python
def check_explain_inv_spec(spec):
    # 1. Setup the bdds
    model = pynusmv.glob.prop_database().master.bddFsm  # Model fsm

    spec_bdd = spec_to_bdd(model, spec)                 # Bdd of spec
    negated_spec_bdd = -spec_bdd                        # Bdd of ~spec

    # 2. Explore the regions
    reach = model.init                                  # Already explored states
    new = model.init                                    # States to explore

    trace = [reach]                                     # Trace used to save the execution

    while new.isnot_false() and not new.intersected(negated_spec_bdd):

        new = model.post(new) - reach                   # Remove already checked states
        reach = reach + new                             # Add new states to reach

        trace.append(new)                               # Add reached region to trace

    if (not new.intersected(negated_spec_bdd)):
        # The formula is satisfied on every reachable state
        return (True, None) 
    
    # 3. Build the counter-example
    invalid_states = new * negated_spec_bdd             # States in new that violate the spec
    target = model.pick_one_state(invalid_states)       # State that violate the spec
    
    counter_example = compute_counter_example(model, target, trace) 

    # The property is not an invariant, return a counter-example
    return (False, tuple(counter_example))
```

=== Counter example generation

When a specification is violated, a counter-example must be provided to demonstrate the failure.

The algorithm maintains a `trace` list where each element represents the region reached on that iteration starting from the previous one. The execution is then reconstructed via backwards traversal.

The function `compute_counter_example(model, trace, spec)` implements this operation throught the following steps:
- The algorithm pick a state `current` from the set of invalid states, computed by the intersection `trace[-1] * spec`, and insert it into the `counter_example` list.
- The `trace` is then traversed in reverse starting from the second to last element. At each iteration one state is selected from the current region and added, with the curresponding input, to `counter_example`.
- The procedure returns a valid execution of the model that leads to an invalid state.

```python
def compute_counter_example(model, trace, neg_spec):
    invalid_states = trace[-1] * neg_spec                           # States that violate spec
    current = model.pick_one_state(invalid_states)              # Current considered value

    pre_states = model.pre(current)   # Compute states that can reach current in one step  
    counter_example = [current.get_str_values()]

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
The algorithm is composed by two main loops:
- Reachable state exploration
- Counter-example generation

The correctness of each phase is demonstrated using the Loop invariant technique.

=== Exploration of the reachable states

The exploration phase identifies all the reachable states while checking for property violations.

==== Loop invariants

Three invariants are maintained throughout the execution in the first loop:
- `reach`: representing the region of all the already reached states without duplicates.
- `new`: represent the region of all the newly found reachable states.
- `trace`: an ordered list where each element represents a regions of all the states reached at each iteration.

==== Base case
Initially `reach`,`new` and `trace` are initialized with the initial states of the model, therefore all invariants hold.

==== Inductive step
The loop condition checks if `new` is not empty, in that case there are still new states to explore and the loop body is executed.

For each iteration $i$:
- `new` is updated by computing the post-image of the previous `new` and subtracting all the states that are already present in `reach`. Therefore `new` contains only states reachable from the $i - 1$ iteration region that are not already in `reach`.
- `reach` is updated to include the current set `new`, therefore it contains all the reachable states found so far.
- `trace` appends the current set `new`, therefore is a list of $i + 1$ elements representing all the regions reachable from the previous region.

==== Termination
We can then see that the loop invariants hold for the base case and for the inductive case. Therefore by induction the loop invariants hold for each iteration of the loop.

Since we are dealing with a finite state model the algorithm will eventually explore all the reachable states. Therefore there are only two possible execution:

+ `new` becomes empty, all the reachable states have been explored and none of them violate the specification, so the algorithm returns `(True, None)`.
+ `new` intersected with `neg_spec_bdd` is not empty, there exists at least one newly reached state that violates the specification $phi$, so the algorithm returns `False` along with a counter-example.

=== Counter-example generation

If a violation is detected, a second loop reconstructs a valid execution path from one initial state to the violating state.

==== Loop invariant

Two invariants are maintained throughout the execution in the second loop:
- `counter_example`: a list of alternating states and inputs representing a valid execution of the system that lead to a invalid state.
- `current`: the current state being added to the counter-example list.

==== Base case
Initially `current` is initialized with a state picked from the set of invalid states, therefore it is a state that violates the specification. The `counter_example` list is initialized with this state. Therefore the invariants hold.

==== Inductive step
The algorithm iterate backwards through the `trace` list, starting from the second to last element. At each step $i$:
- A predecessor state is selected from a list of states that are in `trace[i]` and can reach `current` in one transition.
- `counter_example` is updated by prepending this predecessor and the corresponding input.
- `current` is updated to this predecessor.

==== Termination
The invariants hold for the base case and for the inductive case. Therefore by induction the loop invariants hold for each iteration of the loop.

The trace list is finite, since the model is finite and the algorithm explores only reachable states. Therefore the loop will terminate after a finite number of steps. There are only one possible execution: the algorithm returns the `counter_example` list.

#pagebreak()

= Part 2

== Assignment

The second part of the assignment request the implementation of a symbolic algorithm for the verification of a specific class of LTL formulas called _response formulas_. They have a specific form:

$ square (f -> diamond g) $

Both $f$ and $g$ are Boolean combinations of base formulas with no temporal operators.

In the following pages will be described an implementation of the function `check_examplain_response_spec(spec)` that respect the following specification:

- Check if the given `spec` is satisfied by the loaded SMV model
- The return value is a `tuple` of 2 elemens:
  - The first element is a Boolean value that is `True` if the formula is satisfied, `False` otherwise
  - The second element is `None` is the formula is satisfied but contains a counter-example otherwise.
- The counter-example take the form of a tuple of alternating states and input, ending with a state.
- If the execution is looping the last state should be present somewhere else in the sequence.

== Logic

We are dealing with a _response formula_ that we can explain such as:

#align(center, [_Every time that $f$ happens, $g$ must eventually happen at the same time or afterwards._])

Being a reactive property, and therefore happens over an infinite computation, to prove that the formula is not satisfied we must provide a counter-example in witch the negation is true. A path in witch $f$ holds but $g$ never happens again. For that we need 2 parts:

+ *Prefix*: A sequence of states leading to $f$
+ *Loop*: An infinite cycle in witch $g$ is always `false`.

== Implementation

The check of the formula structure was already done by the function `parse(spec)`, so we can just use it and check if the result is a valid `tuple` of $f$ and $g$ or `None`. In the second case the program shuld return `None`, beacause the formula is not a _response formula_.

After that, using the provided function `spec_to_bdd(model, spec)`, we can obtain the `bdd` generated from the two needed formulas: $f$ and $not g$.

The algorithm will operate only on the reachable states, so we get them using `model.reachable_states`. From this we can compute the variable `recur` that will contain all the possible starting point for a cycle. In our case all the reachable states in which $f$ holds and $not g$ holds.

There are two possibile execution:

+ `recur` becomes empty, there are no possible cycle, the formula holds and the algorithms return a positive result.
+ Otherwise each iteration compute the `pre_reach`, all the state that can be reach `recur` in a finite number of steps greater than $0$, and `new`, all the states that might be part of the cycle.

If a cycle is found then the algorithm will build a counter-example using the function `compute_counter_example(model, recur, pre_reach)`, which will be describe in the next section.

The loop runs until there are no more possibile candidates for a cycle.

```python
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
```

=== Counter example generation

As said before a counter-example is an execution of the system that leads to a state for wich the formula is not satisfied. It is composed of 2 parts:ù

+ *Prefix*: A sequence of states leading to $f$
+ *Loop*: An infinite cycle in witch $g$ is always `false`.

Those two parts are respectively computed by `compute_prefix` and `compute_loop`.

==== Build the path

The first computation is easy, we just need to compute a path that reach the starting node of the cycle. To do that, we start from the `model.init` set of states and we proced with the execution until we reach a `frontier` that contains that specific state.

After that we can construct the needed `tuple` visiting the array from the end to the beginning.

```python
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
```

==== Build the loop

The loop is more complex. We need to compute a loop starting from `s`, following the path through the frontiers list.

We first need to identify the smallest number of steps `k` that contains `s`. We then define 2 invariant:

- `path` -> All the possible path ending in `s` in `k` steps.
- `current` -> Last state put in the `path`.

The algorithm build the counter-example iterating backwards the `frontiers` taking one state and its corresponding input at the time.

After the last iteration `path` contains a full path ending in `s` that starts from the first `frontier` region.

Unite those 2 path togheter leads to a path starting from an initial state, reaching a state in witch $f$ holds and $not g$ holds, and lead to a cycle in witch $not g$ holds.

We can then be sure that the counter-example is built on the right way and rapresent a valid execution of the system that don't satisfies the formula.

```python
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
```
