# Two-State Short-Word Sample Bound

## Abstract

Short-word two-state realizability has an alphabet-linear sample cutoff.

**Theorem 1.1 (A uniform cutoff for partial Boolean labels).**

$$\exists C \in \mathbb{N}, \forall (k: \mathbb{N}), \forall (D: \operatorname{Finset}(\operatorname{List}(\operatorname{Fin}(k)))), \forall (t: D \to \operatorname{Bool}), (\forall w \in D, \operatorname{length}(w) \leq 2) \Rightarrow (\forall E \subseteq D, \operatorname{card}(E) \leq C(k + 1) \Rightarrow \operatorname{Realizable}(k, E, t)) \Rightarrow \operatorname{Realizable}(k, D, t).$$

*Proof.* Machine-checked in Lean as `D5/S0/Automata/TwoStateShortWordSampleBound.alphabet_linear_sample_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k be any natural number, D a finite set of words over Fin k, and t a Boolean labeling of D. Suppose every word in D has length at most two. Realizable(k,E,t) means that some finite state type in Type 0, with at most two states, supports a total deterministic Boolean-output automaton agreeing with t on E. The automaton has an initial state; its acceptance set is unobserved. Labels outside E are unrestricted.

There is one natural number C, independent of k, D and t, such that realizability of every subsample E of size at most C(k+1) implies realizability of D. The proof supplies C=16. Different subsamples may use different state carriers and transition tables. The same alphabet and target labeling are used throughout.

A machine with at most two states has either constant output or injective Boolean output. In the latter case, use the output as the state coordinate; in the constant case, use a constant-output machine. Both cases give a normalized machine with initial output e and two shared transition tables x and y. Its outputs on the empty word, a singleton a, and a pair ab are e, x(a), and x(b) if x(a)=e or y(b) otherwise.

For each fixed e, the nonempty-word observations become implications on the 2k Boolean table entries, together with their contrapositives. There are 4k literal vertices. From any starting literal, repeatedly add an edge to a vertex not yet reached, retaining that edge's original observation as its source. At most one source per added vertex suffices to preserve all reachability from the start.

If no literal and its negation are mutually reachable, a linear extension of the reachability-set order produces a satisfying assignment. Otherwise, retain sparse paths in both directions between such a pair. Their observation sources form an unsatisfiable subsample with at most 8k observations. An inconsistent empty-word label instead gives a singleton obstruction. Thus each fixed e has an obstruction of size at most 8k+1 whenever that branch has no model.

Union the obstructions for e=false and e=true. Their union has at most 16k+2 observations, hence at most 16(k+1). A two-state machine fitting this union normalizes to one of those two branches and contradicts its obstruction. This proves the stated local-to-global implication. The argument includes k=0, empty domains and samples, the empty word, and one-state machines. It asserts neither optimality of 16 nor a result for longer words or larger state budgets. The implication-graph assignment method is the classical two-clause satisfiability construction; the estimate here counts original observations through the shared transition tables.

## References

- Truth anchor: `D5/S0/Automata/TwoStateShortWordSampleBound.alphabet_linear_sample_bound`
- Dependency: [D5/S0/Automata/FiniteSampleRestriction](FiniteSampleRestriction.md)
