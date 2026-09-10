# Finite Slot CNF for First-Return Skeletons

## Abstract

A concrete finite CNF admits every total first-return skeleton that fits the trace, published anchors, and allocated signature budget. Unused slots remain legal.

**Definition 1.1 (Allocate the used return pairs inside a finite slot budget).**

Lean statement: `D5/S0/Certificates/SkeletonSlotCNF.slotsOfBudget`

*Formalization.* `D5/S0/Certificates/SkeletonSlotCNF.slotsOfBudget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Enumerate the existing total skeleton's used output-return pairs, embed them in the available signature slots, and fill spare slots by repeating one existing pair. SlotWitness records equations to the existing Skeleton rather than a second evaluation semantics.

**Theorem 1.2 (Local trace equations yield a satisfying assignment of generated CNF).**

Lean statement: `D5/S0/Certificates/SkeletonSlotCNF.model_to_sat`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SkeletonSlotCNF.model_to_sat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula is generated from finite trace data and fixed capacities. It includes one-hot rows, both block actions, all four output labels, root states, the start-zero-loop, and the zero-output anchor.

An intermediate signature color at each trace node factors the 10-edge clauses into a source-to-slot link and a slot-to-return implication. No reachability or symmetry-breaking condition is assumed.

**Theorem 1.3 (A total model within the signature budget satisfies the concrete formula).**

Lean statement: `D5/S0/Certificates/SkeletonSlotCNF.budget_model_has_satisfying_assignment`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SkeletonSlotCNF.budget_model_has_satisfying_assignment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The satisfying assignment and slot allocation are constructed. No caller-supplied model-to-SAT implication is an assumption. The finite-state enumeration uses classical choice only in the mathematical witness; formula generation itself is executable.

**Theorem 1.4 (Unsatisfiability excludes every model covered by the compiler).**

Lean statement: `D5/S0/Certificates/SkeletonSlotCNF.model_excluded_by_unsat`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SkeletonSlotCNF.model_excluded_by_unsat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A concrete native-CNF refutation would exclude the covered fixed-capacity models. The present module supplies no such refutation, no verified DIMACS byte translation, and no oracle-to-trace transport for the 79-power instance. Pinned Lean elaboration and axiom validation remain necessary before admission.

## References

- Truth anchor: `D5/S0/Certificates/SkeletonSlotCNF.budget_model_has_satisfying_assignment`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotCNF.model_excluded_by_unsat`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotCNF.model_to_sat`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotCNF.slotsOfBudget`
- Dependency: [D5/S0/Automata/FiniteSampleSkeletonTotalization](../Automata/FiniteSampleSkeletonTotalization.md)
