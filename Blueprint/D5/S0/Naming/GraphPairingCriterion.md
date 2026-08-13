# Graph Pairing Separation Criterion

## Abstract

A graph pairing separates both curried coordinates exactly under injectivity and a one-point omission bound.

**Theorem 1.1 (Graph pairing separates both coordinates exactly under the range criterion).**

$$\forall A, B, f: A \to B,\\(\operatorname{Injective}(a \mapsto (b \mapsto f(a) = b)) \land \operatorname{Injective}(b \mapsto (a \mapsto f(a) = b))) \iff (\operatorname{Injective}(f) \land \operatorname{Subsingleton}(B \setminus \operatorname{range}(f))).$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/GraphPairingCriterion.graph_pairing_separating_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary types A and B and a function f from A to B, consider the relation that holds on (a,b) exactly when f(a) = b. Injectivity of its row curry says that distinct inputs have distinct graph rows. Injectivity of its column curry says that distinct codomain points have distinct graph columns.

Both separation properties hold exactly when f is injective and the complement of its range is a subsingleton. Thus at most one codomain point may be omitted. The forward proof reads injectivity from equal rows and compares any two omitted columns; the reverse proof uses an attained point to distinguish columns unless both lie outside the range.

This is the graph-pairing clause only. Other clauses carried by the source atom are not claimed by this deposit and remain unresolved.

## References

- Truth anchor: `D5/S0/Naming/GraphPairingCriterion.graph_pairing_separating_iff`
