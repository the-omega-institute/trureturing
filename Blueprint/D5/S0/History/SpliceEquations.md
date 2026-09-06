# Splice Equations

## Abstract

Marker-history splicing is pinned by its defining recursion, not by a library alias.

**Theorem 1.1 (Splicing is determined recursively on the second history).**

$$(\forall h: MarkerHistory, \operatorname{splice}\left(h, 1\right) = h) \land (\forall epsilon: Marker, h, g: MarkerHistory, \operatorname{splice}\left(h, \operatorname{of}\left(epsilon\right) \times g\right) = \operatorname{of}\left(epsilon\right) \times \operatorname{splice}\left(h, g\right)).$$

*Proof.* Machine-checked in Lean as `D5/S0/History/SpliceEquations.splice_recursion_equations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every marker history h, splicing the empty history on the right returns h.

For every marker epsilon and histories h and g, prefixing epsilon to the second argument prefixes the same marker to the splice. The two universally quantified equalities are asserted together.

The marker-history carrier defines splicing through the free-monoid product. That definition is compact, but on its own it leaves a reader unable to check that the operation is the intended one: any product-shaped alias would typecheck equally well.

The theorem `splice_recursion_equations` states the two equations that determine splicing on its second argument. The empty history is the right unit, and prefixing a marker to the second argument prefixes the same marker to the result. Together they characterize the operation recursively, so the carrier's definition is verified against the intended recursion rather than assumed to implement it.

`D5/S0/History/SpliceEquations` also carries a computational witness: splicing two one-marker histories yields the two-marker history whose leading marker comes from the second argument. The witness holds by reduction, so it exercises the definition itself rather than a restatement of it.

## References

- Truth anchor: `D5/S0/History/SpliceEquations.splice_recursion_equations`
- Dependency: [D5/S0/History/HistoryCarrier](HistoryCarrier.md)
