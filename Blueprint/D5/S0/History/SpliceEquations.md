# Splice Equations

## Abstract

Marker-history splicing follows the recursion on its second history.

**Theorem 1.1 (Splicing is determined recursively on the second history).**

$$(\forall h: MarkerHistory, \operatorname{splice}\left(h, 1\right) = h) \land (\forall epsilon: Marker, h, g: MarkerHistory, \operatorname{splice}\left(h, \operatorname{of}\left(epsilon\right) \times g\right) = \operatorname{of}\left(epsilon\right) \times \operatorname{splice}\left(h, g\right)).$$

*Proof.* Machine-checked in Lean as `D5/S0/History/SpliceEquations.splice_recursion_equations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every marker history h, splicing the empty history on the right returns h.

For every marker epsilon and histories h and g, prefixing epsilon to the second argument prefixes the same marker to the splice. The two universally quantified equalities are asserted together.

A history is read from its last inserted marker to its first. Insertion at the end of the underlying list therefore prefixes the displayed word. Concatenating the two underlying lists in insertion order places the second displayed history before the first.

`D5/S0/History/SpliceEquations` also carries a computational witness: splicing two one-marker histories yields the two-marker history whose leading marker comes from the second argument. The witness holds by reduction of the concatenation recursion.

## References

- Truth anchor: `D5/S0/History/SpliceEquations.splice_recursion_equations`
