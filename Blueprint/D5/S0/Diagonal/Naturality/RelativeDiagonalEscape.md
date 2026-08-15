# Relative Diagonal Escape

## Abstract

A fixed-point-free twist sends every diagonal listing outside its range.

**Theorem 1.1 (A fixed-point-free twist escapes every listing).**

$$\forall A, Y: \operatorname{Type},\ \forall e: A \to \left(A \to Y\right), tau: Y \to Y,\ (\forall y: Y, \operatorname{tau}\left(y\right) \neq y) \Rightarrow \neg (\operatorname{diagonal}\left(tau, e\right) \in \operatorname{range}(e)).$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Naturality/RelativeDiagonalEscape.relative_diagonal_escape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be an address type, Y a value type, e a table indexed twice by A, and tau a self-map of Y. The twisted diagonal sends each address a to tau(e(a,a)).

Assume tau has no fixed point. If the twisted diagonal were a row e(a), then evaluating that row equality at a would make e(a,a) a fixed point of tau. Therefore the twisted diagonal is outside the range of e, without finiteness assumptions on either type.

Loogle found Function.exists_fixed_point_of_surjective as a related surjectivity theorem, while LeanSearch and pinned-Mathlib searches found no full-statement match. The proof imports and applies the repository lemma EscapeCount.diagonal_landing_fixed.

## References

- Truth anchor: `D5/S0/Diagonal/Naturality/RelativeDiagonalEscape.relative_diagonal_escape`
- Dependency: [D5/S0/Diagonal/EscapeCount](../EscapeCount.md)
