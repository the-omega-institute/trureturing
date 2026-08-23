# Nonempty Diagonal Capture Intersections

## Abstract

A nonempty finite row set has an exact simultaneous twisted-diagonal capture count.

**Lemma 1.1 (Nonempty capture intersections have an exact cardinality).**

$$\left(\left(\left(\left(\operatorname{card}\left(\mathit{Address}\right) = A \land \operatorname{card}\left(Y\right) = n\right) \land \operatorname{card}\left(\operatorname{Fix}\left(f\right)\right) = k\right) \land \operatorname{card}\left(S\right) = s\right) \land s \ge 1\right) \Rightarrow \operatorname{card}\left(\{g : \mathit{Address} \to \left(\mathit{Address} \to Y\right) \mid \forall a \in S,\ g(a) = \operatorname{diagonal}(f, g)\}\right) = k^{s} \cdot n^{A \cdot \left(A - s\right)}$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/CaptureIntersectionCardinality.capture_intersection_cardinality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Address and Y be finite types, let f map Y to itself, and let S be a finite set of addresses. Write A for the cardinality of Address, n for the cardinality of Y, k for the number of fixed points of f, and s for the cardinality of S. When s is at least one, the number of listings g whose selected rows all equal the twisted diagonal of g is exactly k^s times n^(A*(A-s)).

The proof reuses the general finite capture-count equivalence from CaptureCount and only substitutes the four named cardinalities. The positivity assumption reproduces the source lemma's domain; the underlying count theorem also holds for an empty selection.

## References

- Truth anchor: `D5/S0/Diagonal/CaptureIntersectionCardinality.capture_intersection_cardinality`
- Dependency: [D5/S0/Diagonal/CaptureCount](CaptureCount.md)
