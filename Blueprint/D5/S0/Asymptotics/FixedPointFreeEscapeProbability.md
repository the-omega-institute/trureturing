# Fixed-Point-Free Escape Probability

## Abstract

A fixed-point-free twist gives uniform escape probability one.

**Theorem 1.1 (Fixed-point-free escape has probability one).**

$$\forall A, Y\ [\operatorname{Fintype}(A)] [\operatorname{Fintype}(Y)] [\operatorname{Nonempty}(A)] [\operatorname{Nonempty}(Y)],\ \forall f: Y\to Y,\ \operatorname{card}\left(\operatorname{Fix}\left(f\right)\right) = 0 \Rightarrow \operatorname{escapeProbability}\left(f\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/FixedPointFreeEscapeProbability.fixed_point_free_escape_probability_eq_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite nonempty types A and Y, escapeProbability is the real cardinality ratio of twisted-diagonal escaped listings to all listings. If the twist has no fixed point, this ratio is exactly one.

The proof is a thin wrapper over the exact fixed-point-free escaped-listing cardinality theorem in D5.S0.Diagonal.CaptureCount, together with the finite function-cardinality identity and elementary real division.

This is a partial closure of clause (i) of the source corollary. Its monotonicity, asymptotic, Poisson, and dense-phase clauses remain open.

## References

- Truth anchor: `D5/S0/Asymptotics/FixedPointFreeEscapeProbability.fixed_point_free_escape_probability_eq_one`
- Dependency: [D5/S0/Diagonal/CaptureCount](../Diagonal/CaptureCount.md)
