# The finite reciprocal Möbius floor inverse

## Abstract

The finite reciprocal Möbius floor inverse

**Theorem 1.1 (Exact finite floor integral).**

Lean statement: `D5/S3/Weil/ZetaPntBounds/ReciprocalMoebiusFloorInverse.floorIntegral_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaPntBounds/ReciprocalMoebiusFloorInverse.floorIntegral_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write Q(u) for the sum of μ(n)/n over positive integers n ≤ u. For real cutoffs P ≥ 1 and 0 ≤ x ≤ P, the integral of Q(u) times ⌊x/u⌋ over 1 ≤ u ≤ P is max(x − 1, 0). The identity includes P = 1 and the range x < 1.

Expand Q as a finite sum of cutoff indicators. In the term indexed by n, substitute u = n v to cancel the factor 1/n. The transformed terms can all be integrated to P because their added tails vanish. The Möbius floor cancellation turns the resulting integrand into the indicator of v ≤ x, whose integral gives the truncated linear function.

## References

- Truth anchor: `D5/S3/Weil/ZetaPntBounds/ReciprocalMoebiusFloorInverse.floorIntegral_eq`
- Dependency: [D5/S3/Arith/MoebiusLogarithmic/ReciprocalBound](../../Arith/MoebiusLogarithmic/ReciprocalBound.md)
