# Matching Fiber Equivalence

## Abstract

Decompose each matching monomial fiber and count its two factors.

Square vertices choose distinct partners outside the monomial support. Linear vertices form the pairs of a fixed-point-free involution. Rebuilding the edges and their local choices proves the inverse construction.

**Theorem 1.1 (Exact Fiber Cardinality).**

Lean statement: `D5/S3/Zeros/Convolution/MatchingEquiv.card_matchingMonomialFiber`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Convolution/MatchingEquiv.card_matchingMonomialFiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The embedding count multiplies the exact factorial quotient counting cross-edge involutions, for arbitrary n, k, S and T.

**Theorem 1.2 (Division-free Count).**

Lean statement: `D5/S3/Zeros/Convolution/MatchingEquiv.card_matchingMonomialFiber_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Convolution/MatchingEquiv.card_matchingMonomialFiber_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product equality supplies the same count without natural-number division, for use in coefficient fields.

**Theorem 1.3 (Matching Coefficient).**

Lean statement: `D5/S3/Zeros/Convolution/MatchingEquiv.coeff_matchingSum_fiber`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Convolution/MatchingEquiv.coeff_matchingSum_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Formula (C) follows by casting the product count into Q. The powers of two cancel and leave only the alternating sign and factorial ratios.

## References

- Truth anchor: `D5/S3/Zeros/Convolution/MatchingEquiv.card_matchingMonomialFiber`
- Truth anchor: `D5/S3/Zeros/Convolution/MatchingEquiv.card_matchingMonomialFiber_mul`
- Truth anchor: `D5/S3/Zeros/Convolution/MatchingEquiv.coeff_matchingSum_fiber`
- Dependency: [D5/S3/Zeros/Convolution/MatchingFiber](MatchingFiber.md)
