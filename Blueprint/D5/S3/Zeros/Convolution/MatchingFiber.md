# Matching Monomial Fibers

## Abstract

Elementary symmetric fibers and a partial matching-coefficient reduction at arbitrary degree.

MatchingIdentity is an unproved proposition. The module proves the elementary symmetric product fiber formula and reduces matching coefficients to a signed fiber cardinality. It also constructs the injection assigning unused partners to squared vertices. The perfect-matching correspondence, complete fiber count, and all-degree matching identity are not proved.

**Theorem 1.1 (Symmetrization Coefficient).**

Lean statement: `D5/S3/Zeros/Convolution/MatchingFiber.symmetrize_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Convolution/MatchingFiber.symmetrize_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 2k <= n, the coefficient of degree n-2k is expressed through the frozen additive-convolution definitions and descending factorials.

**Theorem 1.2 (Elementary Product Fiber).**

Lean statement: `D5/S3/Zeros/Convolution/MatchingFiber.coeff_esymm_mul_fiber`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Convolution/MatchingFiber.coeff_esymm_mul_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For disjoint S and T, the exponent-two/exponent-one coefficient of e_i e_j is choose(|T|,i-|S|) when both lower bounds and total degree agree, and is zero otherwise. The proof constructs inverse subset-pair maps.

**Theorem 1.3 (Matching Coefficient Reduction).**

Lean statement: `D5/S3/Zeros/Convolution/MatchingFiber.coeff_matchingSum_eq_card_fiber`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Convolution/MatchingFiber.coeff_matchingSum_eq_card_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prescribed matching coefficient equals (-2)^(k-|S|) times the cardinality of its decorated-matching fiber. A square-choice bijection proves the weight is constant. The remaining cardinality is not evaluated.

**Theorem 1.4 (Ordered Partner Assignments).**

Lean statement: `D5/S3/Zeros/Convolution/MatchingFiber.card_partner_embeddings`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Convolution/MatchingFiber.card_partner_embeddings` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib counts embeddings from S to the complement of S union T by the corresponding descending factorial. This is one factor in the proposed matching-fiber count, not a proof of the full count.

## References

- Truth anchor: `D5/S3/Zeros/Convolution/MatchingFiber.card_partner_embeddings`
- Truth anchor: `D5/S3/Zeros/Convolution/MatchingFiber.coeff_esymm_mul_fiber`
- Truth anchor: `D5/S3/Zeros/Convolution/MatchingFiber.coeff_matchingSum_eq_card_fiber`
- Truth anchor: `D5/S3/Zeros/Convolution/MatchingFiber.symmetrize_coefficient`
- Dependency: [D5/S3/Zeros/Convolution/FiniteConvolutionCoefficients](FiniteConvolutionCoefficients.md)
- Dependency: [D5/S3/Zeros/Convolution/PerfectMatchingCount](PerfectMatchingCount.md)
