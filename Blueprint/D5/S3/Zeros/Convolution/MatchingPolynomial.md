# Matching Polynomial Formula

## Abstract

Assemble the monomial-fiber counts into formula (star).

All contributing exponent vectors have total degree 2k and entries at most two. Each is a disjoint square/linear fiber. The two coefficient formulas and the alternating factorial sum therefore determine the entire polynomial.

**Theorem 1.1 (Denominator Product).**

Lean statement: `D5/S3/Zeros/Convolution/MatchingPolynomial.matchingSum_esymm_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Convolution/MatchingPolynomial.matchingSum_esymm_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying the matching sum by (n-2k)! times (n-k)! gives the explicit signed elementary-symmetric numerator.

**Theorem 1.2 (Formula (star)).**

Lean statement: `D5/S3/Zeros/Convolution/MatchingPolynomial.matchingSum_esymm`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Convolution/MatchingPolynomial.matchingSum_esymm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The factorial denominator is nonzero in Q, giving the scalar-quotient form for every n and k with 2k at most n.

**Theorem 1.3 (Matching Identity).**

Lean statement: `D5/S3/Zeros/Convolution/MatchingPolynomial.matching_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Convolution/MatchingPolynomial.matching_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluation in R, Mathlib Vieta, and the symmetrization coefficient formula prove the complete MatchingIdentity for every admissible n and k.

## References

- Truth anchor: `D5/S3/Zeros/Convolution/MatchingPolynomial.matchingSum_esymm`
- Truth anchor: `D5/S3/Zeros/Convolution/MatchingPolynomial.matchingSum_esymm_mul`
- Truth anchor: `D5/S3/Zeros/Convolution/MatchingPolynomial.matching_identity`
- Dependency: [D5/S3/Zeros/Convolution/AlternatingFactorialSum](AlternatingFactorialSum.md)
- Dependency: [D5/S3/Zeros/Convolution/MatchingEquiv](MatchingEquiv.md)
