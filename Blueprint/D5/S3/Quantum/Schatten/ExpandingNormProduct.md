# Norm products from an expanding-factor lower bound

## Abstract

Norm products from an expanding-factor lower bound.

**Theorem 1.1 (Balancing a common lower bound).**

Lean statement: `D5/S3/Quantum/Schatten/ExpandingNormProduct.sq_le_product_of_expanding_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/ExpandingNormProduct.sq_le_product_of_expanding_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix complex square matrices A and B, a unitarily invariant norm N, and a nonnegative real m. If m≤N(ATB) for every expanding T, then for every invertible W, m²≤N(AWB)N(A(W⁻¹)*B). Apply the lower bound to Tₜ=(tW+t⁻¹(W⁻¹)*)/2. The triangle inequality gives 2m≤tN(AWB)+t⁻¹N(A(W⁻¹)*B) for every positive t, and scalar optimization gives the result, including zero factors. A and B need not be diagonal or positive.

## References

- Truth anchor: `D5/S3/Quantum/Schatten/ExpandingNormProduct.sq_le_product_of_expanding_lower_bound`
- Dependency: [D5/S3/Quantum/Schatten/ExpandingAverage](ExpandingAverage.md)
- Dependency: [D5/S3/Quantum/Schatten/UINormContinuity](UINormContinuity.md)
