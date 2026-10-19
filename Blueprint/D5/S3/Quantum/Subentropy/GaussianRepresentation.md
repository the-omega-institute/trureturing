# Diagonal Gaussian Laplace transform

## Abstract

The exact diagonal Gaussian quadratic-form Laplace transform.

Let I be finite, p_i≥0 and s≥0. The coordinates z_(i,0), z_(i,1) are independent real Gaussian random variables of mean zero and variance one, so each pair represents one standard complex Gaussian coordinate. No normalization of p is required.

**Theorem 1.1 (Independent complex-coordinate Laplace transform).**

$$\operatorname{E}\left(\operatorname{exp}\left(\operatorname{sum}\left(\frac{\left(0 - s \cdot \operatorname{p}\left(\operatorname{fst}\left(j\right)\right)\right) \cdot \operatorname{z}\left(j\right)^{2}}{2}\right)\right)\right) = \operatorname{prod}\left(\frac{1}{1 + s \cdot \operatorname{p}\left(i\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/GaussianRepresentation.diagonal_gaussian_laplace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quadratic form in the exponential is −Σ_(i,k) s p_i z_(i,k)^2/2. For one real coordinate with coefficient c≥0, rewrite the Gaussian expectation using gaussianPDFReal and combine the exponentials. Mathlib integral_gaussian evaluates the resulting integral. Squaring the answer gives 1/(1+c). Finite product integration pairs the two equal factors for every i, yielding ∏_i(1+s p_i)^(−1). This is the diagonal Laplace transform only. Identification of the entropy expectation with the determinant-integral subentropy remains a separate mathematical obligation.

## References

- Truth anchor: `D5/S3/Quantum/Subentropy/GaussianRepresentation.diagonal_gaussian_laplace`
