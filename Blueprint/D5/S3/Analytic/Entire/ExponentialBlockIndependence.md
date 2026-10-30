# Independent exponential-polynomial blocks

## Abstract

Independent exponential-polynomial blocks.

**Theorem 1.1 (Independent exponential-polynomial blocks).**

Lean statement: `D5/S3/Analytic/Entire/ExponentialBlockIndependence.block_evaluation_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Entire/ExponentialBlockIndependence.block_evaluation_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite index type and injective family of arbitrary complex exponents, the complex-linear map sending a tuple of polynomials to the sum exp(alpha_i*z)*P_i(z) is injective on the whole complex plane. Polynomial degrees and coefficients are unrestricted.

The actual scalar derivative minus alpha maps an exponential block to the corresponding polynomial derivative. Each block therefore belongs to the generalized eigenspace of the actual entire derivative at alpha. Independence of generalized eigenspaces for distinct eigenvalues proves that no nonzero polynomial block can cancel another exponent block.

A finite exponential-polynomial presentation is regrouped by its actual exponents, with exactly zero polynomial blocks removed. An algebraic left inverse of the injective evaluation map gives block projections on all complex-valued functions. Their weighted-kernel identities select one exponent in either variable, including when the candidate separated factors are arbitrary entire functions. These projections are consumed in the distinct-block rank obstruction.

## References

- Truth anchor: `D5/S3/Analytic/Entire/ExponentialBlockIndependence.block_evaluation_injective`
- Dependency: [D5/S3/Analytic/Entire/ExponentialPolynomial](ExponentialPolynomial.md)
