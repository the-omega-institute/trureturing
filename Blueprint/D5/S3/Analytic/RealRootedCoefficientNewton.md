# Strong Newton inequalities for real split polynomials

## Abstract

Real splitting gives strong coefficient Newton inequalities.

**Theorem 1.1 (Strong Newton inequality at every coefficient).**

Lean statement: `D5/S3/Analytic/RealRootedCoefficientNewton.split_polynomial_coefficient_newton`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/RealRootedCoefficientNewton.split_polynomial_coefficient_newton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Teemu Lundström and Leonardo Saud Maia Leite (2025). *Order polytopes of crown posets*. DOI: [10.48550/arXiv.2504.05123](https://doi.org/10.48550/arXiv.2504.05123). URL: <https://arxiv.org/abs/2504.05123v3>.

*Commentary.*

For every real polynomial p that splits over the reals and every natural k, (k+1) times the square of coefficient k+1 is at least (k+2) times the product of coefficients k and k+2. No nonnegativity, simplicity of roots, nonzero polynomial or degree bound is assumed. This is the strong unnormalized coefficient form of the classical Newton inequalities; it is not a claim of a new classical inequality.

Rolle's root-count theorem with multiplicities proves that derivatives of split real polynomials split. Induction on products of real linear and constant factors proves Laguerre positivity at every real point. Evaluating this at zero and inducting on derivatives proves the coefficient inequality with the factorial factors. Applied to the auxiliary scalar polynomial, this gives the Newton inequalities used in the crown log-concavity theorem. The coefficient inequality omits the extra finite-degree factor of the degree-sharp normalized Newton inequalities.

## References

- Truth anchor: `D5/S3/Analytic/RealRootedCoefficientNewton.split_polynomial_coefficient_newton`
