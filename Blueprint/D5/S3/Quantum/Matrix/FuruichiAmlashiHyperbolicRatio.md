# The Furuichi–Eghbali Amlashi hyperbolic ratio

## Abstract

The logarithmic mean hyperbolic ratio below parameter one.

**Definition 1.1 (The ratio).**

Lean statement: `D5/S3/Quantum/Matrix/FuruichiAmlashiHyperbolicRatio.phi`

*Formalization.* `D5/S3/Quantum/Matrix/FuruichiAmlashiHyperbolicRatio.phi` (`✓ std3`).

*Citation.* S. Furuichi and M. Eghbali Amlashi (2024). *On bounds of logarithmic mean and mean inequality chain*. DOI: [10.7153/mia-2024-27-27](https://doi.org/10.7153/mia-2024-27-27). URL: <https://arxiv.org/abs/2203.01134>.

*Commentary.*

For real r and t, phi(r,0)=1 and phi(r,t)=t (cosh t)^(1-r)/sinh t when t is nonzero. The power is the real power of the strictly positive real number cosh t.

**Definition 1.2 (The conjectured parameter range).**

Lean statement: `D5/S3/Quantum/Matrix/FuruichiAmlashiHyperbolicRatio.claim`

*Formalization.* `D5/S3/Quantum/Matrix/FuruichiAmlashiHyperbolicRatio.claim` (`✓ std3`).

*Citation.* S. Furuichi and M. Eghbali Amlashi (2024). *On bounds of logarithmic mean and mean inequality chain*. DOI: [10.7153/mia-2024-27-27](https://doi.org/10.7153/mia-2024-27-27). URL: <https://arxiv.org/abs/2203.01134>.

*Commentary.*

For every real r below one, the complex cast of phi(r,t) fails positive definiteness: some finite real family has a matrix with entries phi(r,x(j)-x(i)) that is not positive semidefinite.

**Theorem 1.3 (Nonpositive definiteness below one).**

Lean statement: `D5/S3/Quantum/Matrix/FuruichiAmlashiHyperbolicRatio.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/FuruichiAmlashiHyperbolicRatio.result` (`✓ std3`). ∎

*Resolves.* `Problems/furuichi-eghbali-amlashi-2022-hyperbolic-ratio-not-positive-definite` (proved) by `D5/S3/Quantum/Matrix/FuruichiAmlashiHyperbolicRatio.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"furuichi-eghbali-amlashi-2022-hyperbolic-ratio-not-positive-definite","declaration_gid":"D5/S3/Quantum/Matrix/FuruichiAmlashiHyperbolicRatio.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* S. Furuichi and M. Eghbali Amlashi (2024). *On bounds of logarithmic mean and mean inequality chain*. DOI: [10.7153/mia-2024-27-27](https://doi.org/10.7153/mia-2024-27-27). URL: <https://arxiv.org/abs/2203.01134>.

*Commentary.*

The full claim holds. Set a=1-r>0. The extension F(z)=exp(a Log(cosh z))/dslope(sinh,0,z) is holomorphic on the open disk of radius pi/2. In this disk the real part of cosh z is positive, so the logarithm is holomorphic, and the divided slope of sinh has no zero. On the real diameter F agrees with phi. At iy for 0<y<pi/2 it equals y (cos y)^a/sin y, which tends to zero as y increases to pi/2. Positive definiteness would force these values to be at least phi(r,0)=1, a contradiction.

The source supplies the conjecture and the positive parameter range r at least one. This proof establishes the negative range for the stated scalar positive definite kernel. The operator-mean ordering consequence uses the external Hiai–Kosaki criterion and is not an additional formal theorem in this module.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/FuruichiAmlashiHyperbolicRatio.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/FuruichiAmlashiHyperbolicRatio.phi`
- Truth anchor: `D5/S3/Quantum/Matrix/FuruichiAmlashiHyperbolicRatio.result`
- Dependency: [D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis](../../Analytic/Fourier/PositiveDefiniteImaginaryAxis.md)
