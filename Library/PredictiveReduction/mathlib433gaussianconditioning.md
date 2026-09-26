---
bibkey: mathlib433gaussianconditioning
authors: The Mathlib Community
year: 2026
title: Gaussian linear images, independence and Markov disintegration in Mathlib v4.33.0
doi: null
url: https://github.com/leanprover-community/mathlib4/tree/v4.33.0/Mathlib/Probability/Distributions/Gaussian
claim: Pinned Gaussian covariance and independence theorems support an explicit conditional-law construction and extended-valued Bayes risk for arbitrary rectangular additive-noise observations.
strata_touched:
  - D5/S3/Observer/Linear/GaussianAffineDisintegration
  - D5/S3/Observer/Linear/GaussianObservationDisintegration
  - D5/S3/Observer/Linear/GaussianPosteriorRisk
license: citation-only
triage: anchor
---

# Gaussian conditioning: library-first implementation

The following v4.33.0 source APIs were inspected before the new proof sources
were written. Rolling documentation was used for discovery only.

- `Probability/Distributions/Gaussian/Multivariate.lean` constructs the actual
  Gaussian probability measure. Its integral and covariance lemmas identify
  the mean and covariance, including positive semidefinite covariances.
- `Probability/Moments/CovarianceBilin.lean` supplies covariance under bounded
  linear maps and its equality with the covariance of scalar inner products.
- `Probability/Distributions/Gaussian/CharFun.lean` supplies `IsGaussian.ext`:
  Gaussian measures with the same mean and covariance are equal.
- `Probability/Distributions/Gaussian/HasGaussianLaw/Basic.lean` and
  `Independence.lean` supply linear images of Gaussian variables and
  `HasGaussianLaw.indepFun_of_covariance_inner`. This is used after the
  observation module derives zero residual/data covariance.
- `Probability/Kernel/Composition/Prod.lean`, `MapComap.lean` and
  `MeasureCompProd.lean` construct deterministic/constant kernel products,
  their maps and their composition-products with probability measures.
- `Probability/Kernel/Disintegration/Basic.lean` supplies the actual
  `Measure.IsCondKernel` predicate. The constructed observation kernel is
  proved to satisfy its measure identity; it is not introduced by assuming
  a posterior-distribution certificate.
- `Data/Matrix/ColumnRowPartitioned.lean` supplies the block multiplication
  identities used to calculate the original state/noise law and innovation.

## Specific construction

For beta>0 and noise precision tau>0, the source starts with a Gaussian on
state-plus-noise coordinates with covariance diag(beta^-1 I,tau^-1 I).
The two marginal Gaussian laws and their independence are established.
With Sigma=(beta I+tau M^T M)^-1, K=tau Sigma M^T and residual readout
[beta Sigma,-K], the inverse identity gives X=K Y+R, Cov(R,Y)=0 and
Cov(R)=Sigma. Gaussian independence then gives the actual product residual
law, and an explicit affine Markov kernel disintegrates the observed joint law.
The resulting kernel is identified pointwise with the earlier candidateLaw.

## Extended-valued Bayes risk

`Probability/Moments/Variance.lean` supplies `variance_eq_sub`,
`variance_sub_const` and the square-integrability API used to derive each
conditional coordinate moment. The Gaussian coordinate means and variances
come from the actual constructed law, not from a supplied moment certificate.
`EuclideanSpace.norm_sq_eq` identifies the coordinate loss with physical
Euclidean squared energy. `Measure.lintegral_compProd` supplies Tonelli for
the constructed posterior kernel. The conversion of the conditional real
integral to `ENNReal` occurs only after proving conditional integrability
and nonnegativity.

The resulting risk identity holds for all measurable estimators, with no
finite-risk assumption. A finite covariance baseline can be cancelled to
prove the almost-everywhere uniqueness of the posterior mean. Orthogonal
propagation is handled by an actual linear isometric equivalence and its
inverse, yielding a correspondence of all competing estimators.

These Gaussian conditioning and risk statements are classical mathematics,
with no new-priority claim. Their role is to close source-level gaps left by
PR8899. No new Lean source in this delivery has yet been elaborated or
kernel-verified. Finite numerical and exact arithmetic checks are reported
separately; they are not formal verification.
