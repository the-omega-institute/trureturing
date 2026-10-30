# Spherical energy definitions

## Abstract

Multivariate spherical energies and their averaged pair kernels.

**Definition 1.1 (Normalized surface measure).**

Lean statement: `D5/S3/Analytic/MultivariateEnergy/Defs.sigma`

*Formalization.* `D5/S3/Analytic/MultivariateEnergy/Defs.sigma` (`✓ std3`).

*Citation.* D. Bilyk, D. Ferizović, A. Glazyrin, R. Matzke, J. Park, O. Vlasiuk (2022). *Potential theory with multivariate kernels*. DOI: [10.1007/s00209-022-03000-z](https://doi.org/10.1007/s00209-022-03000-z). URL: <https://arxiv.org/abs/2104.03410>.

*Commentary.*

The unit sphere is the subtype of real Euclidean space consisting of vectors of norm one. Normalized surface measure is the radial spherical measure of volume, scaled by the inverse of its total mass.

**Definition 1.2 (Multivariate energy).**

Lean statement: `D5/S3/Analytic/MultivariateEnergy/Defs.energy`

*Formalization.* `D5/S3/Analytic/MultivariateEnergy/Defs.energy` (`✓ std3`).

*Citation.* D. Bilyk, D. Ferizović, A. Glazyrin, R. Matzke, J. Park, O. Vlasiuk (2022). *Potential theory with multivariate kernels*. DOI: [10.1007/s00209-022-03000-z](https://doi.org/10.1007/s00209-022-03000-z). URL: <https://arxiv.org/abs/2104.03410>.

*Commentary.*

The energy of a kernel at a Borel measure is its integral against the product measure with that same measure in every input.

**Definition 1.3 (The averaged pair kernel).**

Lean statement: `D5/S3/Analytic/MultivariateEnergy/Defs.avgKernel`

*Formalization.* `D5/S3/Analytic/MultivariateEnergy/Defs.avgKernel` (`✓ std3`).

*Citation.* D. Bilyk, D. Ferizović, A. Glazyrin, R. Matzke, J. Park, O. Vlasiuk (2022). *Potential theory with multivariate kernels*. DOI: [10.1007/s00209-022-03000-z](https://doi.org/10.1007/s00209-022-03000-z). URL: <https://arxiv.org/abs/2104.03410>.

*Commentary.*

All inputs except the last two are integrated against normalized surface measure. The last two inputs remain free.

**Definition 1.4 (Conditional positive definiteness).**

Lean statement: `D5/S3/Analytic/MultivariateEnergy/Defs.IsCondPosDef`

*Formalization.* `D5/S3/Analytic/MultivariateEnergy/Defs.IsCondPosDef` (`✓ std3`).

*Citation.* D. Bilyk, D. Ferizović, A. Glazyrin, R. Matzke, J. Park, O. Vlasiuk (2022). *Potential theory with multivariate kernels*. DOI: [10.1007/s00209-022-03000-z](https://doi.org/10.1007/s00209-022-03000-z). URL: <https://arxiv.org/abs/2104.03410>.

*Commentary.*

The quadratic expression is nonnegative for the difference of any two finite positive Borel measures of equal mass. By Jordan decomposition this is exactly the condition for finite signed measures of total mass zero.

**Definition 1.5 (Admissible kernels).**

Lean statement: `D5/S3/Analytic/MultivariateEnergy/Defs.IsAdmissible`

*Formalization.* `D5/S3/Analytic/MultivariateEnergy/Defs.IsAdmissible` (`✓ std3`).

*Citation.* D. Bilyk, D. Ferizović, A. Glazyrin, R. Matzke, J. Park, O. Vlasiuk (2022). *Potential theory with multivariate kernels*. DOI: [10.1007/s00209-022-03000-z](https://doi.org/10.1007/s00209-022-03000-z). URL: <https://arxiv.org/abs/2104.03410>.

*Commentary.*

A kernel is continuous, invariant under permutations of the inputs, and invariant under every orthogonal transformation of the sphere. The counterexample satisfies this stronger invariance, hence also invariance under rotations.

**Definition 1.6 (Energy minimization).**

Lean statement: `D5/S3/Analytic/MultivariateEnergy/Defs.IsMinimizer`

*Formalization.* `D5/S3/Analytic/MultivariateEnergy/Defs.IsMinimizer` (`✓ std3`).

*Citation.* D. Bilyk, D. Ferizović, A. Glazyrin, R. Matzke, J. Park, O. Vlasiuk (2022). *Potential theory with multivariate kernels*. DOI: [10.1007/s00209-022-03000-z](https://doi.org/10.1007/s00209-022-03000-z). URL: <https://arxiv.org/abs/2104.03410>.

*Commentary.*

A minimizing measure has energy no greater than that of every Borel probability measure.

**Definition 1.7 (The averaged pair characterization).**

Lean statement: `D5/S3/Analytic/MultivariateEnergy/Defs.claim`

*Formalization.* `D5/S3/Analytic/MultivariateEnergy/Defs.claim` (`✓ std3`).

*Citation.* D. Bilyk, D. Ferizović, A. Glazyrin, R. Matzke, J. Park, O. Vlasiuk (2022). *Potential theory with multivariate kernels*. DOI: [10.1007/s00209-022-03000-z](https://doi.org/10.1007/s00209-022-03000-z). URL: <https://arxiv.org/abs/2104.03410>.

*Commentary.*

For every dimension at least two and every arity at least three, normalized surface measure minimizes an admissible kernel exactly when the averaged pair kernel is conditionally positive definite. The orthogonally invariant class contains the counterexample to the source assertion, whether rotations are interpreted as the special or full orthogonal group.

**Theorem 1.8 (Surface measure is a probability measure).**

Lean statement: `D5/S3/Analytic/MultivariateEnergy/Defs.sigma_isProbabilityMeasure`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MultivariateEnergy/Defs.sigma_isProbabilityMeasure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive dimension the spherical measure has finite nonzero total mass, so inverse-mass scaling gives total mass one.

**Definition 1.9 (The three-input centered family).**

Lean statement: `D5/S3/Analytic/MultivariateEnergy/Defs.familyKernel`

*Formalization.* `D5/S3/Analytic/MultivariateEnergy/Defs.familyKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Put A(x)=xx transpose minus I/d, L(x,y)=tr(A(x)A(y)), and T(x,y,z)=tr(A(x)A(y)A(z)). The three-input kernel is beta divided by three times the sum of its three pair traces, minus its triple trace.

## References

- Truth anchor: `D5/S3/Analytic/MultivariateEnergy/Defs.IsAdmissible`
- Truth anchor: `D5/S3/Analytic/MultivariateEnergy/Defs.IsCondPosDef`
- Truth anchor: `D5/S3/Analytic/MultivariateEnergy/Defs.IsMinimizer`
- Truth anchor: `D5/S3/Analytic/MultivariateEnergy/Defs.avgKernel`
- Truth anchor: `D5/S3/Analytic/MultivariateEnergy/Defs.claim`
- Truth anchor: `D5/S3/Analytic/MultivariateEnergy/Defs.energy`
- Truth anchor: `D5/S3/Analytic/MultivariateEnergy/Defs.familyKernel`
- Truth anchor: `D5/S3/Analytic/MultivariateEnergy/Defs.sigma`
- Truth anchor: `D5/S3/Analytic/MultivariateEnergy/Defs.sigma_isProbabilityMeasure`
