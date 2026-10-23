# Spherical moments

## Abstract

Orthogonal invariance and second moments of normalized spherical measure.

**Theorem 1.1 (Orthogonal invariance of surface measure).**

Lean statement: `D5/S3/Analytic/MultivariateEnergy/Moments.measurePreserving_sphereAction`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MultivariateEnergy/Moments.measurePreserving_sphereAction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every real linear isometric equivalence preserves normalized surface measure. The radial cones of transformed spherical sets are the corresponding transformed radial cones. Volume preservation therefore implies preservation of the spherical measure and its normalization.

**Theorem 1.2 (Continuity of the centered matrix feature).**

Lean statement: `D5/S3/Analytic/MultivariateEnergy/Moments.continuous_A`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MultivariateEnergy/Moments.continuous_A` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each entry of the centered rank-one matrix is a product of two coordinates minus a constant, so the matrix feature is continuous.

**Theorem 1.3 (Integrability for finite measures).**

Lean statement: `D5/S3/Analytic/MultivariateEnergy/Moments.integrable_A`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MultivariateEnergy/Moments.integrable_A` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unit sphere is compact. Every entry of the continuous matrix feature is consequently integrable against any finite Borel measure, and coordinatewise integrability gives matrix integrability.

**Theorem 1.4 (The exact spherical second moment).**

Lean statement: `D5/S3/Analytic/MultivariateEnergy/Moments.integral_coord_mul_coord`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MultivariateEnergy/Moments.integral_coord_mul_coord` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive dimension d, the integral of x(i)x(j) against normalized surface measure is zero for distinct coordinates and is 1/d for equal coordinates. Reflection in one coordinate gives the vanishing off-diagonal entries. Coordinate transpositions make all diagonal entries equal, while their sum is the integral of the squared norm, hence one.

**Theorem 1.5 (The centered feature has zero average).**

Lean statement: `D5/S3/Analytic/MultivariateEnergy/Moments.integral_A_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MultivariateEnergy/Moments.integral_A_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integral of xx transpose is I/d. Subtracting I/d entrywise therefore gives zero matrix average for the centered feature A.

**Theorem 1.6 (The pair trace polynomial).**

Lean statement: `D5/S3/Analytic/MultivariateEnergy/Moments.L_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MultivariateEnergy/Moments.L_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pair trace is the square of the Euclidean inner product minus 1/d.

**Theorem 1.7 (The triple trace polynomial).**

Lean statement: `D5/S3/Analytic/MultivariateEnergy/Moments.T_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MultivariateEnergy/Moments.T_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The triple trace is the product of the three pairwise inner products, minus the sum of their squares divided by d, plus 2 divided by d squared. The polynomial exhibits full symmetry and orthogonal invariance.

**Theorem 1.8 (Admissibility of the three-input family).**

Lean statement: `D5/S3/Analytic/MultivariateEnergy/Moments.isAdmissible_familyKernel_three`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MultivariateEnergy/Moments.isAdmissible_familyKernel_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In every positive dimension and for every real beta, the three-input family is continuous, invariant under all permutations of its inputs, and invariant under every orthogonal transformation. Orthogonal invariance also implies invariance under the special orthogonal group.

## References

- Truth anchor: `D5/S3/Analytic/MultivariateEnergy/Moments.L_eq`
- Truth anchor: `D5/S3/Analytic/MultivariateEnergy/Moments.T_eq`
- Truth anchor: `D5/S3/Analytic/MultivariateEnergy/Moments.continuous_A`
- Truth anchor: `D5/S3/Analytic/MultivariateEnergy/Moments.integrable_A`
- Truth anchor: `D5/S3/Analytic/MultivariateEnergy/Moments.integral_A_eq_zero`
- Truth anchor: `D5/S3/Analytic/MultivariateEnergy/Moments.integral_coord_mul_coord`
- Truth anchor: `D5/S3/Analytic/MultivariateEnergy/Moments.isAdmissible_familyKernel_three`
- Truth anchor: `D5/S3/Analytic/MultivariateEnergy/Moments.measurePreserving_sphereAction`
- Dependency: [D5/S3/Analytic/MultivariateEnergy/Defs](Defs.md)
