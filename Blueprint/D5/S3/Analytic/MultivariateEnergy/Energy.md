# Energy

## Abstract

Energy of centered spherical matrix kernels.

**Theorem 1.1 (Cubic energy from the centered moment).**

Lean statement: `D5/S3/Analytic/MultivariateEnergy/Energy.energy_family_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MultivariateEnergy/Energy.energy_family_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite dimension d, real beta, and Borel probability measure mu on the unit sphere, put Q equal to the integral of xx transpose minus the identity divided by d. The three-input family has energy beta times tr(Q squared) minus tr(Q cubed). Fubini and integration of linear matrix functionals give the reduction.

**Theorem 1.2 (The averaged matrix pairing).**

Lean statement: `D5/S3/Analytic/MultivariateEnergy/Energy.avgKernel_family_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MultivariateEnergy/Energy.avgKernel_family_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In every positive dimension, integrating the first of the three inputs against normalized surface measure leaves beta divided by three times tr(A(x)A(y)). The surface average of A is zero, so both pairs involving the integrated input and the cubic term vanish.

**Theorem 1.3 (Positivity for finite measure differences).**

Lean statement: `D5/S3/Analytic/MultivariateEnergy/Energy.isCondPosDef_family`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MultivariateEnergy/Energy.isCondPosDef_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative beta the averaged kernel is conditionally positive definite. For any two finite Borel measures, its quadratic expression is beta divided by three times tr((Q1 minus Q2) squared). The moment matrices are real symmetric, so the trace is nonnegative. This proof does not need equality of the two total masses.

## References

- Truth anchor: `D5/S3/Analytic/MultivariateEnergy/Energy.avgKernel_family_eq`
- Truth anchor: `D5/S3/Analytic/MultivariateEnergy/Energy.energy_family_eq`
- Truth anchor: `D5/S3/Analytic/MultivariateEnergy/Energy.isCondPosDef_family`
- Dependency: [D5/S3/Analytic/MultivariateEnergy/Moments](Moments.md)
