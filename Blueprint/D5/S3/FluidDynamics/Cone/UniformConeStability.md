# Uniform cone stability

## Abstract

Every compact set of true-cone data admits one positive perturbation radius preserving the lower bound on v and positive definiteness of the cone matrix.

**Definition 1.1 (Cone datum).**

Lean statement: `D5/S3/FluidDynamics/Cone/UniformConeStability.ConeDatum`

*Formalization.* `D5/S3/FluidDynamics/Cone/UniformConeStability.ConeDatum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A cone datum is a triple of real numbers in the order P, J, v, equipped with the product metric.

**Definition 1.2 (True cone).**

Lean statement: `D5/S3/FluidDynamics/Cone/UniformConeStability.trueCone`

*Formalization.* `D5/S3/FluidDynamics/Cone/UniformConeStability.trueCone` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The true cone consists of data for which v and P are greater than two and v is strictly below the cone bound at P and J.

**Theorem 1.3 (Continuous cone bound).**

Lean statement: `D5/S3/FluidDynamics/Cone/UniformConeStability.continuous_coneBound`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Cone/UniformConeStability.continuous_coneBound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cone bound is a continuous real function of the cone datum.

**Theorem 1.4 (Open true cone).**

Lean statement: `D5/S3/FluidDynamics/Cone/UniformConeStability.isOpen_trueCone`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Cone/UniformConeStability.isOpen_trueCone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The true cone is open in the space of cone data.

**Theorem 1.5 (Uniform perturbation radius).**

Lean statement: `D5/S3/FluidDynamics/Cone/UniformConeStability.compact_trueCone_stable`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Cone/UniformConeStability.compact_trueCone_stable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every compact subset of the true cone admits a single positive radius such that any datum at distance at most that radius from any point of the subset remains in the true cone.

**Theorem 1.6 (Uniform matrix positivity).**

Lean statement: `D5/S3/FluidDynamics/Cone/UniformConeStability.compact_coneMatrix_posDef_stable`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Cone/UniformConeStability.compact_coneMatrix_posDef_stable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every compact subset of the true cone admits a single positive radius such that any datum at distance at most that radius from any point of the subset has v greater than two and a positive definite cone matrix.

## References

- Truth anchor: `D5/S3/FluidDynamics/Cone/UniformConeStability.ConeDatum`
- Truth anchor: `D5/S3/FluidDynamics/Cone/UniformConeStability.compact_coneMatrix_posDef_stable`
- Truth anchor: `D5/S3/FluidDynamics/Cone/UniformConeStability.compact_trueCone_stable`
- Truth anchor: `D5/S3/FluidDynamics/Cone/UniformConeStability.continuous_coneBound`
- Truth anchor: `D5/S3/FluidDynamics/Cone/UniformConeStability.isOpen_trueCone`
- Truth anchor: `D5/S3/FluidDynamics/Cone/UniformConeStability.trueCone`
- Dependency: [D5/S3/FluidDynamics/Cone/ConePositivity](ConePositivity.md)
