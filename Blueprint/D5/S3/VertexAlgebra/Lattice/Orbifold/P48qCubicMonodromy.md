# Conformal Monodromy of the P48q Cubic Twisted Module

## Abstract

The actual P48q cubic twisted carrier has a conformal rotation with a primitive scalar cube.

**Theorem 1.1 (Phase of the actual conformal coefficient).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qCubicMonodromy.conformalMonodromy_native_conformal_eigenvector`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qCubicMonodromy.conformalMonodromy_native_conformal_eigenvector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The conformal coefficient at cover exponent −6 is the full zero mode. On a nonzero joint coefficient of an eigenvector, the zero mode determines the weight as 16/9 plus the grading index divided by three. Multiplying the normalized grading rotation by the vacuum phase gives exp(2πi times the weight) on the eigenvector.

**Theorem 1.2 (The primitive scalar cube).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qCubicMonodromy.conformalMonodromy_cube`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qCubicMonodromy.conformalMonodromy_cube` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized grading rotation cubes to the identity. The vacuum phase cubed is exp(2πi/3), since three times 16/9 is 5 + 1/3.

**Theorem 1.3 (The ambient cyclic product).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qCubicMonodromy.cyclicProduct_eq_zeta_of_nativeMonodromy`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qCubicMonodromy.cyclicProduct_eq_zeta_of_nativeMonodromy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given a projective centralizer action for the specified ambient associator with the constructed conformal rotation as its generator action, the operator power formula identifies the cyclic associator product with exp(2πi/3). Evaluating the operator identity on the nonzero vacuum cancels the vector. A subgroup trivializing the associator cannot contain the generator.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qCubicMonodromy.conformalMonodromy_cube`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qCubicMonodromy.conformalMonodromy_native_conformal_eigenvector`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qCubicMonodromy.cyclicProduct_eq_zeta_of_nativeMonodromy`
- Dependency: [D5/S3/FiniteGroups/Cyclic/CyclicProjectiveMonodromy](../../../FiniteGroups/Cyclic/CyclicProjectiveMonodromy.md)
