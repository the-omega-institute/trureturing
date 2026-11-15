# Bloch axis contraction commutator

## Abstract

Parameterized commutators of qubit Bloch axis contractions.

**Definition 1.1 (Bloch axis contraction).**

Lean statement: `D5/S3/Quantum/Measurement/Bloch/AxisContractionCommutator.axisContraction`

*Formalization.* `D5/S3/Quantum/Measurement/Bloch/AxisContractionCommutator.axisContraction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real three-coordinate axis n and real factor c, axisContraction n c is the matrix c I + (1 - c) n nᵀ, with entries expanded over Fin 3.

**Definition 1.2 (Bloch axis dot product).**

Lean statement: `D5/S3/Quantum/Measurement/Bloch/AxisContractionCommutator.axisDot`

*Formalization.* `D5/S3/Quantum/Measurement/Bloch/AxisContractionCommutator.axisDot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite coordinate dot product of two real Bloch vectors n and m is the sum over Fin 3 of n k times m k.

**Definition 1.3 (Bloch axis outer product).**

Lean statement: `D5/S3/Quantum/Measurement/Bloch/AxisContractionCommutator.axisOuter`

*Formalization.* `D5/S3/Quantum/Measurement/Bloch/AxisContractionCommutator.axisOuter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The outer product axisOuter n m is the matrix with entry (i,j) equal to n i times m j.

**Theorem 1.4 (Symmetric nonzero outer products force parallel axes).**

Lean statement: `D5/S3/Quantum/Measurement/Bloch/AxisContractionCommutator.axisOuter_eq_implies_parallel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Bloch/AxisContractionCommutator.axisOuter_eq_implies_parallel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the first three-coordinate vector is nonzero and its outer product with a second vector is symmetric under swapping the two vectors, then the second vector is a real scalar multiple of the first.

**Theorem 1.5 (Bloch axis contraction commutator factorization).**

Lean statement: `D5/S3/Quantum/Measurement/Bloch/AxisContractionCommutator.axisContraction_commutator`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Bloch/AxisContractionCommutator.axisContraction_commutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real three-coordinate axes n and m and real factors c and d, the commutator of axisContraction n c and axisContraction m d equals the scalar (1 - c)(1 - d)(n · m) times the antisymmetric outer-product difference n mᵀ - m nᵀ.

**Theorem 1.6 (Nonparallel nonorthogonal axes do not commute).**

Lean statement: `D5/S3/Quantum/Measurement/Bloch/AxisContractionCommutator.axisContraction_commutator_ne_zero_of_nonparallel_nonorthogonal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Bloch/AxisContractionCommutator.axisContraction_commutator_ne_zero_of_nonparallel_nonorthogonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero first axis, a second axis that is not a scalar multiple of it, a nonzero dot product, and factors different from one, the two Bloch contractions have a nonzero commutator.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/Bloch/AxisContractionCommutator.axisContraction`
- Truth anchor: `D5/S3/Quantum/Measurement/Bloch/AxisContractionCommutator.axisContraction_commutator`
- Truth anchor: `D5/S3/Quantum/Measurement/Bloch/AxisContractionCommutator.axisContraction_commutator_ne_zero_of_nonparallel_nonorthogonal`
- Truth anchor: `D5/S3/Quantum/Measurement/Bloch/AxisContractionCommutator.axisDot`
- Truth anchor: `D5/S3/Quantum/Measurement/Bloch/AxisContractionCommutator.axisOuter`
- Truth anchor: `D5/S3/Quantum/Measurement/Bloch/AxisContractionCommutator.axisOuter_eq_implies_parallel`
- Dependency: [D5/S3/Quantum/Measurement/Bloch/QubitBloch](QubitBloch.md)
