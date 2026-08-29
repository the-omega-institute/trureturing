# Surjective Sensor Reindex Kernel Equality

## Abstract

Surjective reindexing preserves the joint sensor kernel.

**Theorem 1.1 (Surjective reindexing preserves family-kernel membership).**

$$\forall sensor: I \to \left(X \to O\right), select: J \to I, x, y: X,\\{}\operatorname{Surjective}\left(select\right) \Rightarrow (\operatorname{FamilyKernel}\left(sensor, x, y\right) \iff \operatorname{FamilyKernel}\left(j \mapsto \operatorname{sensor}\left(\operatorname{select}\left(j\right)\right), x, y\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SensorFamilies/SurjectiveSensorReindexKernelEquality.surjective_reindex_preserves_family_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let select map new sensor indices onto every original sensor index, and fix source states x and y.

Original-family agreement immediately gives reindexed agreement. For the reverse direction, surjectivity supplies a new index above each old coordinate.

The theorem preserves pointwise family-kernel membership; select need not be injective.

## References

- Truth anchor: `D5/S3/ConceptDynamics/SensorFamilies/SurjectiveSensorReindexKernelEquality.surjective_reindex_preserves_family_kernel`
