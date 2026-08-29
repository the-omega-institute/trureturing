# Sensor Family Restriction Monotonicity

## Abstract

Restricting a sensor family can only enlarge its equality kernel.

**Theorem 1.1 (Reindexing a subfamily only enlarges the kernel).**

$$\forall sensor: I \to \left(X \to O\right), select: J \to I, \operatorname{ker}\left(x \mapsto (i \mapsto \operatorname{sensor}\left(i, x\right))\right) \subseteq \operatorname{ker}\left(x \mapsto (j \mapsto \operatorname{sensor}\left(\operatorname{select}\left(j\right), x\right))\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SensorFamilies/SensorFamilyRestrictionMonotonicity.restricting_sensor_family_enlarges_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let select choose original sensor indices for a reindexed family. It may delete or repeat coordinates.

Agreement at every original coordinate implies agreement at each selected coordinate by evaluation through select.

Therefore the complete-family kernel is contained in the selected-family kernel; no injectivity or surjectivity of select is assumed.

## References

- Truth anchor: `D5/S3/ConceptDynamics/SensorFamilies/SensorFamilyRestrictionMonotonicity.restricting_sensor_family_enlarges_kernel`
