# Sensor Family Extension Strict Refinement

## Abstract

Adding a separating sensor strictly refines a sensor-family kernel.

**Theorem 1.1 (The extended family refines the original family).**

$$\forall sensor: I \to \left(X \to O\right), extra: X \to O, x, y: X,\\{}\operatorname{FamilyKernel}\left(\operatorname{extendedSensor}\left(sensor, extra\right), x, y\right) \Rightarrow \operatorname{FamilyKernel}\left(sensor, x, y\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SensorFamilies/SensorFamilyExtensionStrictRefinement.extension_kernel_refines_original` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume x and y agree under every coordinate of the family extended by one extra sensor.

Evaluating that agreement at each original-coordinate injection proves that x and y agree under the original family.

**Theorem 1.2 (A separating extra sensor witnesses strict refinement).**

$$\forall sensor: I \to \left(X \to O\right), extra: X \to O, x, y: X,\\{}(\operatorname{FamilyKernel}\left(sensor, x, y\right) \land \operatorname{extra}\left(x\right) \neq \operatorname{extra}\left(y\right)) \Rightarrow (\operatorname{FamilyKernel}\left(sensor, x, y\right) \land \neg\operatorname{FamilyKernel}\left(\operatorname{extendedSensor}\left(sensor, extra\right), x, y\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SensorFamilies/SensorFamilyExtensionStrictRefinement.separating_extension_witnesses_strict_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Now assume x and y agree under every old sensor but receive distinct values from the extra sensor.

The pair remains in the old family kernel and is excluded from the extended family kernel, giving the stated witness-level split.

## References

- Truth anchor: `D5/S3/ConceptDynamics/SensorFamilies/SensorFamilyExtensionStrictRefinement.extension_kernel_refines_original`
- Truth anchor: `D5/S3/ConceptDynamics/SensorFamilies/SensorFamilyExtensionStrictRefinement.separating_extension_witnesses_strict_refinement`
