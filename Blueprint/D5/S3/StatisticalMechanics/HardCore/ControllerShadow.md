# Constructed controller shadows

## Abstract

Transport state-dependent geometric controllers by replaying their coarse history.

**Definition 1.1 (Coarse history replay).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/ControllerShadow.controllerTrace`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/ControllerShadow.controllerTrace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The newest-first direction history determines a coarse mask by replaying actual memoryStep updates. The function is total on illegal histories; only legal branches contribute to path counts.

**Definition 1.2 (A constructed history policy).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/ControllerShadow.liftedPolicy`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/ControllerShadow.liftedPolicy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fine controller reads the replayed coarse mask. It never substitutes the current fine mask's projection for forgotten coarse history.

**Theorem 1.3 (All-depth refinement).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/ControllerShadow.lifted_controller_refines`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/ControllerShadow.lifted_controller_refines` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nested initial blocker sets and increasing radius, the constructed history policy has no more fine-memory descendants than the original coarse state policy. MemoryRefinement owns the synchronized-history comparison and is reused.

**Theorem 1.4 (An exact legal geometric diagnostic).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/ControllerShadow.coarse_shadow_is_not_current_projection`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/ControllerShadow.coarse_shadow_is_not_current_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The chronological SRL walk straight, straight, right, right is legal in both radii. The point (2,-1) remains in the radius-four state after projection into the radius-three disk, but the radius-three process has already forgotten it. The finite proof script requests kernel reduction.

This source is a logically reviewed candidate. Lean elaboration, executed axiom closure and Scribe emission have not been obtained in the authoring runtime.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/ControllerShadow.coarse_shadow_is_not_current_projection`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/ControllerShadow.controllerTrace`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/ControllerShadow.liftedPolicy`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/ControllerShadow.lifted_controller_refines`
- Dependency: [D5/S3/StatisticalMechanics/HardCore/MemoryRefinement](MemoryRefinement.md)
