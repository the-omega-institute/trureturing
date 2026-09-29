# GuardedEqualityRegistrationTemplates

## Abstract

Guarded equality registration programs over complete finite object arenas.

**Definition 1.1 (guardSlot).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrationTemplates.guardSlot`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrationTemplates.guardSlot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The shared constructor-written zero label in Fin 3 identifies the guard slot.

**Definition 1.2 (leftSlot).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrationTemplates.leftSlot`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrationTemplates.leftSlot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The shared constructor-written one label in Fin 3 identifies the left equality slot.

**Definition 1.3 (isGuardSlot).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrationTemplates.isGuardSlot`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrationTemplates.isGuardSlot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Pinned finite equality decides whether a slot label is guardSlot.

**Definition 1.4 (isLeftSlot).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrationTemplates.isLeftSlot`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrationTemplates.isLeftSlot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Pinned finite equality decides whether a slot label is leftSlot.

**Definition 1.5 (guardedEqSignature).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrationTemplates.guardedEqSignature`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrationTemplates.guardedEqSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin 3 retains three slot labels. Bool.rec selects the output type, its equality dictionary and its role: one Boolean ADMIT guard and two typed CUT terms. The anchor index is empty and every state is retained.

**Definition 1.6 (guardedEqRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrationTemplates.guardedEqRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrationTemplates.guardedEqRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Dependent Boolean dispatch selects the guard or a typed value; a second Bool.rec selects the left or right equality term. Fin labels are compared as data, with no Fin or Nat recursor dispatch, and all three readouts remain independent.

**Definition 1.7 (guardedEqArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrationTemplates.guardedEqArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrationTemplates.guardedEqArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed law equates the CUT terms whenever the varying guard is true.

**Theorem 1.8 (guardedEqLegacy).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrationTemplates.guardedEqLegacy`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrationTemplates.guardedEqLegacy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full conditional equation is definitionally the generated law.

**Theorem 1.9 (guardedEq_sensitivity).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrationTemplates.guardedEq_sensitivity`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrationTemplates.guardedEq_sensitivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An inhabited arena and two distinct values witness each guard and equality slot independently.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrationTemplates.guardSlot`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrationTemplates.guardedEqArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrationTemplates.guardedEqLegacy`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrationTemplates.guardedEqRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrationTemplates.guardedEqSignature`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrationTemplates.guardedEq_sensitivity`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrationTemplates.isGuardSlot`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrationTemplates.isLeftSlot`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrationTemplates.leftSlot`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/RegistrationTemplates](RegistrationTemplates.md)
- Dependency: [D5/S3/ConceptDynamics/RegistrationWitnesses](../RegistrationWitnesses.md)
