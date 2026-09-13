# ConjunctionRegistrationTemplates

## Abstract

Typed finite conjunction registration programs preserve complete source statements.

**Definition 1.1 (ConjunctionClause).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates.ConjunctionClause`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates.ConjunctionClause` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Finite indices give a closed language of count equality, three-set coverage, disjointness, positive and negative anchored membership, and binary conjunction. No constructor accepts an arbitrary law.

**Definition 1.2 (conjunctionStatement).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates.conjunctionStatement`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates.conjunctionStatement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The interpreter retains the clause tree and the original finite set operations over predicates and anchors.

**Definition 1.3 (conjunctionDecidable).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates.conjunctionDecidable`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates.conjunctionDecidable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Structural recursion decides the interpreted finite clause tree.

**Definition 1.4 (conjunctionSignature).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates.conjunctionSignature`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates.conjunctionSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The generated signature contains exactly the requested Boolean ADMIT readouts and ANCHOR slots.

**Definition 1.5 (conjunctionRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates.conjunctionRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates.conjunctionRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each state predicate is reflected to its Boolean readout; the supplied anchors are retained.

**Definition 1.6 (conjunctionArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates.conjunctionArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates.conjunctionArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An explicit finite object arena and a typed clause tree determine the realization-dependent law.

**Theorem 1.7 (conjunctionLegacy).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates.conjunctionLegacy`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates.conjunctionLegacy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Boolean reflection preserves every clause and its conjunction structure without using source theorem proofs.

**Definition 1.8 (replaceConjunctionReadout).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates.replaceConjunctionReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates.replaceConjunctionReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One Boolean readout changes while all other readouts and every anchor stay fixed.

**Definition 1.9 (replaceConjunctionAnchor).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates.replaceConjunctionAnchor`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates.replaceConjunctionAnchor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One anchor changes while every readout and each other anchor stay fixed.

**Theorem 1.10 (conjunction_sensitivity).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates.conjunction_sensitivity`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates.conjunction_sensitivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A valid realization and one falsifying update per slot construct full finite slot sensitivity, including anchor support.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates.ConjunctionClause`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates.conjunctionArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates.conjunctionDecidable`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates.conjunctionLegacy`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates.conjunctionRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates.conjunctionSignature`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates.conjunctionStatement`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates.conjunction_sensitivity`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates.replaceConjunctionAnchor`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates.replaceConjunctionReadout`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/RegistrationTemplates](RegistrationTemplates.md)
