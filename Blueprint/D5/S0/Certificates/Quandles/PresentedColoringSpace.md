# Presented Coloring Space

## Abstract

Generator colorings satisfying a presentation are exactly homomorphisms from its presented quandle.

**Definition 1.1 (Presented coloring assignments).**

Lean statement: `D5/S0/Certificates/Quandles/PresentedColoringSpace.RelColoring`

*Formalization.* `D5/S0/Certificates/Quandles/PresentedColoringSpace.RelColoring` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A coloring assignment is a generator map whose evaluations agree on every presented relation.

**Definition 1.2 (Colorings and homomorphisms are equivalent).**

Lean statement: `D5/S0/Certificates/Quandles/PresentedColoringSpace.satisfyingAssignmentsEquiv`

*Formalization.* `D5/S0/Certificates/Quandles/PresentedColoringSpace.satisfyingAssignmentsEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The universal property extends every satisfying generator assignment uniquely to a quandle homomorphism, and restriction to generators is its inverse.

**Theorem 1.3 (Coloring equivalence evaluation).**

Lean statement: `D5/S0/Certificates/Quandles/PresentedColoringSpace.satisfyingAssignmentsEquiv_apply`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Quandles/PresentedColoringSpace.satisfyingAssignmentsEquiv_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluating the equivalence sends a satisfying assignment to the homomorphism supplied by the presentation lift.

**Theorem 1.4 (Restriction recovers a coloring assignment).**

Lean statement: `D5/S0/Certificates/Quandles/PresentedColoringSpace.satisfyingAssignmentsEquiv_symm_apply_of`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Quandles/PresentedColoringSpace.satisfyingAssignmentsEquiv_symm_apply_of` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Restricting a homomorphism to the presented generators recovers its generator assignment.

## References

- Truth anchor: `D5/S0/Certificates/Quandles/PresentedColoringSpace.RelColoring`
- Truth anchor: `D5/S0/Certificates/Quandles/PresentedColoringSpace.satisfyingAssignmentsEquiv`
- Truth anchor: `D5/S0/Certificates/Quandles/PresentedColoringSpace.satisfyingAssignmentsEquiv_apply`
- Truth anchor: `D5/S0/Certificates/Quandles/PresentedColoringSpace.satisfyingAssignmentsEquiv_symm_apply_of`
- Dependency: [D5/S0/Certificates/Quandles/PresentedQuandle](PresentedQuandle.md)
