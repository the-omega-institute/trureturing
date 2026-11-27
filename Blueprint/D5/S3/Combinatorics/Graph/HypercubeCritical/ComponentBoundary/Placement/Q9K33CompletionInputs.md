# Size and direction pairs in actual components

## Abstract

Two-coordinate saturation forces a corner and ambient packing forces sixty vertices.

**Theorem 1.1 (Every pair of directions occurs at a common corner).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33CompletionInputs.exists_corner_for_each_direction_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33CompletionInputs.exists_corner_for_each_direction_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put unit weight on the two prescribed axes and zero elsewhere. The singular defect forces a row whose selected incident weights sum to at least the square root of two. Both directions must therefore lead into the component.

**Theorem 1.2 (An actual component has at least sixty vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33CompletionInputs.sixty_le_actual_component`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33CompletionInputs.sixty_le_actual_component` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The balanced cubic lower bound starts at fifty-four. A closed component of size fifty-four limits the ambient subcubic set to 257. Each axis contributes one sixth of the component size, so the next available size is sixty.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33CompletionInputs.exists_corner_for_each_direction_pair`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33CompletionInputs.sixty_le_actual_component`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeFiftyFourLowerBound](../../BalancedCubeFiftyFourLowerBound.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ComponentWeightedProfile](../Q9ComponentWeightedProfile.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9Gray54ExtensionBound](../Q9Gray54ExtensionBound.md)
