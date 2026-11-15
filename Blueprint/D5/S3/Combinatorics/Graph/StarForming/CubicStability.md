# Local support facts for compensated exchanges

## Abstract

Local support facts for compensated exchanges

The selected-leaf failure is adjacent; any other selected neighbor of its witness is an isolate. A witness adjacent to a high vertex has the corresponding isolate restriction. Shared leaf/high witnesses force the specified good-support owner. Isolates are retained in these local statements. Global exchange cardinalities and the sharp SF-minus-beta bound require further counting.

**Theorem 1.1 (leaf has adjacent failure).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicStability.leaf_has_adjacent_failure`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicStability.leaf_has_adjacent_failure` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem leaf_has_adjacent_failure {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (hirreflexive : ∀ vertex, ¬ adjacency vertex vertex) (hsymmetric : ∀ first second, adjacency first second → adjacency second first) (hminimal : Minimal adjacency selection) (leaf support : Vertex) (hleaf : selection leaf) (hhigh : High adjacency selection support) (hsupport : adjacency leaf support) (hunique : ∀ neighbor, selection neighbor → adjacency leaf neighbor → neighbor = support) : ∃ outside, Failure adjacency selection leaf outside ∧ adjacency outside leaf.

**Theorem 1.2 (leaf failure other neighbor is isolated).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicStability.leaf_failure_other_neighbor_is_isolated`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicStability.leaf_failure_other_neighbor_is_isolated` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem leaf_failure_other_neighbor_is_isolated {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (hsymmetric : ∀ first second, adjacency first second → adjacency second first) (leaf support outside other : Vertex) (hhigh : High adjacency selection support) (hunique : ∀ neighbor, selection neighbor → adjacency leaf neighbor → neighbor = support) (hfailure : Failure adjacency selection leaf outside) (hother : selection other) (hdifferent : other ≠ leaf) (hedge : adjacency outside other) : ∀ endpoint, selection endpoint → ¬ adjacency other endpoint.

**Theorem 1.3 (high adjacent failure other neighbor is isolated).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicStability.high_adjacent_failure_other_neighbor_is_isolated`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicStability.high_adjacent_failure_other_neighbor_is_isolated` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem high_adjacent_failure_other_neighbor_is_isolated {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (hsymmetric : ∀ first second, adjacency first second → adjacency second first) (htrianglefree : ∀ outside first second, adjacency outside first → adjacency outside second → adjacency first second → False) (deleted outside other : Vertex) (hfailure : Failure adjacency selection deleted outside) (hdeletededge : adjacency outside deleted) (hotheredge : adjacency outside other) (hother : selection other) (hdifferent : other ≠ deleted) : ∀ endpoint, selection endpoint → ¬ adjacency other endpoint.

**Theorem 1.4 (shared leaf high witness has good support owner).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicStability.shared_leaf_high_witness_has_good_support_owner`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicStability.shared_leaf_high_witness_has_good_support_owner` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem shared_leaf_high_witness_has_good_support_owner {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (htrianglefree : ∀ outside first second, adjacency outside first → adjacency outside second → adjacency first second → False) (leaf support deleted outside : Vertex) (hleaf : selection leaf) (hsupport : selection support) (hleafedge : adjacency leaf support) (houtsideedge : adjacency outside leaf) (hunique : ∀ neighbor, selection neighbor → adjacency leaf neighbor → neighbor = support) (hhigh : High adjacency selection deleted) (hfailure : Failure adjacency selection deleted outside) : deleted = support ∧ ¬ adjacency outside deleted.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicStability.high_adjacent_failure_other_neighbor_is_isolated`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicStability.leaf_failure_other_neighbor_is_isolated`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicStability.leaf_has_adjacent_failure`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicStability.shared_leaf_high_witness_has_good_support_owner`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/RegularBound](RegularBound.md)
