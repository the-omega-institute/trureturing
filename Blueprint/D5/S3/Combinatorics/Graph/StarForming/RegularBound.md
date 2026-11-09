# Deletion witnesses and local degree capacity

## Abstract

Deletion witnesses and local degree capacity

The graph relation is arbitrary except for each displayed simplicity or symmetry hypothesis. A high selected vertex has an outside deletion failure; distinct high vertices cannot share one. A failure has at most two selected neighbors, or at most one when nonadjacent to the deleted vertex. The selected-leaf witness lemma here explicitly assumes no selected isolates. The final capacity inequality is a local numerical implication; a complete degree-sum extraction is a separate obligation.

**Definition 1.1 (TwoAt).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/RegularBound.TwoAt`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/RegularBound.TwoAt` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def TwoAt {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (outside : Vertex) : Prop.

**Definition 1.2 (Forms).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/RegularBound.Forms`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/RegularBound.Forms` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def Forms {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) : Prop.

**Definition 1.3 (Minimal).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/RegularBound.Minimal`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/RegularBound.Minimal` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def Minimal {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) : Prop.

**Definition 1.4 (High).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/RegularBound.High`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/RegularBound.High` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def High {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (vertex : Vertex) : Prop.

**Definition 1.5 (Failure).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/RegularBound.Failure`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/RegularBound.Failure` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def Failure {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (deleted outside : Vertex) : Prop.

**Theorem 1.6 (covered deletion has failure).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/RegularBound.covered_deletion_has_failure`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/RegularBound.covered_deletion_has_failure` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem covered_deletion_has_failure {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (hminimal : Minimal adjacency selection) (deleted : Vertex) (hselected : selection deleted) (hnew : TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted) deleted) : ∃ outside, Failure adjacency selection deleted outside.

**Theorem 1.7 (high has failure).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/RegularBound.high_has_failure`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/RegularBound.high_has_failure` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem high_has_failure {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (hirreflexive : ∀ vertex, ¬ adjacency vertex vertex) (hminimal : Minimal adjacency selection) (deleted : Vertex) (hhigh : High adjacency selection deleted) : ∃ outside, Failure adjacency selection deleted outside.

**Theorem 1.8 (adjacent high survives).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/RegularBound.adjacent_high_survives`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/RegularBound.adjacent_high_survives` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem adjacent_high_survives {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (center deleted outside : Vertex) (hhigh : High adjacency selection center) (hdifferent : center ≠ deleted) (hedge : adjacency outside center) : TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted) outside.

**Theorem 1.9 (selected leaf has private witness).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/RegularBound.selected_leaf_has_private_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/RegularBound.selected_leaf_has_private_witness` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem selected_leaf_has_private_witness {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (hirreflexive : ∀ vertex, ¬ adjacency vertex vertex) (hsymmetric : ∀ first second, adjacency first second → adjacency second first) (hminimal : Minimal adjacency selection) (hnoisolates : ∀ vertex, selection vertex → ∃ neighbor, selection neighbor ∧ adjacency vertex neighbor) (leaf support : Vertex) (hleaf : selection leaf) (hhigh : High adjacency selection support) (hsupport : adjacency leaf support) (hunique : ∀ neighbor, selection neighbor → adjacency leaf neighbor → neighbor = support) : ∃ outside, Failure adjacency selection leaf outside ∧ adjacency outside leaf ∧ ∀ neighbor, selection neighbor → adjacency outside neighbor → neighbor = leaf.

**Theorem 1.10 (failure witnesses disjoint).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/RegularBound.failure_witnesses_disjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/RegularBound.failure_witnesses_disjoint` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem failure_witnesses_disjoint {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (hforms : Forms adjacency selection) (first second outside : Vertex) (hfirst : High adjacency selection first) (hsecond : High adjacency selection second) (hfailureFirst : Failure adjacency selection first outside) (hfailureSecond : Failure adjacency selection second outside) : first = second.

**Theorem 1.11 (witness has no three neighbors).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/RegularBound.witness_has_no_three_neighbors`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/RegularBound.witness_has_no_three_neighbors` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem witness_has_no_three_neighbors {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (deleted outside first second third : Vertex) (hfailure : Failure adjacency selection deleted outside) (hf : selection first) (hs : selection second) (ht : selection third) (hfs : first ≠ second) (hft : first ≠ third) (hst : second ≠ third) (ha : adjacency outside first) (hb : adjacency outside second) (hc : adjacency outside third) : False.

**Theorem 1.12 (nonadjacent witness unique neighbor).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/RegularBound.nonadjacent_witness_unique_neighbor`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/RegularBound.nonadjacent_witness_unique_neighbor` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem nonadjacent_witness_unique_neighbor {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (deleted outside first second : Vertex) (hfailure : Failure adjacency selection deleted outside) (hnonadjacent : ¬ adjacency outside deleted) (hf : selection first) (hs : selection second) (ha : adjacency outside first) (hb : adjacency outside second) : first = second.

**Theorem 1.13 (witness capacity).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/RegularBound.witness_capacity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/RegularBound.witness_capacity` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem witness_capacity (maximum selectedDegree outsideDegree : Nat) (adjacent : Prop) (hselected : selectedDegree ≤ maximum) (houtside : outsideDegree ≤ 2) (hadjacent : adjacent → selectedDegree + 1 ≤ maximum) (hnonadjacent : ¬ adjacent → outsideDegree ≤ 1) : selectedDegree + outsideDegree ≤ maximum + 1.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/RegularBound.Failure`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/RegularBound.Forms`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/RegularBound.High`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/RegularBound.Minimal`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/RegularBound.TwoAt`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/RegularBound.adjacent_high_survives`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/RegularBound.covered_deletion_has_failure`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/RegularBound.failure_witnesses_disjoint`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/RegularBound.high_has_failure`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/RegularBound.nonadjacent_witness_unique_neighbor`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/RegularBound.selected_leaf_has_private_witness`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/RegularBound.witness_capacity`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/RegularBound.witness_has_no_three_neighbors`
