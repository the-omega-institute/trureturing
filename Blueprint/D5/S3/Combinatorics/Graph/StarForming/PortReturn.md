# Direct split and relay returns

## Abstract

Direct split and relay returns

A deletion failure is exactly one of the Direct, Split or Relay shapes defined here. Protected high ports have a return witness; that witness is unique and excludes another high vertex touching the same return. The proof keeps all adjacency, selected-neighbor and symmetry conditions. It does not assert that every signal forces a positive Heawood block loss.

**Definition 1.1 (OnlyNeighbor).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PortReturn.OnlyNeighbor`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/PortReturn.OnlyNeighbor` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def OnlyNeighbor {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (vertex neighbor : Vertex) : Prop.

**Definition 1.2 (FailureShape).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PortReturn.FailureShape`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/PortReturn.FailureShape` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def FailureShape {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (deleted outside : Vertex) : Prop.

**Theorem 1.3 (failure iff shapes).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PortReturn.failure_iff_shapes`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PortReturn.failure_iff_shapes` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem failure_iff_shapes {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (hforms : Forms adjacency selection) (deleted outside : Vertex) (hselected : selection deleted) (houtside : ¬ selection outside) : Failure adjacency selection deleted outside ↔ FailureShape adjacency selection deleted outside.

**Theorem 1.4 (protected port returns).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PortReturn.protected_port_returns`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PortReturn.protected_port_returns` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem protected_port_returns {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection block core : Vertex → Prop) (hirreflexive : ∀ vertex, ¬ adjacency vertex vertex) (hsymmetric : ∀ first second, adjacency first second → adjacency second first) (hminimal : Minimal adjacency selection) (port exit : Vertex) (hhigh : High adjacency selection port) (hexit : core exit) (hboundary : ∀ neighbor, adjacency port neighbor → ¬ block neighbor → neighbor = exit) (hprotectedOmitted : ∀ outside, block outside → ¬ selection outside → adjacency outside port → TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ port) outside) (hprotectedSelected : ∀ neighbor, block neighbor → selection neighbor → adjacency port neighbor → ∃ replacement, selection replacement ∧ replacement ≠ port ∧ adjacency neighbor replacement) (hexitNeighbors : ∀ vertex, adjacency exit vertex → vertex ≠ port → core vertex) : ∃ outside, core outside ∧ Failure adjacency selection port outside ∧ (outside = exit ∨ (¬ adjacency outside port ∧ OnlyNeighbor adjacency selection outside exit ∧ OnlyNeighbor adjacency selection exit port)).

**Theorem 1.5 (return witness unique).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PortReturn.return_witness_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PortReturn.return_witness_unique` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem return_witness_unique {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (hforms : Forms adjacency selection) (first second outside : Vertex) (hfirst : High adjacency selection first) (hsecond : High adjacency selection second) (hfailureFirst : Failure adjacency selection first outside) (hfailureSecond : Failure adjacency selection second outside) : first = second.

**Theorem 1.6 (other high cannot touch return).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PortReturn.other_high_cannot_touch_return`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PortReturn.other_high_cannot_touch_return` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem other_high_cannot_touch_return {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (port other outside : Vertex) (hdifferent : other ≠ port) (hhigh : High adjacency selection other) (hfailure : Failure adjacency selection port outside) : ¬ adjacency outside other.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PortReturn.FailureShape`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PortReturn.OnlyNeighbor`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PortReturn.failure_iff_shapes`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PortReturn.other_high_cannot_touch_return`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PortReturn.protected_port_returns`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PortReturn.return_witness_unique`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/RegularBound](RegularBound.md)
