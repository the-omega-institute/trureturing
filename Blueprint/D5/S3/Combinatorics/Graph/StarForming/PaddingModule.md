# Actual arbitrary-size open padding modules

## Abstract

Actual arbitrary-size open padding modules

The disjoint broken Heawood block and marked four-port equality core form the actual open module. Saturating the Heawood block omits its own first core pair and pays one strictly lost core vertex, while the remaining two ports are unrestricted. The original minimal forming set and dissociation set remain actual attained witnesses. The module has exactly two degree-two ring ports and all other degrees three, with a proper coloring across both attachment edges.

**Definition 1.1 (Vertex).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.Vertex`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.Vertex` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: abbrev Vertex (I : Type).

**Definition 1.2 (adjacency).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.adjacency`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.adjacency` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def adjacency (e : Equiv.Perm I) (mark : I) : Vertex I → Vertex I → Prop | .inl v,.inl w => HeawoodPorts.graph.Adj v w | .inr x,.inr y => (FourPortCore.graph e mark).Adj x y | .inl v,.inr y => y.1=mark ∧ ((v=0 ∧ y.2=13) ∨ (v=8 ∧ y.2=12)) | .inr x,.inl w => x.1=mark ∧ ((w=0 ∧ x.2=13) ∨ (w=8 ∧ x.2=12)) def graph (e : Equiv.Perm I) (mark : I) : SimpleGraph (Vertex I).

**Definition 1.3 (graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.graph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def graph (e : Equiv.Perm I) (mark : I) : SimpleGraph (Vertex I).

**Theorem 1.4 (restrictions).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.restrictions`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.restrictions` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem restrictions (e : Equiv.Perm I) (mark : I) (D : Finset (Vertex I)) (hD : IsKIndependent (graph e mark) 2 D) : IsKIndependent HeawoodPorts.graph 2 D.toLeft ∧ IsKIndependent (FourPortCore.graph e mark) 2 D.toRight.

**Theorem 1.5 (beta cap).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.beta_cap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.beta_cap` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem beta_cap (e : Equiv.Perm I) (mark : I) (D : Finset (Vertex I)) (hD : IsKIndependent (graph e mark) 2 D) : D.card ≤ 7+12*Fintype.card I.

**Definition 1.6 (forming).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.forming`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.forming` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def forming : Finset (Vertex I).

**Definition 1.7 (independent).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.independent`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.independent` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def independent : Finset (Vertex I).

**Theorem 1.8 (forming minimal).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.forming_minimal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.forming_minimal` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem forming_minimal (e : Equiv.Perm I) (mark : I) : IsMinimalStarForming (graph e mark) 2 forming.

**Theorem 1.9 (forming card).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.forming_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.forming_card` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem forming_card : (forming : Finset (Vertex I)).card=8+12*Fintype.card I.

**Definition 1.10 (neighbors).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.neighbors`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.neighbors` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def neighbors (e : Equiv.Perm I) (mark : I) : Vertex I → Finset (Vertex I) | .inl v => (Cubic.brokenNeighbors v).toFinset.map Function.Embedding.inl ∪ (if v=0 then {Sum.inr (mark,13)} else if v=8 then {Sum.inr (mark,12)} else ∅) | .inr x => ((EqualityCore.neighbors e x).filter (fun y => ¬ FourPortCore.cut mark x y)).map Function.Embedding.inr ∪ (if x=(mark,12) then {Sum.inl 8} else if x=(mark,13) then {Sum.inl 0} else ∅) set_option maxHeartbeats 1200000 in theorem mem_neighbors (e : Equiv.Perm I) (mark : I) (x y : Vertex I) : y ∈ neighbors e mark x ↔ (graph e mark).Adj x y.

**Theorem 1.11 (mem neighbors).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.mem_neighbors`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.mem_neighbors` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem mem_neighbors (e : Equiv.Perm I) (mark : I) (x y : Vertex I) : y ∈ neighbors e mark x ↔ (graph e mark).Adj x y.

**Definition 1.12 (leftPort).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.leftPort`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.leftPort` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def leftPort (mark : I) : Vertex I.

**Definition 1.13 (rightPort).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.rightPort`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.rightPort` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def rightPort (mark : I) : Vertex I.

**Theorem 1.14 (degree).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.degree`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.degree` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem degree (e : Equiv.Perm I) (mark : I) (x : Vertex I) : DegreeCapacity.degree (graph e mark) x = if x=leftPort mark ∨ x=rightPort mark then 2 else 3.

**Definition 1.15 (color).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.color`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.color` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def color : Vertex I → Bool | .inl v => decide (7 ≤ v.val) | .inr x => EqualityCore.color x.2 /-- The actual point/line coloring agrees with the periodic core coloring across both new attachment edges. -/ theorem proper_color (e : Equiv.Perm I) (mark : I) (x y : Vertex I) (h : (graph e mark).Adj x y) : color x ≠ color y.

**Theorem 1.16 (proper color).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.proper_color`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.proper_color` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem proper_color (e : Equiv.Perm I) (mark : I) (x y : Vertex I) (h : (graph e mark).Adj x y) : color x ≠ color y.

**Theorem 1.17 (bipartite).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.bipartite`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.bipartite` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem bipartite (e : Equiv.Perm I) (mark : I) : (graph e mark).Colorable 2.

**Theorem 1.18 (independent valid).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.independent_valid`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.independent_valid` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem independent_valid (e : Equiv.Perm I) (mark : I) : IsKIndependent (graph e mark) 2 independent.

**Theorem 1.19 (independent card).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.independent_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.independent_card` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem independent_card : (independent : Finset (Vertex I)).card=7+12*Fintype.card I.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.Vertex`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.adjacency`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.beta_cap`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.bipartite`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.color`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.degree`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.forming`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.forming_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.forming_minimal`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.independent`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.independent_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.independent_valid`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.leftPort`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.mem_neighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.neighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.proper_color`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.restrictions`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PaddingModule.rightPort`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/FourPortCore](FourPortCore.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/HeawoodPorts](HeawoodPorts.md)
