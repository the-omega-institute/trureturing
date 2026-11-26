# All-length four-port strict loss

## Abstract

All-length four-port strict loss

The actual periodic twenty-per-cell equality graph loses the two disjoint edges x0-x1 and x2-x3 in one marked cell. Exactly their four endpoints have degree two. The actual cut identity gives the unrestricted twelve-per-cell cap. If either complete cut pair is omitted, attaining the cap would force the complementary pair selected, no selected isolates, and no complementary edges. Restoring the edges then contradicts the original periodic integer weight identity. This proves strict loss at every length, with no restriction at the other pair.

**Definition 1.1 (cut).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.cut`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.cut` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def cut (mark : I) (x y : I × Fin 20) : Prop.

**Definition 1.2 (graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.graph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def graph (e : Equiv.Perm I) (mark : I) : SimpleGraph (I × Fin 20).

**Definition 1.3 (ports).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.ports`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.ports` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def ports (mark : I) : Finset (I × Fin 20).

**Theorem 1.4 (degree).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.degree`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.degree` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem degree (e : Equiv.Perm I) (mark : I) (x : I × Fin 20) : DegreeCapacity.degree (graph e mark) x = if x ∈ ports mark then 2 else 3.

**Theorem 1.5 (selected deficiency).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.selected_deficiency`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.selected_deficiency` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem selected_deficiency (e : Equiv.Perm I) (mark : I) (D : Finset (I × Fin 20)) : deficiency (graph e mark) 3 D = (D ∩ ports mark).card.

**Theorem 1.6 (exact identity).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.exact_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.exact_identity` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem exact_identity (e : Equiv.Perm I) (mark : I) (D : Finset (I × Fin 20)) (hD : IsKIndependent (graph e mark) 2 D) : 5*D.card+4+(isolates (graph e mark) D).card+2*complementEdges (graph e mark) D = 60*Fintype.card I+2*(D ∩ ports mark).card.

**Theorem 1.7 (card bound).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.card_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.card_bound` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem card_bound (e : Equiv.Perm I) (mark : I) (D : Finset (I × Fin 20)) (hD : IsKIndependent (graph e mark) 2 D) : D.card ≤ 12*Fintype.card I.

**Definition 1.8 (weight).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.weight`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.weight` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def weight : Fin 20 → ℤ.

**Theorem 1.9 (total weight).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.total_weight`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.total_weight` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem total_weight : (∑ v : I × Fin 20, weight v.2) = 0.

**Theorem 1.10 (weight balance).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.weight_balance`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.weight_balance` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem weight_balance (e : Equiv.Perm I) (x : I × Fin 20) : WeightedBalance.neighborSum (EqualityCore.graph e) (fun v => weight v.2) x + 2*weight x.2 = 0.

**Theorem 1.11 (restored selected degree).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.restored_selected_degree`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.restored_selected_degree` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem restored_selected_degree (e : Equiv.Perm I) (mark : I) (D : Finset (I × Fin 20)) (x : I × Fin 20) : selectedDegree (EqualityCore.graph e) D x = selectedDegree (graph e mark) D x + if x ∈ ports mark ∧ (mark,mate x.2) ∈ D then 1 else 0.

**Definition 1.12 (pair).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.pair`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.pair` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def pair (mark : I) (side : Bool) : Finset (I × Fin 20).

**Theorem 1.13 (omitted pair strict).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.omitted_pair_strict`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.omitted_pair_strict` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem omitted_pair_strict (e : Equiv.Perm I) (mark : I) (D : Finset (I × Fin 20)) (hD : IsKIndependent (graph e mark) 2 D) (side : Bool) (hmiss : Disjoint D (pair mark side)) : D.card+1 ≤ 12*Fintype.card I.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.card_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.cut`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.degree`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.exact_identity`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.omitted_pair_strict`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.pair`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.ports`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.restored_selected_degree`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.selected_deficiency`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.total_weight`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.weight`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/FourPortCore.weight_balance`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/DissociationDeficiency](DissociationDeficiency.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/EqualityCore](EqualityCore.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/WeightedBalance](WeightedBalance.md)
