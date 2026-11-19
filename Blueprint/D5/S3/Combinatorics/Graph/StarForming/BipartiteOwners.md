# Exact bipartite owner maxima

## Abstract

Exact bipartite owner maxima

For every finite bipartite graph, fixing a subset A of one side gives the actual dissociation completion A plus all zero-neighbor opposite vertices plus one representative for each distinct owner. Restriction gives the matching upper bound, so beta is the finite maximum of |A|+r0+p. For cubic graphs, exact edge and right-degree counts give the integer surplus p-2(r1-p)-r2 and an actual attaining left subset with surplus 3(beta-N). No connectedness or nonempty hypothesis is added.

**Definition 1.1 (Owns).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteOwners.Owns`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/BipartiteOwners.Owns` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def Owns (A : Finset V) (a r : V) : Prop.

**Theorem 1.2 (completion card).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteOwners.completion_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BipartiteOwners.completion_card` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem completion_card (A : Finset V) (hA : ∀ a ∈ A, color a = false) : (completion G color A).card = A.card + (zero G color A).card + (owners G color A).card.

**Theorem 1.3 (completion dissociation).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteOwners.completion_dissociation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BipartiteOwners.completion_dissociation` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem completion_dissociation (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (A : Finset V) (hA : ∀ a ∈ A, color a = false) : IsKIndependent G 2 (completion G color A).

**Theorem 1.4 (restriction upper).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteOwners.restriction_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BipartiteOwners.restriction_upper` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem restriction_upper (D : Finset V) (hD : IsKIndependent G 2 D) : let A.

**Theorem 1.5 (beta formula).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteOwners.beta_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BipartiteOwners.beta_formula` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem beta_formula (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) : beta G 2 = ((Finset.univ.filter (fun v => color v = false)).powerset.sup (fun A => A.card + (zero G color A).card + (owners G color A).card)).

**Definition 1.6 (rightCount).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteOwners.rightCount`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/BipartiteOwners.rightCount` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def rightCount (A : Finset V) (j : ℕ) : ℕ.

**Theorem 1.7 (cubic surplus identity).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteOwners.cubic_surplus_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BipartiteOwners.cubic_surplus_identity` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem cubic_surplus_identity (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hr : ∀ v, DegreeCapacity.degree G v = 3) (N : ℕ) (hN : (Finset.univ.filter (fun v => color v = true)).card = N) (A : Finset V) (hA : ∀ a ∈ A, color a = false) : 3 * ((A.card : ℤ) + (zero G color A).card + (owners G color A).card - N) = surplus G color A.

**Theorem 1.8 (cubic surplus maximum).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BipartiteOwners.cubic_surplus_maximum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BipartiteOwners.cubic_surplus_maximum` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem cubic_surplus_maximum (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hr : ∀ v, DegreeCapacity.degree G v = 3) (N : ℕ) (hN : (Finset.univ.filter (fun v => color v = true)).card = N) : ∃ A : Finset V, (∀ a ∈ A, color a = false) ∧ surplus G color A = 3*((beta G 2 : ℤ)-N) ∧ ∀ B : Finset V, (∀ b ∈ B, color b = false) → surplus G color B ≤ surplus G color A.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteOwners.Owns`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteOwners.beta_formula`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteOwners.completion_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteOwners.completion_dissociation`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteOwners.cubic_surplus_identity`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteOwners.cubic_surplus_maximum`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteOwners.restriction_upper`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BipartiteOwners.rightCount`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/BipartiteBounds](BipartiteBounds.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity](DegreeCapacity.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/DissociationCover](DissociationCover.md)
