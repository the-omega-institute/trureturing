# The six original double-lift certificates

## Abstract

The six original double-lift certificates

The supplied binary point/line labels, sheet bits, twist flags and selected lists are unchanged. All six N1,N2,S,J,C,K types have actual dissociation fifteen-sets and the cubic upper cap sixteen; S and J additionally have actual sixteen-sets proving beta=SF=16. The six finite witnesses do not themselves classify arbitrary signings or transfer across graph isomorphisms.

**Definition 1.1 (label).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.label`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.label` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def label (vertex : Fin 28) : Nat.

**Definition 1.2 (sheet).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.sheet`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.sheet` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def sheet (vertex : Fin 28) : Nat.

**Definition 1.3 (dot).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.dot`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.dot` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def dot (first second : Nat) : Nat.

**Definition 1.4 (adjacency).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.adjacency`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.adjacency` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def adjacency (twists : List (Nat × Nat)) (first second : Fin 28) : Prop.

**Definition 1.5 (selected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.selected`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.selected` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def selected (points lines : List Nat) (vertex : Fin 28) : Prop.

**Definition 1.6 (scalarTwists).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.scalarTwists`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.scalarTwists` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def scalarTwists : List (Nat × Nat).

**Definition 1.7 (jordanTwists).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.jordanTwists`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.jordanTwists` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def jordanTwists : List (Nat × Nat).

**Definition 1.8 (scalarPoints).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.scalarPoints`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.scalarPoints` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def scalarPoints : List Nat.

**Definition 1.9 (scalarLines).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.scalarLines`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.scalarLines` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def scalarLines : List Nat.

**Definition 1.10 (jordanPoints).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.jordanPoints`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.jordanPoints` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def jordanPoints : List Nat.

**Definition 1.11 (jordanLines).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.jordanLines`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.jordanLines` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def jordanLines : List Nat.

**Theorem 1.12 (scalar dissociates).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.scalar_dissociates`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.scalar_dissociates` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem scalar_dissociates : Dissociates (adjacency scalarTwists) (selected scalarPoints scalarLines).

**Theorem 1.13 (jordan dissociates).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.jordan_dissociates`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.jordan_dissociates` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem jordan_dissociates : Dissociates (adjacency jordanTwists) (selected jordanPoints jordanLines).

**Theorem 1.14 (scalar card).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.scalar_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.scalar_card` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem scalar_card : ((List.finRange 28).filter (fun vertex => decide (selected scalarPoints scalarLines vertex))).length = 16.

**Theorem 1.15 (jordan card).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.jordan_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.jordan_card` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem jordan_card : ((List.finRange 28).filter (fun vertex => decide (selected jordanPoints jordanLines vertex))).length = 16.

**Definition 1.16 (scalarGraph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.scalarGraph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.scalarGraph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def scalarGraph : SimpleGraph (Fin 28).

**Definition 1.17 (jordanGraph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.jordanGraph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.jordanGraph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def jordanGraph : SimpleGraph (Fin 28).

**Definition 1.18 (scalarSet).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.scalarSet`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.scalarSet` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def scalarSet : Finset (Fin 28).

**Definition 1.19 (jordanSet).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.jordanSet`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.jordanSet` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def jordanSet : Finset (Fin 28).

**Theorem 1.20 (scalar selection).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.scalar_selection`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.scalar_selection` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem scalar_selection : IsKIndependent scalarGraph 2 scalarSet ∧ scalarSet.card = 16.

**Theorem 1.21 (jordan selection).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.jordan_selection`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.jordan_selection` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem jordan_selection : IsKIndependent jordanGraph 2 jordanSet ∧ jordanSet.card = 16.

**Theorem 1.22 (scalar class).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.scalar_class`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.scalar_class` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem scalar_class : scalarGraph.Colorable 2 ∧ ∀ v, DegreeCapacity.degree scalarGraph v = 3.

**Theorem 1.23 (jordan class).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.jordan_class`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.jordan_class` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem jordan_class : jordanGraph.Colorable 2 ∧ ∀ v, DegreeCapacity.degree jordanGraph v = 3.

**Theorem 1.24 (scalar parameters).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.scalar_parameters`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.scalar_parameters` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem scalar_parameters : beta scalarGraph 2 = 16 ∧ SF scalarGraph 2 = 16.

**Theorem 1.25 (jordan parameters).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.jordan_parameters`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.jordan_parameters` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem jordan_parameters : beta jordanGraph 2 = 16 ∧ SF jordanGraph 2 = 16.

**Definition 1.26 (sixTwists).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.sixTwists`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.sixTwists` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def sixTwists (k : Fin 6) : List (Nat × Nat).

**Definition 1.27 (sixPoints).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.sixPoints`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.sixPoints` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def sixPoints (k : Fin 6) : List Nat.

**Definition 1.28 (sixLines).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.sixLines`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.sixLines` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def sixLines (k : Fin 6) : List Nat.

**Definition 1.29 (sixGraph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.sixGraph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.sixGraph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def sixGraph (k : Fin 6) : SimpleGraph (Fin 28).

**Definition 1.30 (sixSet).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.sixSet`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.sixSet` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def sixSet (k : Fin 6) : Finset (Fin 28).

**Theorem 1.31 (six selection).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.six_selection`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.six_selection` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem six_selection (k : Fin 6) : IsKIndependent (sixGraph k) 2 (sixSet k) ∧ (sixSet k).card = 15.

**Theorem 1.32 (six class).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.six_class`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.six_class` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem six_class (k : Fin 6) : (sixGraph k).Colorable 2 ∧ ∀ v, DegreeCapacity.degree (sixGraph k) v = 3.

**Theorem 1.33 (six beta bounds).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.six_beta_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.six_beta_bounds` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem six_beta_bounds (k : Fin 6) : 15 ≤ beta (sixGraph k) 2 ∧ beta (sixGraph k) 2 ≤ 16.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.adjacency`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.dot`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.jordanGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.jordanLines`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.jordanPoints`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.jordanSet`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.jordanTwists`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.jordan_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.jordan_class`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.jordan_dissociates`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.jordan_parameters`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.jordan_selection`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.label`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.scalarGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.scalarLines`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.scalarPoints`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.scalarSet`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.scalarTwists`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.scalar_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.scalar_class`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.scalar_dissociates`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.scalar_parameters`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.scalar_selection`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.selected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.sheet`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.sixGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.sixLines`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.sixPoints`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.sixSet`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.sixTwists`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.six_beta_bounds`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.six_class`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.six_selection`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/FiniteMasks](FiniteMasks.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/RegularCompensation](RegularCompensation.md)
