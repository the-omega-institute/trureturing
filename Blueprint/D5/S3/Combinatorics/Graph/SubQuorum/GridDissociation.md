# All-size rectangular-grid dissociation equality

## Abstract

All-size rectangular-grid dissociation equality

The actual Cartesian path graph is used throughout. Actual row restrictions give the no-three-selected path cap. Each two-by-two square has capacity two; saturation in an odd two-row band forces full even columns and empty odd columns, and prevents three consecutive positive row deviations. The odd-integer profile theorem and exact even-width pairing give the upper bound for every pair of natural dimensions, including zero. The actual periodic selection and its transpose attain both terms of F, with exact symbolic residue counts. Thus beta equals F without bounded-size grid enumeration. Coloring psiSq, representative Omega, arbitrary matching directions, absorption and strip-transfer claims are separate parameters and remain outside this theorem.

**Definition 1.1 (graph).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.graph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def graph (m n : ℕ) : SimpleGraph (Fin m × Fin n).

**Definition 1.2 (row).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.row`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.row` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def row (D : Finset (Fin m × Fin n)) (i : Fin m) : Finset (Fin n).

**Definition 1.3 (rowCount).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.rowCount`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.rowCount` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def rowCount (D : Finset (Fin m × Fin n)) (i : Fin m) : ℕ.

**Theorem 1.4 (sum rowCount).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.sum_rowCount`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.sum_rowCount` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem sum_rowCount (D : Finset (Fin m × Fin n)) : ∑ i, rowCount D i=D.card.

**Theorem 1.5 (row three free).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.row_three_free`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.row_three_free` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem row_three_free (D : Finset (Fin m × Fin n)) (hD : IsKIndependent (graph m n) 2 D) (i : Fin m) (j k l : Fin n) (hjk : j.val+1=k.val) (hkl : k.val+1=l.val) : ¬ (j ∈ row D i ∧ k ∈ row D i ∧ l ∈ row D i).

**Theorem 1.6 (row bound).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.row_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.row_bound` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem row_bound (D : Finset (Fin m × Fin n)) (hD : IsKIndependent (graph m n) 2 D) (i : Fin m) : rowCount D i ≤ n-n/3.

**Definition 1.7 (bandCount).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.bandCount`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.bandCount` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def bandCount (D : Finset (Fin m × Fin n)) (i k : Fin m) (j : Fin n) : ℕ.

**Theorem 1.8 (band pair bound).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.band_pair_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.band_pair_bound` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem band_pair_bound (D : Finset (Fin m × Fin n)) (hD : IsKIndependent (graph m n) 2 D) (i k : Fin m) (hik : (SimpleGraph.pathGraph m).Adj i k) (j l : Fin n) (hjl : (SimpleGraph.pathGraph n).Adj j l) : bandCount D i k j+bandCount D i k l ≤ 2.

**Theorem 1.9 (sum bandCount).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.sum_bandCount`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.sum_bandCount` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem sum_bandCount (D : Finset (Fin m × Fin n)) (i k : Fin m) : (∑ j, bandCount D i k j)=rowCount D i+rowCount D k.

**Theorem 1.10 (bandCount cap).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.bandCount_cap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.bandCount_cap` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem bandCount_cap (D : Finset (Fin m × Fin n)) (i k : Fin m) (j : Fin n) : bandCount D i k j ≤ 2.

**Theorem 1.11 (even band bound).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.even_band_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.even_band_bound` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem even_band_bound (hn : n%2=0) (D : Finset (Fin m × Fin n)) (hD : IsKIndependent (graph m n) 2 D) (i k : Fin m) (hik : (SimpleGraph.pathGraph m).Adj i k) : rowCount D i+rowCount D k ≤ n.

**Theorem 1.12 (odd band bound).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.odd_band_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.odd_band_bound` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem odd_band_bound (hn : n%2=1) (D : Finset (Fin m × Fin n)) (hD : IsKIndependent (graph m n) 2 D) (i k : Fin m) (hik : (SimpleGraph.pathGraph m).Adj i k) : rowCount D i+rowCount D k ≤ n+1.

**Theorem 1.13 (band rigidity).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.band_rigidity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.band_rigidity` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem band_rigidity (hn : n%2=1) (D : Finset (Fin m × Fin n)) (hD : IsKIndependent (graph m n) 2 D) (i k : Fin m) (hik : (SimpleGraph.pathGraph m).Adj i k) (htotal : n+1 ≤ rowCount D i+rowCount D k) : ∀ j, bandCount D i k j=if j.val%2=0 then 2 else 0.

**Theorem 1.14 (odd row pair).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.odd_row_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.odd_row_pair` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem odd_row_pair (hn : n%2=1) (D : Finset (Fin m × Fin n)) (hD : IsKIndependent (graph m n) 2 D) (i k : Fin m) (hik : (SimpleGraph.pathGraph m).Adj i k) : rowCount D i+rowCount D k ≤ n ∨ (2*rowCount D i=n+1 ∧ 2*rowCount D k=n+1).

**Theorem 1.15 (row profile three free).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.row_profile_three_free`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.row_profile_three_free` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem row_profile_three_free (hn : n%2=1) (D : Finset (Fin m × Fin n)) (hD : IsKIndependent (graph m n) 2 D) (i k l : Fin m) (hik : i.val+1=k.val) (hkl : k.val+1=l.val) : ¬ (0<2*(rowCount D i : ℤ)-n ∧ 0<2*(rowCount D k : ℤ)-n ∧ 0<2*(rowCount D l : ℤ)-n).

**Definition 1.16 (g).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.g`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.g` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def g (p : ℕ) : ℕ.

**Definition 1.17 (rowFormula).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.rowFormula`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.rowFormula` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def rowFormula (p q : ℕ) : ℕ.

**Definition 1.18 (formula).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.formula`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.formula` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def formula (p q : ℕ) : ℕ.

**Theorem 1.19 (odd width bound).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.odd_width_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.odd_width_bound` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem odd_width_bound (hn : n%2=1) (D : Finset (Fin m × Fin n)) (hD : IsKIndependent (graph m n) 2 D) : D.card ≤ formula m n.

**Theorem 1.20 (selection bound).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.selection_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.selection_bound` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem selection_bound (D : Finset (Fin m × Fin n)) (hD : IsKIndependent (graph m n) 2 D) : D.card ≤ formula m n.

**Theorem 1.21 (beta bound).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.beta_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.beta_bound` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem beta_bound : beta (graph m n) 2 ≤ formula m n.

**Definition 1.22 (chosen).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.chosen`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.chosen` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def chosen (p q : ℕ) : Finset (Fin p × Fin q).

**Theorem 1.23 (chosen dissociation).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.chosen_dissociation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.chosen_dissociation` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem chosen_dissociation : IsKIndependent (graph m n) 2 (chosen m n).

**Theorem 1.24 (chosen card).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.chosen_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.chosen_card` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem chosen_card : (chosen m n).card=rowFormula m n.

**Definition 1.25 (transpose).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.transpose`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.transpose` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def transpose : graph m n ≃g graph n m.

**Theorem 1.26 (formula le beta).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.formula_le_beta`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.formula_le_beta` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem formula_le_beta : formula m n ≤ beta (graph m n) 2.

**Theorem 1.27 (beta exact).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.beta_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.beta_exact` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem beta_exact : beta (graph m n) 2=formula m n.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.bandCount`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.bandCount_cap`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.band_pair_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.band_rigidity`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.beta_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.beta_exact`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.chosen`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.chosen_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.chosen_dissociation`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.even_band_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.formula`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.formula_le_beta`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.g`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.odd_band_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.odd_row_pair`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.odd_width_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.row`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.rowCount`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.rowFormula`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.row_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.row_profile_three_free`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.row_three_free`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.selection_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.sum_bandCount`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.sum_rowCount`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.transpose`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/Isomorphism](../StarForming/Isomorphism.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/SquareCapacity](../StarForming/SquareCapacity.md)
- Dependency: [D5/S3/Combinatorics/Graph/SubQuorum/GridProfile](GridProfile.md)
