# Exact odd-integer grid profiles

## Abstract

Exact odd-integer grid profiles

The actual path-neighborhood defect is at most one; positive defect forces full alternating support. Finite odd-integer level decomposition proves the complete source profile theorem without a negative-entry lower bound. Exact adjacent-pair summation and odd-ladder rigidity are consumed by the actual rectangular-grid dissociation proof.

**Theorem 1.1 (three free card).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.three_free_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.three_free_card` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem three_free_card (n : ℕ) (P : Finset ℕ) (hP : ∀ i ∈ P, i < n) (hthree : ∀ i, ¬ (i ∈ P ∧ i+1 ∈ P ∧ i+2 ∈ P)) : P.card ≤ n-n/3.

**Definition 1.2 (neighbors).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.neighbors`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.neighbors` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def neighbors {n : ℕ} (P : Finset (Fin n)) : Finset (Fin n).

**Theorem 1.3 (card le neighbors of missing even).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.card_le_neighbors_of_missing_even`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.card_le_neighbors_of_missing_even` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem card_le_neighbors_of_missing_even {n : ℕ} (hn : n % 2 = 1) (P : Finset (Fin n)) (pivot : Fin n) (hp : pivot.val % 2 = 0) (hmissing : pivot ∉ P) : P.card ≤ (neighbors P).card.

**Theorem 1.4 (odd path defect support).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.odd_path_defect_support`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.odd_path_defect_support` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem odd_path_defect_support {n : ℕ} (hn : n % 2 = 1) (P : Finset (Fin n)) (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ (SimpleGraph.pathGraph n).Adj a b) (hdefect : (neighbors P).card < P.card) : ∀ i : Fin n, i ∈ P ↔ i.val % 2 = 0.

**Theorem 1.5 (odd path defect bound).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.odd_path_defect_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.odd_path_defect_bound` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem odd_path_defect_bound {n : ℕ} (hn : n % 2 = 1) (P : Finset (Fin n)) : P.card ≤ (neighbors P).card + 1.

**Theorem 1.6 (even path expansion).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.even_path_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.even_path_expansion` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem even_path_expansion {n : ℕ} (hn : n % 2 = 0) (P : Finset (Fin n)) : P.card ≤ (neighbors P).card.

**Definition 1.7 (Compatible).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.Compatible`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.Compatible` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def Compatible {n : ℕ} (a : Fin n → ℤ) : Prop.

**Definition 1.8 (upperLevel).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.upperLevel`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.upperLevel` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def upperLevel {n : ℕ} (a : Fin n → ℤ) (h : ℕ) : Finset (Fin n).

**Definition 1.9 (lowerLevel).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.lowerLevel`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.lowerLevel` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def lowerLevel {n : ℕ} (a : Fin n → ℤ) (h : ℕ) : Finset (Fin n).

**Theorem 1.10 (even level balance).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.even_level_balance`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.even_level_balance` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem even_level_balance {n : ℕ} (hn : n % 2 = 0) (a : Fin n → ℤ) (ha : Compatible a) (h : ℕ) : (upperLevel a h).card ≤ (lowerLevel a h).card.

**Theorem 1.11 (odd level balance).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.odd_level_balance`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.odd_level_balance` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem odd_level_balance {n : ℕ} (hn : n % 2 = 1) (a : Fin n → ℤ) (ha : Compatible a) (h : ℕ) : (upperLevel a h).card ≤ (lowerLevel a h).card+1.

**Theorem 1.12 (positive level forces alternation).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.positive_level_forces_alternation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.positive_level_forces_alternation` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem positive_level_forces_alternation {n : ℕ} (hn : n % 2 = 1) (a : Fin n → ℤ) (ha : Compatible a) (h : ℕ) (hpos : (lowerLevel a h).card < (upperLevel a h).card) : ∀ i : Fin n, (i.val % 2 = 0 → 0<a i) ∧ (i.val % 2 = 1 → a i<0).

**Theorem 1.13 (profile level identity).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.profile_level_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.profile_level_identity` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem profile_level_identity {n : ℕ} (a : Fin n → ℤ) (H : ℕ) (hodd : ∀ i, a i%2=1) (hlo : ∀ i, -(2*(H : ℤ)+1) ≤ a i) (hhi : ∀ i, a i ≤ 2*(H : ℤ)+1) : (∑ i, a i) = (∑ i, if 0<a i then (1 : ℤ) else -1) + 2 * ∑ h ∈ Finset.range H, ((upperLevel a h).card - ((lowerLevel a h).card : ℤ)).

**Theorem 1.14 (sign sum bound).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.sign_sum_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.sign_sum_bound` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem sign_sum_bound {n : ℕ} (a : Fin n → ℤ) (hthree : ∀ i j k : Fin n, i.val+1=j.val → j.val+1=k.val → ¬ (0<a i ∧ 0<a j ∧ 0<a k)) : (∑ i, if 0<a i then (1 : ℤ) else -1) ≤ (n : ℤ)-2*(n/3 : ℕ).

**Theorem 1.15 (profile bound).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.profile_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.profile_bound` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem profile_bound {n : ℕ} (a : Fin n → ℤ) (A : ℕ) (hA : A%2=1) (hodd : ∀ i, a i%2=1) (hupper : ∀ i, a i ≤ A) (ha : Compatible a) (hthree : ∀ i j k : Fin n, i.val+1=j.val → j.val+1=k.val → ¬ (0<a i ∧ 0<a j ∧ 0<a k)) : (∑ i, a i) ≤ if n%2=0 then (n : ℤ)-2*(n/3 : ℕ) else max (A : ℤ) ((n : ℤ)-2*(n/3 : ℕ)).

**Theorem 1.16 (odd adjacent sum bound).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.odd_adjacent_sum_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.odd_adjacent_sum_bound` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem odd_adjacent_sum_bound {n : ℕ} (hn : n%2=1) (f : Fin n → ℤ) (hf : ∀ i j, (SimpleGraph.pathGraph n).Adj i j → f i+f j ≤ 2) (pivot : Fin n) (hp : pivot.val%2=0) : (∑ i, f i) ≤ (n : ℤ)-1+f pivot.

**Theorem 1.17 (even adjacent sum bound).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.even_adjacent_sum_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.even_adjacent_sum_bound` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem even_adjacent_sum_bound {n : ℕ} (hn : n%2=0) (f : Fin n → ℤ) (hf : ∀ i j, (SimpleGraph.pathGraph n).Adj i j → f i+f j ≤ 2) : (∑ i, f i) ≤ n.

**Theorem 1.18 (odd ladder rigidity).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.odd_ladder_rigidity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.odd_ladder_rigidity` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem odd_ladder_rigidity {n : ℕ} (hn : n%2=1) (c : Fin n → ℕ) (hcap : ∀ i, c i≤2) (hpair : ∀ i j, (SimpleGraph.pathGraph n).Adj i j → c i+c j≤2) (htotal : n+1 ≤ ∑ i, c i) : ∀ i, c i=if i.val%2=0 then 2 else 0.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.Compatible`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.card_le_neighbors_of_missing_even`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.even_adjacent_sum_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.even_level_balance`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.even_path_expansion`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.lowerLevel`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.neighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.odd_adjacent_sum_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.odd_ladder_rigidity`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.odd_level_balance`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.odd_path_defect_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.odd_path_defect_support`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.positive_level_forces_alternation`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.profile_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.profile_level_identity`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.sign_sum_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.three_free_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.upperLevel`
- Dependency: [D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives](C4FreeRepresentatives.md)
