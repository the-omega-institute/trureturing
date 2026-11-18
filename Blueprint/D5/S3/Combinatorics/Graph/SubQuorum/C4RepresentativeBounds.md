# General C4-free representative bounds

## Abstract

General C4-free representative bounds

Actual finite representative maxima and graph-level pair ownership prove beta<=psiSq<=Omega, the equal-side regular C4-free threshold, positive-excess matching budgets and support rigidity. Projective-plane specializations keep their precise degree, cardinality and unique-pair hypotheses. These proofs concern arbitrary finite graphs; they do not assert rectangular-grid equality.

**Definition 1.1 (NoFourCycle).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.NoFourCycle`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.NoFourCycle` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def NoFourCycle {Vertex : Type} (adjacency : Vertex → Vertex → Prop) : Prop.

**Theorem 1.2 (neighbor pair unique owner).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.neighbor_pair_unique_owner`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.neighbor_pair_unique_owner` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem neighbor_pair_unique_owner {Vertex : Type} {adjacency : Vertex → Vertex → Prop} (hfree : NoFourCycle adjacency) (first second left right : Vertex) (hpair : left ≠ right) (hfirstLeft : first ≠ left) (hfirstRight : first ≠ right) (hsecondLeft : second ≠ left) (hsecondRight : second ≠ right) (hfirstEdge : adjacency first left) (hfirstOther : adjacency first right) (hsecondEdge : adjacency second left) (hsecondOther : adjacency second right) : first = second.

**Theorem 1.3 (pair packing).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.pair_packing`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.pair_packing` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem pair_packing {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hfree : NoFourCycle G.Adj) (U B : Finset V) (hUB : Disjoint U B) : (∑ u ∈ U, ((B.filter (G.Adj u)).card * ((B.filter (G.Adj u)).card - 1))) ≤ B.card * (B.card - 1).

**Theorem 1.4 (pair packing lower).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.pair_packing_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.pair_packing_lower` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem pair_packing_lower {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hfree : NoFourCycle G.Adj) (U B : Finset V) (hUB : Disjoint U B) (k : ℕ) (hk : ∀ u ∈ U, k ≤ (B.filter (G.Adj u)).card) : k * (k - 1) * U.card ≤ B.card * (B.card - 1).

**Definition 1.5 (endpoints).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.endpoints`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.endpoints` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def endpoints (M : Finset (V × V)) : Finset V.

**Definition 1.6 (Feasible).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.Feasible`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.Feasible` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: structure Feasible (T : Finset V) (M : Finset (V × V)) : Prop.

**Definition 1.7 (Omega).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.Omega`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.Omega` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: noncomputable def Omega : ℕ. The supremum ranges over all actual feasible singleton and matching pairs.

**Theorem 1.8 (objective le omega).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.objective_le_omega`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.objective_le_omega` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem objective_le_omega (T : Finset V) (M : Finset (V × V)) (h : Feasible G T M) : T.card + M.card ≤ Omega G.

**Theorem 1.9 (Omega upper from all feasible pairs).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.omega_upper_of_objective_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.omega_upper_of_objective_bound` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem omega_upper_of_objective_bound (n : ℕ) (h : ∀ T M, Feasible G T M → T.card + M.card ≤ n) : Omega G ≤ n. The finite Pappus maximum is its actual consumer.

**Theorem 1.10 (dissociation feasible).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.dissociation_feasible`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.dissociation_feasible` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dissociation_feasible (T : Finset V) (hT : IsKIndependent G 2 T) : Feasible G T ∅.

**Theorem 1.11 (positive excess budget).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.positive_excess_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.positive_excess_budget` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem positive_excess_budget (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hfree : NoFourCycle G.Adj) (D N : ℕ) (hD : 3 ≤ D) (hr : ∀ v, DegreeCapacity.degree G v = D) (hsides : ∀ c, (Finset.univ.filter (fun v => color v = c)).card = N) (T : Finset V) (M : Finset (V × V)) (hf : Feasible G T M) (hexcess : N < T.card + M.card) : (M.card : ℤ) + ((T.card : ℤ) + M.card - N) ≤ (N : ℤ) - 2 * ((D - 1) * (D - 2) : ℕ) - 4.

**Theorem 1.12 (objective threshold).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.objective_threshold`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.objective_threshold` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem objective_threshold (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hfree : NoFourCycle G.Adj) (D N : ℕ) (hD : 3 ≤ D) (hr : ∀ v, DegreeCapacity.degree G v = D) (hsides : ∀ c, (Finset.univ.filter (fun v => color v = c)).card = N) (hN : N ≤ 2 * (D - 1) * (D - 2) + 4) (T : Finset V) (M : Finset (V × V)) (hf : Feasible G T M) : T.card + M.card ≤ N.

**Theorem 1.13 (objective general bound).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.objective_general_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.objective_general_bound` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem objective_general_bound (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hfree : NoFourCycle G.Adj) (D N : ℕ) (hD : 3 ≤ D) (hr : ∀ v, DegreeCapacity.degree G v = D) (hsides : ∀ c, (Finset.univ.filter (fun v => color v = c)).card = N) (T : Finset V) (M : Finset (V × V)) (hf : Feasible G T M) : T.card + M.card ≤ max N (2*N - 2*((D-1)*(D-2)) - 4).

**Theorem 1.14 (first excess matching empty).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.first_excess_matching_empty`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.first_excess_matching_empty` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem first_excess_matching_empty (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hfree : NoFourCycle G.Adj) (D N : ℕ) (hD : 3 ≤ D) (hr : ∀ v, DegreeCapacity.degree G v = D) (hsides : ∀ c, (Finset.univ.filter (fun v => color v = c)).card = N) (hN : N = 2*((D-1)*(D-2))+5) (T : Finset V) (M : Finset (V × V)) (hf : Feasible G T M) (hc : T.card + M.card = N+1) : M = ∅.

**Theorem 1.15 (zero excess unused).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.zero_excess_unused`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.zero_excess_unused` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem zero_excess_unused (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hfree : NoFourCycle G.Adj) (D N : ℕ) (hr : ∀ v, DegreeCapacity.degree G v = D) (hsides : ∀ c, (Finset.univ.filter (fun v => color v = c)).card = N) (T : Finset V) (M : Finset (V × V)) (hf : Feasible G T M) (hc : T.card + M.card = N) (c : Bool) : (unusedSide T M color c).card = 0 ∨ (D-1)*(D-2)+1 ≤ (unusedSide T M color c).card.

**Theorem 1.16 (objective one side support).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.objective_one_side_support`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.objective_one_side_support` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem objective_one_side_support (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hfree : NoFourCycle G.Adj) (D N : ℕ) (hr : ∀ v, DegreeCapacity.degree G v = D) (hsides : ∀ c, (Finset.univ.filter (fun v => color v = c)).card = N) (hN : N ≤ 2*((D-1)*(D-2))+1) (T : Finset V) (M : Finset (V × V)) (hf : Feasible G T M) (hc : T.card + M.card = N) : ∃ c : Bool, (∀ v ∈ T, color v = c) ∧ (∀ v, color v = c → v ∈ T ∪ endpoints M).

**Theorem 1.17 (coloring representatives).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.coloring_representatives`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.coloring_representatives` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem coloring_representatives {C : Type} [DecidableEq C] (c : V → Option C) (hc : IsSubQuorum G c) : ∃ T : Finset V, ∃ M : Finset (V × V), Feasible G T M ∧ T.card + M.card = (palette c Finset.univ).card ∧ (M = ∅ → ∀ v w, c v ≠ none → c w = c v → ¬ G.Adj v w).

**Theorem 1.18 (palette le omega).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.palette_le_omega`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.palette_le_omega` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem palette_le_omega {C : Type} [DecidableEq C] (c : V → Option C) (hc : IsSubQuorum G c) : (palette c Finset.univ).card ≤ Omega G.

**Theorem 1.19 (psiSq le omega).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.psiSq_le_omega`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.psiSq_le_omega` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem psiSq_le_omega : psiSq G ≤ Omega G.

**Theorem 1.20 (parameter comparison).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.parameter_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.parameter_comparison` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem parameter_comparison : beta G 2 ≤ psiSq G ∧ psiSq G ≤ Omega G.

**Theorem 1.21 (threshold parameters).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.threshold_parameters`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.threshold_parameters` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem threshold_parameters (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hfree : NoFourCycle G.Adj) (D N : ℕ) (hD : 3 ≤ D) (hr : ∀ v, DegreeCapacity.degree G v = D) (hsides : ∀ c, (Finset.univ.filter (fun v => color v = c)).card = N) (hN : N ≤ 2 * (D - 1) * (D - 2) + 4) : beta G 2 = N ∧ psiSq G = N ∧ Omega G = N.

**Theorem 1.22 (plane parameter specialization).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.plane_parameter_specialization`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.plane_parameter_specialization` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem plane_parameter_specialization (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hfree : NoFourCycle G.Adj) (q : ℕ) (hq : 2 ≤ q) (hr : ∀ v, DegreeCapacity.degree G v = q + 1) (hsides : ∀ c, (Finset.univ.filter (fun v => color v = c)).card = q*q+q+1) : beta G 2 = q*q+q+1 ∧ psiSq G = q*q+q+1 ∧ Omega G = q*q+q+1.

**Theorem 1.23 (plane optimal support).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.plane_optimal_support`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.plane_optimal_support` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem plane_optimal_support (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hfree : NoFourCycle G.Adj) (q : ℕ) (hq : 3 ≤ q) (hr : ∀ v, DegreeCapacity.degree G v = q+1) (hsides : ∀ c, (Finset.univ.filter (fun v => color v = c)).card = q*q+q+1) (T : Finset V) (M : Finset (V × V)) (hf : Feasible G T M) (hc : T.card+M.card = q*q+q+1) : ∃ c : Bool, (∀ v ∈ T, color v = c) ∧ (∀ v, color v = c → v ∈ T ∪ endpoints M).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.Feasible`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.NoFourCycle`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.Omega`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.coloring_representatives`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.dissociation_feasible`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.endpoints`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.first_excess_matching_empty`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.neighbor_pair_unique_owner`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.objective_general_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.objective_le_omega`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.objective_one_side_support`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.objective_threshold`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.omega_upper_of_objective_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.pair_packing`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.pair_packing_lower`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.palette_le_omega`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.parameter_comparison`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.plane_optimal_support`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.plane_parameter_specialization`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.positive_excess_budget`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.psiSq_le_omega`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.threshold_parameters`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds.zero_excess_unused`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/RegularCompensation](../StarForming/RegularCompensation.md)
- Dependency: [D5/S3/Combinatorics/Graph/SubQuorum/DissociationColoring](DissociationColoring.md)
