# Actual C4-free representatives, support rigidity and Pappus obstruction

## Abstract

Actual C4-free representatives, support rigidity and Pappus obstruction

The actual finite matching/singleton maximum Omega bounds the actual sub-quorum palette, with beta<=psiSq<=Omega. Graph-level pair ownership and unused-side sums prove the complete equal-side regular C4-free threshold, the positive-excess matching budget and general upper envelope. At the first possible excess the matching part is empty. Objective-N pairs have each unused-side count zero or at least (D-1)(D-2)+1; below the support threshold their singleton support lies on one fully occupied side, including all projective planes of order at least three. The source binary-label q=2 mixed-support optimum is checked separately from the cyclic-label Heawood beta=psiSq=Omega=7<SF=8 result. Pappus has all three parameters ten, every optimal representative matching empty, and every ten-color optimum has dissociation support and distinct colors. None asserts rectangular-grid equality.

**Definition 1.1 (NoFourCycle).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.NoFourCycle`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.NoFourCycle` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def NoFourCycle {Vertex : Type} (adjacency : Vertex → Vertex → Prop) : Prop.

**Theorem 1.2 (neighbor pair unique owner).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.neighbor_pair_unique_owner`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.neighbor_pair_unique_owner` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem neighbor_pair_unique_owner {Vertex : Type} {adjacency : Vertex → Vertex → Prop} (hfree : NoFourCycle adjacency) (first second left right : Vertex) (hpair : left ≠ right) (hfirstLeft : first ≠ left) (hfirstRight : first ≠ right) (hsecondLeft : second ≠ left) (hsecondRight : second ≠ right) (hfirstEdge : adjacency first left) (hfirstOther : adjacency first right) (hsecondEdge : adjacency second left) (hsecondOther : adjacency second right) : first = second.

**Definition 1.3 (pappusNeighbors).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusNeighbors`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusNeighbors` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def pappusNeighbors (vertex : Fin 18) : List Nat.

**Definition 1.4 (pappusSelected).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusSelected`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusSelected` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def pappusSelected : List Nat.

**Theorem 1.5 (pappus regular bipartite certificate).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_regular_bipartite_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_regular_bipartite_certificate` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem pappus_regular_bipartite_certificate : (∀ vertex : Fin 18, (pappusNeighbors vertex).length = 3 ∧ (pappusNeighbors vertex).Nodup ∧ ∀ neighbor, neighbor ∈ pappusNeighbors vertex → neighbor < 18 ∧ neighbor % 2 ≠ vertex.val % 2) ∧ (∀ first second : Fin 18, second.val ∈ pappusNeighbors first ↔ first.val ∈ pappusNeighbors second).

**Theorem 1.6 (pappus no four cycle certificate).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_no_four_cycle_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_no_four_cycle_certificate` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem pappus_no_four_cycle_certificate : ∀ first second : Fin 18, first ≠ second → ((pappusNeighbors first).filter (fun vertex => (pappusNeighbors second).contains vertex)).length ≤ 1.

**Theorem 1.7 (pappus dissociation certificate).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_dissociation_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_dissociation_certificate` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem pappus_dissociation_certificate : pappusSelected.length = 10 ∧ pappusSelected.Nodup ∧ (∀ vertex, vertex ∈ pappusSelected → vertex < 18) ∧ (∀ vertex : Fin 18, vertex.val ∈ pappusSelected → ((pappusNeighbors vertex).filter (fun neighbor => pappusSelected.contains neighbor)).length ≤ 1).

**Theorem 1.8 (pair packing).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pair_packing`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pair_packing` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem pair_packing {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hfree : NoFourCycle G.Adj) (U B : Finset V) (hUB : Disjoint U B) : (∑ u ∈ U, ((B.filter (G.Adj u)).card * ((B.filter (G.Adj u)).card - 1))) ≤ B.card * (B.card - 1).

**Theorem 1.9 (pair packing lower).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pair_packing_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pair_packing_lower` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem pair_packing_lower {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hfree : NoFourCycle G.Adj) (U B : Finset V) (hUB : Disjoint U B) (k : ℕ) (hk : ∀ u ∈ U, k ≤ (B.filter (G.Adj u)).card) : k * (k - 1) * U.card ≤ B.card * (B.card - 1).

**Definition 1.10 (pappusGraph).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusGraph`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusGraph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def pappusGraph : SimpleGraph (Fin 18).

**Definition 1.11 (pappusSet).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusSet`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusSet` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def pappusSet : Finset (Fin 18).

**Theorem 1.12 (pappus class).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_class`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_class` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem pappus_class : pappusGraph.Colorable 2 ∧ (∀ v, DegreeCapacity.degree pappusGraph v = 3) ∧ NoFourCycle pappusGraph.Adj.

**Theorem 1.13 (pappus selection).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_selection`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_selection` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem pappus_selection : IsKIndependent pappusGraph 2 pappusSet ∧ pappusSet.card = 10.

**Theorem 1.14 (beta pappus).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.beta_pappus`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.beta_pappus` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem beta_pappus : beta pappusGraph 2 = 10.

**Definition 1.15 (claim).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.claim`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.claim` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def claim : Prop.

**Theorem 1.16 (result).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.result` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem result : ¬ claim.

**Definition 1.17 (endpoints).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.endpoints`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.endpoints` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def endpoints (M : Finset (V × V)) : Finset V.

**Definition 1.18 (Feasible).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.Feasible`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.Feasible` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: structure Feasible (T : Finset V) (M : Finset (V × V)) : Prop.

**Theorem 1.19 (objective le omega).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.objective_le_omega`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.objective_le_omega` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem objective_le_omega (T : Finset V) (M : Finset (V × V)) (h : Feasible G T M) : T.card + M.card ≤ Omega G.

**Theorem 1.20 (dissociation feasible).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.dissociation_feasible`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.dissociation_feasible` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dissociation_feasible (T : Finset V) (hT : IsKIndependent G 2 T) : Feasible G T ∅.

**Theorem 1.21 (positive excess budget).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.positive_excess_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.positive_excess_budget` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem positive_excess_budget (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hfree : NoFourCycle G.Adj) (D N : ℕ) (hD : 3 ≤ D) (hr : ∀ v, DegreeCapacity.degree G v = D) (hsides : ∀ c, (Finset.univ.filter (fun v => color v = c)).card = N) (T : Finset V) (M : Finset (V × V)) (hf : Feasible G T M) (hexcess : N < T.card + M.card) : (M.card : ℤ) + ((T.card : ℤ) + M.card - N) ≤ (N : ℤ) - 2 * ((D - 1) * (D - 2) : ℕ) - 4.

**Theorem 1.22 (objective threshold).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.objective_threshold`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.objective_threshold` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem objective_threshold (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hfree : NoFourCycle G.Adj) (D N : ℕ) (hD : 3 ≤ D) (hr : ∀ v, DegreeCapacity.degree G v = D) (hsides : ∀ c, (Finset.univ.filter (fun v => color v = c)).card = N) (hN : N ≤ 2 * (D - 1) * (D - 2) + 4) (T : Finset V) (M : Finset (V × V)) (hf : Feasible G T M) : T.card + M.card ≤ N.

**Theorem 1.23 (objective general bound).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.objective_general_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.objective_general_bound` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem objective_general_bound (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hfree : NoFourCycle G.Adj) (D N : ℕ) (hD : 3 ≤ D) (hr : ∀ v, DegreeCapacity.degree G v = D) (hsides : ∀ c, (Finset.univ.filter (fun v => color v = c)).card = N) (T : Finset V) (M : Finset (V × V)) (hf : Feasible G T M) : T.card + M.card ≤ max N (2*N - 2*((D-1)*(D-2)) - 4).

**Theorem 1.24 (first excess matching empty).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.first_excess_matching_empty`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.first_excess_matching_empty` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem first_excess_matching_empty (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hfree : NoFourCycle G.Adj) (D N : ℕ) (hD : 3 ≤ D) (hr : ∀ v, DegreeCapacity.degree G v = D) (hsides : ∀ c, (Finset.univ.filter (fun v => color v = c)).card = N) (hN : N = 2*((D-1)*(D-2))+5) (T : Finset V) (M : Finset (V × V)) (hf : Feasible G T M) (hc : T.card + M.card = N+1) : M = ∅.

**Theorem 1.25 (zero excess unused).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.zero_excess_unused`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.zero_excess_unused` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem zero_excess_unused (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hfree : NoFourCycle G.Adj) (D N : ℕ) (hr : ∀ v, DegreeCapacity.degree G v = D) (hsides : ∀ c, (Finset.univ.filter (fun v => color v = c)).card = N) (T : Finset V) (M : Finset (V × V)) (hf : Feasible G T M) (hc : T.card + M.card = N) (c : Bool) : (unusedSide T M color c).card = 0 ∨ (D-1)*(D-2)+1 ≤ (unusedSide T M color c).card.

**Theorem 1.26 (objective one side support).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.objective_one_side_support`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.objective_one_side_support` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem objective_one_side_support (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hfree : NoFourCycle G.Adj) (D N : ℕ) (hr : ∀ v, DegreeCapacity.degree G v = D) (hsides : ∀ c, (Finset.univ.filter (fun v => color v = c)).card = N) (hN : N ≤ 2*((D-1)*(D-2))+1) (T : Finset V) (M : Finset (V × V)) (hf : Feasible G T M) (hc : T.card + M.card = N) : ∃ c : Bool, (∀ v ∈ T, color v = c) ∧ (∀ v, color v = c → v ∈ T ∪ endpoints M).

**Theorem 1.27 (coloring representatives).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.coloring_representatives`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.coloring_representatives` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem coloring_representatives {C : Type} [DecidableEq C] (c : V → Option C) (hc : IsSubQuorum G c) : ∃ T : Finset V, ∃ M : Finset (V × V), Feasible G T M ∧ T.card + M.card = (palette c Finset.univ).card ∧ (M = ∅ → ∀ v w, c v ≠ none → c w = c v → ¬ G.Adj v w).

**Theorem 1.28 (palette le omega).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.palette_le_omega`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.palette_le_omega` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem palette_le_omega {C : Type} [DecidableEq C] (c : V → Option C) (hc : IsSubQuorum G c) : (palette c Finset.univ).card ≤ Omega G.

**Theorem 1.29 (psiSq le omega).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.psiSq_le_omega`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.psiSq_le_omega` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem psiSq_le_omega : psiSq G ≤ Omega G.

**Theorem 1.30 (parameter comparison).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.parameter_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.parameter_comparison` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem parameter_comparison : beta G 2 ≤ psiSq G ∧ psiSq G ≤ Omega G.

**Theorem 1.31 (threshold parameters).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.threshold_parameters`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.threshold_parameters` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem threshold_parameters (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hfree : NoFourCycle G.Adj) (D N : ℕ) (hD : 3 ≤ D) (hr : ∀ v, DegreeCapacity.degree G v = D) (hsides : ∀ c, (Finset.univ.filter (fun v => color v = c)).card = N) (hN : N ≤ 2 * (D - 1) * (D - 2) + 4) : beta G 2 = N ∧ psiSq G = N ∧ Omega G = N.

**Theorem 1.32 (plane parameter specialization).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.plane_parameter_specialization`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.plane_parameter_specialization` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem plane_parameter_specialization (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hfree : NoFourCycle G.Adj) (q : ℕ) (hq : 2 ≤ q) (hr : ∀ v, DegreeCapacity.degree G v = q + 1) (hsides : ∀ c, (Finset.univ.filter (fun v => color v = c)).card = q*q+q+1) : beta G 2 = q*q+q+1 ∧ psiSq G = q*q+q+1 ∧ Omega G = q*q+q+1.

**Theorem 1.33 (plane optimal support).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.plane_optimal_support`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.plane_optimal_support` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem plane_optimal_support (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hfree : NoFourCycle G.Adj) (q : ℕ) (hq : 3 ≤ q) (hr : ∀ v, DegreeCapacity.degree G v = q+1) (hsides : ∀ c, (Finset.univ.filter (fun v => color v = c)).card = q*q+q+1) (T : Finset V) (M : Finset (V × V)) (hf : Feasible G T M) (hc : T.card+M.card = q*q+q+1) : ∃ c : Bool, (∀ v ∈ T, color v = c) ∧ (∀ v, color v = c → v ∈ T ∪ endpoints M).

**Theorem 1.34 (heawood parameters).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.heawood_parameters`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.heawood_parameters` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem heawood_parameters : beta HeawoodParameters.graph 2 = 7 ∧ psiSq HeawoodParameters.graph = 7 ∧ Omega HeawoodParameters.graph = 7 ∧ SF HeawoodParameters.graph 2 = 8.

**Definition 1.35 (binaryHeawood).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.binaryHeawood`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.binaryHeawood` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def binaryHeawood : SimpleGraph (Fin 14).

**Definition 1.36 (mixedSingletons).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.mixedSingletons`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.mixedSingletons` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def mixedSingletons : Finset (Fin 14).

**Definition 1.37 (mixedMatching).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.mixedMatching`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.mixedMatching` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def mixedMatching : Finset (Fin 14 × Fin 14).

**Theorem 1.38 (mixed support optimum).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.mixed_support_optimum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.mixed_support_optimum` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem mixed_support_optimum : Feasible binaryHeawood mixedSingletons mixedMatching ∧ mixedSingletons.card + mixedMatching.card = Omega binaryHeawood ∧ (mixedSingletons.filter (fun v => heawoodColor v = false)).card = 3 ∧ (mixedSingletons.filter (fun v => heawoodColor v = true)).card = 3.

**Theorem 1.39 (omega pappus).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.omega_pappus`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.omega_pappus` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem omega_pappus : Omega pappusGraph = 10.

**Theorem 1.40 (pappus parameters).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_parameters`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_parameters` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem pappus_parameters : beta pappusGraph 2 = 10 ∧ psiSq pappusGraph = 10 ∧ Omega pappusGraph = 10.

**Theorem 1.41 (pappus optimal matching empty).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_optimal_matching_empty`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_optimal_matching_empty` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem pappus_optimal_matching_empty (T : Finset (Fin 18)) (M : Finset (Fin 18 × Fin 18)) (hf : Feasible pappusGraph T M) (hc : T.card + M.card = 10) : M = ∅.

**Theorem 1.42 (pappus coloring rigidity).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_coloring_rigidity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_coloring_rigidity` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem pappus_coloring_rigidity (c : Fin 18 → Option ℕ) (hc : IsSubQuorum pappusGraph c) (hp : (palette c Finset.univ).card = 10) : IsKIndependent pappusGraph 2 (coloredSupport c Finset.univ) ∧ (coloredSupport c Finset.univ).card = 10 ∧ Set.InjOn c (coloredSupport c Finset.univ).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.Feasible`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.NoFourCycle`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.beta_pappus`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.binaryHeawood`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.coloring_representatives`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.dissociation_feasible`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.endpoints`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.first_excess_matching_empty`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.heawood_parameters`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.mixedMatching`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.mixedSingletons`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.mixed_support_optimum`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.neighbor_pair_unique_owner`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.objective_general_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.objective_le_omega`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.objective_one_side_support`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.objective_threshold`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.omega_pappus`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pair_packing`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pair_packing_lower`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.palette_le_omega`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusNeighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusSelected`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappusSet`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_class`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_coloring_rigidity`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_dissociation_certificate`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_no_four_cycle_certificate`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_optimal_matching_empty`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_parameters`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_regular_bipartite_certificate`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.pappus_selection`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.parameter_comparison`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.plane_optimal_support`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.plane_parameter_specialization`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.positive_excess_budget`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.psiSq_le_omega`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.threshold_parameters`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives.zero_excess_unused`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates](../StarForming/HeawoodCertificates.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters](../StarForming/HeawoodParameters.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/RegularCompensation](../StarForming/RegularCompensation.md)
- Dependency: [D5/S3/Combinatorics/Graph/SubQuorum/DissociationColoring](DissociationColoring.md)
