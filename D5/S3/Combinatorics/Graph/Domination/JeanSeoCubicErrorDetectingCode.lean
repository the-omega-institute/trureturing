/- GID: D5/S3/Combinatorics/Graph/Domination/JeanSeoCubicErrorDetectingCode
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/JeanSeoCubicErrorDetectingCode
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/Domination/JeanSeoCubicErrorDetectingCode.claim; result=D5/S3/Combinatorics/Graph/Domination/JeanSeoCubicErrorDetectingCode.result; claim=D5/S3/Combinatorics/Graph/Domination/JeanSeoCubicErrorDetectingCode.claim
   digest: A connected cubic graph has an error-detecting code of density 18/25. -/

/-
result:
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#19618; Refuted)
  Direct frozen dependencies: none.
All ten private theorems are bind-only, with consumers:
neighbor_symmetry, neighbor_loopless -> graph;
neighbor_finset -> regular, closed_dominators_eq;
regular, detic, connected, density -> result;
closed_dominators_eq, domination, separation -> detic.
The public result is the designated refutation result (`basis=refutes`) and is
exempt from four-slot escape registration (CLAUDE.md §3.9).
-/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic.FinCases

/-! Binding conventions for D. C. Jean and S. J. Seo, "Optimal Error-detection system for Identifying Codes",
arXiv:2208.06052v1 (published as "Optimal error-detection system for identifying codes", Networks 85 (2025) 61–75,
DOI 10.1002/net.22254): the closed dominators `N_S[u] = N[u] ∩ S`, error-detecting identifying codes (DET:IC) by
Theorem 2.1 ("each vertex is at least 2-dominated and all pairs are 2#-distinguished"), and Conjecture 1, "For a cubic
graph G, DET:IC%(G) ≥ 3/4". -/

namespace D5.S3.Combinatorics.Graph.Domination.JeanSeoCubicErrorDetectingCode

/-- `N_S[u] = N[u] ∩ S`, where `N[u] = N(u) ∪ {u}` is the closed neighborhood. -/
def closedDominators {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (u : V) : Finset V :=
  (G.neighborFinset u ∪ {u}) ∩ S

/-- Theorem 2.1 with Definitions 1 and 3: `S` is a DET:IC if and only if each vertex is at least 2-dominated
(`|N_S[v]| ≥ 2`) and all pairs are 2#-distinguished (`|N_S[u] − N_S[v]| ≥ 2` or `|N_S[v] − N_S[u]| ≥ 2`). -/
def IsDETIC {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : Prop :=
  (∀ v, 2 ≤ (closedDominators G S v).card) ∧
    ∀ u v, u ≠ v →
      2 ≤ (closedDominators G S u \ closedDominators G S v).card ∨
        2 ≤ (closedDominators G S v \ closedDominators G S u).card

/-- Conjecture 1: for a (finite, simple, connected) cubic graph `G`, `DET:IC%(G) ≥ 3/4`; that is, every DET:IC `S`
of `G` has density `|S| / |V(G)| ≥ 3/4`. -/
def claim : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsRegularOfDegree 3 → G.Connected →
      ∀ S : Finset V, IsDETIC G S → (3 : ℚ) / 4 ≤ (S.card : ℚ) / Fintype.card V

end D5.S3.Combinatorics.Graph.Domination.JeanSeoCubicErrorDetectingCode

set_option maxRecDepth 100000
set_option maxHeartbeats 500000

namespace D5.S3.Combinatorics.Graph.Domination.JeanSeoCubicErrorDetectingCode

private def neighbors (v : Fin 50) : Finset (Fin 50) :=
  match v.val with
  | 0 => {14, 15, 16}
  | 1 => {14, 17, 18}
  | 2 => {15, 19, 20}
  | 3 => {17, 19, 21}
  | 4 => {20, 22, 23}
  | 5 => {21, 22, 24}
  | 6 => {16, 23, 25}
  | 7 => {18, 24, 25}
  | 8 => {9, 38, 39}
  | 9 => {8, 40, 41}
  | 10 => {11, 42, 43}
  | 11 => {10, 44, 45}
  | 12 => {13, 46, 47}
  | 13 => {12, 48, 49}
  | 14 => {0, 1, 26}
  | 15 => {0, 2, 27}
  | 16 => {0, 6, 28}
  | 17 => {1, 3, 29}
  | 18 => {1, 7, 30}
  | 19 => {2, 3, 31}
  | 20 => {2, 4, 32}
  | 21 => {3, 5, 33}
  | 22 => {4, 5, 34}
  | 23 => {4, 6, 35}
  | 24 => {5, 7, 36}
  | 25 => {6, 7, 37}
  | 26 => {14, 38, 49}
  | 27 => {15, 38, 39}
  | 28 => {16, 39, 40}
  | 29 => {17, 40, 41}
  | 30 => {18, 41, 42}
  | 31 => {19, 42, 43}
  | 32 => {20, 43, 44}
  | 33 => {21, 44, 45}
  | 34 => {22, 45, 46}
  | 35 => {23, 46, 47}
  | 36 => {24, 47, 48}
  | 37 => {25, 48, 49}
  | 38 => {8, 26, 27}
  | 39 => {8, 27, 28}
  | 40 => {9, 28, 29}
  | 41 => {9, 29, 30}
  | 42 => {10, 30, 31}
  | 43 => {10, 31, 32}
  | 44 => {11, 32, 33}
  | 45 => {11, 33, 34}
  | 46 => {12, 34, 35}
  | 47 => {12, 35, 36}
  | 48 => {13, 36, 37}
  | _ => {13, 26, 37}

private theorem neighbor_symmetry : ∀ u v : Fin 50, v ∈ neighbors u ↔ u ∈ neighbors v := by
  intro u
  fin_cases u <;> decide +kernel

private theorem neighbor_loopless : ∀ u : Fin 50, u ∉ neighbors u := by
  decide +kernel

private def graph : SimpleGraph (Fin 50) where
  Adj u v := v ∈ neighbors u
  symm := ⟨fun {u v} h => (neighbor_symmetry u v).mp h⟩
  loopless := ⟨neighbor_loopless⟩

private instance graphAdjDecidable : DecidableRel graph.Adj := fun u v => inferInstanceAs (Decidable (v ∈ neighbors u))

private theorem neighbor_finset (v : Fin 50) : graph.neighborFinset v = neighbors v := by
  exact @Finset.toFinset_coe (Fin 50) (neighbors v) (inferInstanceAs (Fintype (graph.neighborSet v)))

private theorem regular : graph.IsRegularOfDegree 3 := by
  intro v
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighbor_finset]
  fin_cases v <;> decide +kernel

private def code : Finset (Fin 50) := Finset.univ.filter (fun v => 14 ≤ v.val)

private def dominators (v : Fin 50) : Finset (Fin 50) :=
  match v.val with
  | 0 => {14, 15, 16}
  | 1 => {14, 17, 18}
  | 2 => {15, 19, 20}
  | 3 => {17, 19, 21}
  | 4 => {20, 22, 23}
  | 5 => {21, 22, 24}
  | 6 => {16, 23, 25}
  | 7 => {18, 24, 25}
  | 8 => {38, 39}
  | 9 => {40, 41}
  | 10 => {42, 43}
  | 11 => {44, 45}
  | 12 => {46, 47}
  | 13 => {48, 49}
  | 14 => {14, 26}
  | 15 => {15, 27}
  | 16 => {16, 28}
  | 17 => {17, 29}
  | 18 => {18, 30}
  | 19 => {19, 31}
  | 20 => {20, 32}
  | 21 => {21, 33}
  | 22 => {22, 34}
  | 23 => {23, 35}
  | 24 => {24, 36}
  | 25 => {25, 37}
  | 26 => {14, 26, 38, 49}
  | 27 => {15, 27, 38, 39}
  | 28 => {16, 28, 39, 40}
  | 29 => {17, 29, 40, 41}
  | 30 => {18, 30, 41, 42}
  | 31 => {19, 31, 42, 43}
  | 32 => {20, 32, 43, 44}
  | 33 => {21, 33, 44, 45}
  | 34 => {22, 34, 45, 46}
  | 35 => {23, 35, 46, 47}
  | 36 => {24, 36, 47, 48}
  | 37 => {25, 37, 48, 49}
  | 38 => {26, 27, 38}
  | 39 => {27, 28, 39}
  | 40 => {28, 29, 40}
  | 41 => {29, 30, 41}
  | 42 => {30, 31, 42}
  | 43 => {31, 32, 43}
  | 44 => {32, 33, 44}
  | 45 => {33, 34, 45}
  | 46 => {34, 35, 46}
  | 47 => {35, 36, 47}
  | 48 => {36, 37, 48}
  | _ => {26, 37, 49}

private theorem closed_dominators_eq : ∀ v : Fin 50, closedDominators graph code v = dominators v := by
  intro v
  rw [closedDominators, neighbor_finset]
  fin_cases v <;> decide +kernel

private theorem domination : ∀ v : Fin 50, 2 ≤ (dominators v).card := by
  intro v
  fin_cases v <;> decide +kernel

private theorem separation : ∀ u v : Fin 50, u ≠ v →
    2 ≤ (dominators u \ dominators v).card ∨ 2 ≤ (dominators v \ dominators u).card := by
  intro u
  fin_cases u <;> decide +kernel

private theorem detic : IsDETIC graph code := by
  constructor
  · simpa only [closed_dominators_eq] using domination
  · simpa only [closed_dominators_eq] using separation

private theorem connected : graph.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable graph).mpr
  refine ⟨0, ?_⟩
  have h0 : graph.Reachable (0 : Fin 50) 0 := SimpleGraph.Reachable.refl 0
  have h14 : graph.Reachable (0 : Fin 50) 14 := h0.trans (show graph.Adj 0 14 from by decide).reachable
  have h15 : graph.Reachable (0 : Fin 50) 15 := h0.trans (show graph.Adj 0 15 from by decide).reachable
  have h16 : graph.Reachable (0 : Fin 50) 16 := h0.trans (show graph.Adj 0 16 from by decide).reachable
  have h1 : graph.Reachable (0 : Fin 50) 1 := h14.trans (show graph.Adj 14 1 from by decide).reachable
  have h26 : graph.Reachable (0 : Fin 50) 26 := h14.trans (show graph.Adj 14 26 from by decide).reachable
  have h2 : graph.Reachable (0 : Fin 50) 2 := h15.trans (show graph.Adj 15 2 from by decide).reachable
  have h27 : graph.Reachable (0 : Fin 50) 27 := h15.trans (show graph.Adj 15 27 from by decide).reachable
  have h6 : graph.Reachable (0 : Fin 50) 6 := h16.trans (show graph.Adj 16 6 from by decide).reachable
  have h28 : graph.Reachable (0 : Fin 50) 28 := h16.trans (show graph.Adj 16 28 from by decide).reachable
  have h17 : graph.Reachable (0 : Fin 50) 17 := h1.trans (show graph.Adj 1 17 from by decide).reachable
  have h18 : graph.Reachable (0 : Fin 50) 18 := h1.trans (show graph.Adj 1 18 from by decide).reachable
  have h38 : graph.Reachable (0 : Fin 50) 38 := h26.trans (show graph.Adj 26 38 from by decide).reachable
  have h49 : graph.Reachable (0 : Fin 50) 49 := h26.trans (show graph.Adj 26 49 from by decide).reachable
  have h19 : graph.Reachable (0 : Fin 50) 19 := h2.trans (show graph.Adj 2 19 from by decide).reachable
  have h20 : graph.Reachable (0 : Fin 50) 20 := h2.trans (show graph.Adj 2 20 from by decide).reachable
  have h39 : graph.Reachable (0 : Fin 50) 39 := h27.trans (show graph.Adj 27 39 from by decide).reachable
  have h23 : graph.Reachable (0 : Fin 50) 23 := h6.trans (show graph.Adj 6 23 from by decide).reachable
  have h25 : graph.Reachable (0 : Fin 50) 25 := h6.trans (show graph.Adj 6 25 from by decide).reachable
  have h40 : graph.Reachable (0 : Fin 50) 40 := h28.trans (show graph.Adj 28 40 from by decide).reachable
  have h3 : graph.Reachable (0 : Fin 50) 3 := h17.trans (show graph.Adj 17 3 from by decide).reachable
  have h29 : graph.Reachable (0 : Fin 50) 29 := h17.trans (show graph.Adj 17 29 from by decide).reachable
  have h7 : graph.Reachable (0 : Fin 50) 7 := h18.trans (show graph.Adj 18 7 from by decide).reachable
  have h30 : graph.Reachable (0 : Fin 50) 30 := h18.trans (show graph.Adj 18 30 from by decide).reachable
  have h8 : graph.Reachable (0 : Fin 50) 8 := h38.trans (show graph.Adj 38 8 from by decide).reachable
  have h13 : graph.Reachable (0 : Fin 50) 13 := h49.trans (show graph.Adj 49 13 from by decide).reachable
  have h37 : graph.Reachable (0 : Fin 50) 37 := h49.trans (show graph.Adj 49 37 from by decide).reachable
  have h31 : graph.Reachable (0 : Fin 50) 31 := h19.trans (show graph.Adj 19 31 from by decide).reachable
  have h4 : graph.Reachable (0 : Fin 50) 4 := h20.trans (show graph.Adj 20 4 from by decide).reachable
  have h32 : graph.Reachable (0 : Fin 50) 32 := h20.trans (show graph.Adj 20 32 from by decide).reachable
  have h35 : graph.Reachable (0 : Fin 50) 35 := h23.trans (show graph.Adj 23 35 from by decide).reachable
  have h9 : graph.Reachable (0 : Fin 50) 9 := h40.trans (show graph.Adj 40 9 from by decide).reachable
  have h21 : graph.Reachable (0 : Fin 50) 21 := h3.trans (show graph.Adj 3 21 from by decide).reachable
  have h41 : graph.Reachable (0 : Fin 50) 41 := h29.trans (show graph.Adj 29 41 from by decide).reachable
  have h24 : graph.Reachable (0 : Fin 50) 24 := h7.trans (show graph.Adj 7 24 from by decide).reachable
  have h42 : graph.Reachable (0 : Fin 50) 42 := h30.trans (show graph.Adj 30 42 from by decide).reachable
  have h12 : graph.Reachable (0 : Fin 50) 12 := h13.trans (show graph.Adj 13 12 from by decide).reachable
  have h48 : graph.Reachable (0 : Fin 50) 48 := h13.trans (show graph.Adj 13 48 from by decide).reachable
  have h43 : graph.Reachable (0 : Fin 50) 43 := h31.trans (show graph.Adj 31 43 from by decide).reachable
  have h22 : graph.Reachable (0 : Fin 50) 22 := h4.trans (show graph.Adj 4 22 from by decide).reachable
  have h44 : graph.Reachable (0 : Fin 50) 44 := h32.trans (show graph.Adj 32 44 from by decide).reachable
  have h46 : graph.Reachable (0 : Fin 50) 46 := h35.trans (show graph.Adj 35 46 from by decide).reachable
  have h47 : graph.Reachable (0 : Fin 50) 47 := h35.trans (show graph.Adj 35 47 from by decide).reachable
  have h5 : graph.Reachable (0 : Fin 50) 5 := h21.trans (show graph.Adj 21 5 from by decide).reachable
  have h33 : graph.Reachable (0 : Fin 50) 33 := h21.trans (show graph.Adj 21 33 from by decide).reachable
  have h36 : graph.Reachable (0 : Fin 50) 36 := h24.trans (show graph.Adj 24 36 from by decide).reachable
  have h10 : graph.Reachable (0 : Fin 50) 10 := h42.trans (show graph.Adj 42 10 from by decide).reachable
  have h34 : graph.Reachable (0 : Fin 50) 34 := h22.trans (show graph.Adj 22 34 from by decide).reachable
  have h11 : graph.Reachable (0 : Fin 50) 11 := h44.trans (show graph.Adj 44 11 from by decide).reachable
  have h45 : graph.Reachable (0 : Fin 50) 45 := h33.trans (show graph.Adj 33 45 from by decide).reachable
  intro v
  fin_cases v <;> assumption

private theorem density : (code.card : ℚ) / Fintype.card (Fin 50) < (3 : ℚ) / 4 := by
  decide +kernel

theorem result : ¬ claim := by
  intro h
  exact (not_le_of_gt density) (h (Fin 50) graph regular connected code detic)

end D5.S3.Combinatorics.Graph.Domination.JeanSeoCubicErrorDetectingCode
