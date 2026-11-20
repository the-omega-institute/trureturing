import D5.S3.Combinatorics.SpectralGraph.MandalMannaDQDilworthRefutation
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Distance multiplicity for a universal-clique family of cographs

The graph is the join of a clique with a disjoint union of a balanced complete
bipartite graph and isolated vertices. The family addresses the explicit-family
clause of Open Problem 14.2(ii) in arXiv:2611.06981v1, p. 22.
-/

namespace D5.S3.Combinatorics.SpectralGraph.UniversalCliqueCographDistance

open SimpleGraph
open MandalMannaDQDilworthRefutation (vicinal HasChainCover dilworthNumber)

abbrev Vertex (r s b : ℕ) := Fin r ⊕ ((Fin s ⊕ Fin s) ⊕ Fin b)

variable {r s b : ℕ}

private abbrev hub (i : Fin r) : Vertex r s b := .inl i
private abbrev left (i : Fin s) : Vertex r s b := .inr (.inl (.inl i))
private abbrev right (i : Fin s) : Vertex r s b := .inr (.inl (.inr i))
private abbrev isolate (i : Fin b) : Vertex r s b := .inr (.inr i)

/-- The universal-clique join on its native disjoint-sum carrier. -/
def graph (r s b : ℕ) : SimpleGraph (Vertex r s b) :=
  (((⊤ : SimpleGraph (Fin r))ᶜ).sum
    (((completeBipartiteGraph (Fin s) (Fin s)).sum (⊥ : SimpleGraph (Fin b)))ᶜ))ᶜ

local notation "G" => graph r s b

private theorem hub_universal (i : Fin r) : G.IsUniversal (hub i) := by
  intro v hv
  cases v <;> simpa [graph, ne_comm] using hv

theorem connected (hr : 0 < r) : (graph r s b).Connected :=
  Connected.of_isUniversal (hub_universal ⟨0, hr⟩)

theorem distance (hr : 0 < r) (u v : Vertex r s b) :
    G.dist u v = if u = v then 0 else if G.Adj u v then 1 else 2 := by
  classical
  split_ifs with heq hadj
  · subst v
    exact dist_self
  · exact dist_eq_one_iff_adj.mpr hadj
  · let h : Vertex r s b := hub ⟨0, hr⟩
    have hu : u ≠ h := by
      intro e
      subst u
      exact hadj (hub_universal _ (Ne.symm heq))
    have hv : v ≠ h := by
      intro e
      subst v
      exact hadj (hub_universal _ heq).symm
    have hed := G.edist_eq_two_iff.mpr
      ⟨heq, hadj, h, (hub_universal _ hu).symm, (hub_universal _ hv).symm⟩
    simp [SimpleGraph.dist, hed]

private theorem not_hub_of_nonadjacent {u v : Vertex r s b} (hne : u ≠ v)
    (hn : ¬ G.Adj u v) : ∃ z, u = Sum.inr z := by
  cases u with
  | inl i => exact (hn (hub_universal i hne.symm)).elim
  | inr z => exact ⟨z, rfl⟩

theorem induced_path_excluded (r s b : ℕ) :
    ¬ (pathGraph 4).IsIndContained (graph r s b) := by
  rintro ⟨e⟩
  have nonedge (i j : Fin 4) (h : ¬ (pathGraph 4).Adj i j) :
      ¬ (graph r s b).Adj (e i) (e j) := fun h' => h (e.map_rel_iff.mp h')
  have edge (i j : Fin 4) (h : (pathGraph 4).Adj i j) :
      (graph r s b).Adj (e i) (e j) := e.map_rel_iff.mpr h
  have h02 := nonedge 0 2 (by decide)
  have h13 := nonedge 1 3 (by decide)
  obtain ⟨x0, hx0⟩ := not_hub_of_nonadjacent (e.injective.ne (by decide : (0 : Fin 4) ≠ 2)) h02
  obtain ⟨x1, hx1⟩ := not_hub_of_nonadjacent (e.injective.ne (by decide : (1 : Fin 4) ≠ 3)) h13
  obtain ⟨x2, hx2⟩ := not_hub_of_nonadjacent (e.injective.ne (by decide : (2 : Fin 4) ≠ 0))
    (fun h => h02 h.symm)
  obtain ⟨x3, hx3⟩ := not_hub_of_nonadjacent (e.injective.ne (by decide : (3 : Fin 4) ≠ 1))
    (fun h => h13 h.symm)
  have h01 := edge 0 1 (by decide)
  have h12 := edge 1 2 (by decide)
  have h23 := edge 2 3 (by decide)
  have h03 := nonedge 0 3 (by decide)
  rw [hx0, hx1] at h01
  rw [hx1, hx2] at h12
  rw [hx2, hx3] at h23
  rw [hx0, hx3] at h03
  rcases x0 with (i | i) | i <;> rcases x1 with (j | j) | j <;>
    simp [graph, completeBipartiteGraph_adj] at h01
  all_goals
    rcases x2 with (k | k) | k <;> simp [graph, completeBipartiteGraph_adj] at h12
  all_goals
    rcases x3 with (l | l) | l <;> simp [graph, completeBipartiteGraph_adj] at h23
  all_goals
    simp [graph, completeBipartiteGraph_adj] at h03

private theorem vicinal_hub (u : Vertex r s b) (i : Fin r) : vicinal G u (hub i) := by
  intro w _
  by_cases h : w = hub i
  · exact Or.inl h
  · exact Or.inr (hub_universal i h)

private theorem vicinal_left (i j : Fin s) : vicinal G (left i) (left j) := by
  intro w h
  refine Or.inr ?_
  rcases w with x | ((x | x) | x) <;>
    simp_all [graph, completeBipartiteGraph_adj, mem_neighborSet]

private theorem vicinal_right (i j : Fin s) : vicinal G (right i) (right j) := by
  intro w h
  refine Or.inr ?_
  rcases w with x | ((x | x) | x) <;>
    simp_all [graph, completeBipartiteGraph_adj, mem_neighborSet]

private theorem vicinal_isolate (i : Fin b) (u : Vertex r s b) : vicinal G (isolate i) u := by
  intro w h
  rcases w with x | ((x | x) | x)
  · by_cases he : hub x = u
    · exact Or.inl he
    · exact Or.inr (hub_universal x he.symm).symm
  all_goals simp [graph, completeBipartiteGraph_adj, mem_neighborSet] at h

private def chain (v : Vertex r s b) : Fin 2 :=
  match v with
  | .inr (.inl (.inr _)) => 1
  | _ => 0

theorem two_chain_cover (r s b : ℕ) : HasChainCover (graph r s b) 2 := by
  refine ⟨chain, ?_⟩
  intro u v h
  rcases u with i | ((i | i) | i) <;> rcases v with j | ((j | j) | j) <;>
    first
    | exact Or.inr (vicinal_hub _ _)
    | exact Or.inl (vicinal_hub _ _)
    | exact Or.inl (vicinal_left _ _)
    | exact Or.inl (vicinal_right _ _)
    | exact Or.inl (vicinal_isolate _ _)
    | exact Or.inr (vicinal_isolate _ _)
    | exfalso; exact (by decide : (0 : Fin 2) ≠ 1) h
    | exfalso; exact (by decide : (1 : Fin 2) ≠ 0) h

theorem incomparable_parts (hs : 2 ≤ s) (i j : Fin s) :
    ¬ vicinal G (left i) (right j) ∧ ¬ vicinal G (right j) (left i) := by
  have other (x : Fin s) : ∃ y : Fin s, y ≠ x := by
    let z : Fin s := ⟨0, by omega⟩
    let o : Fin s := ⟨1, by omega⟩
    by_cases h : x = z
    · refine ⟨o, ?_⟩
      intro h'
      have := congrArg Fin.val (h'.trans h)
      contradiction
    · exact ⟨z, Ne.symm h⟩
  obtain ⟨j', hj⟩ := other j
  obtain ⟨i', hi⟩ := other i
  constructor
  · intro h
    have hh := h (show right j' ∈ G.neighborSet (left i) by
      simp [graph, completeBipartiteGraph_adj, mem_neighborSet])
    simpa [graph, completeBipartiteGraph_adj, mem_neighborSet, hj] using hh
  · intro h
    have hh := h (show left i' ∈ G.neighborSet (right j) by
      simp [graph, completeBipartiteGraph_adj, mem_neighborSet])
    simpa [graph, completeBipartiteGraph_adj, mem_neighborSet, hi] using hh

theorem width (hs : 2 ≤ s) : dilworthNumber G = 2 := by
  apply le_antisymm
  · exact sInf_le ⟨2, by norm_num, two_chain_cover r s b⟩
  · apply le_sInf
    rintro _ ⟨k, rfl, c, hc⟩
    have hk : 2 ≤ k := by
      by_contra! hk
      let i : Fin s := ⟨0, by omega⟩
      have hval := (c (left i)).isLt
      have hval' := (c (right i)).isLt
      have heq : c (left i) = c (right i) := Fin.ext (by omega)
      have hn := incomparable_parts (r := r) (b := b) hs i i
      exact (hc _ _ heq).elim hn.1 hn.2
    exact_mod_cast hk

end D5.S3.Combinatorics.SpectralGraph.UniversalCliqueCographDistance
