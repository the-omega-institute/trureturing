/- GID: D5/S3/Combinatorics/CycleSums/ConsecutiveCycleSumsGraph
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CycleSums/ConsecutiveCycleSumsGraph
   mirror-E: none(waiver:elementary-graph-construction)
   anchors: []
   utility: none
   digest: A hub and consecutive tail paths connect the sets used for cycle sums. -/

import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Combinatorics.CycleSums.ConsecutiveCycleSumsGraph

/-- Vertices whose labels belong to a finite set of positive integers. -/
def vertices (n : ℕ) (S : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => v.val + 1 ∈ S)

@[simp] theorem mem_vertices {n : ℕ} {S : Finset ℕ} {v : Fin n} :
    v ∈ vertices n S ↔ v.val + 1 ∈ S := by simp [vertices]

/-- Translating bounded positive labels to vertices preserves their sum. -/
theorem sum_vertices {n : ℕ} {S : Finset ℕ}
    (hS : ∀ x ∈ S, 1 ≤ x ∧ x ≤ n) :
    (∑ v ∈ vertices n S, (v.val + 1)) = ∑ x ∈ S, x := by
  apply Finset.sum_bij (fun v _ => v.val + 1)
  · intro v hv
    exact mem_vertices.mp hv
  · intro v hv w hw he
    exact Fin.ext (by omega)
  · intro x hx
    have h := hS x hx
    refine ⟨⟨x - 1, by omega⟩, ?_, by dsimp; omega⟩
    apply mem_vertices.mpr
    simpa [Nat.sub_add_cancel h.1] using hx
  · intro v hv
    rfl

/-- The star edges join label one to labels three through `k+1`. -/
private def starEdges (n k : ℕ) (hn : 0 < n) : Finset (Sym2 (Fin n)) :=
  (Finset.univ.filter (fun v : Fin n => 2 ≤ v.val ∧ v.val ≤ k)).image
    (fun v => s(⟨0, hn⟩, v))

/-- The original cycle with the star edges adjoined. -/
def completion (n k : ℕ) (hn : 0 < n) : SimpleGraph (Fin n) :=
  SimpleGraph.cycleGraph n ⊔ SimpleGraph.fromEdgeSet (starEdges n k hn : Set (Sym2 (Fin n)))

theorem cycle_le_completion (n k : ℕ) (hn : 0 < n) :
    SimpleGraph.cycleGraph n ≤ completion n k hn := le_sup_left

private theorem star_card {n k : ℕ} (hn : 0 < n) :
    (starEdges n k hn).card ≤ k - 1 := by
  classical
  unfold starEdges
  refine (Finset.card_image_le).trans ?_
  let S := Finset.univ.filter (fun v : Fin n => 2 ≤ v.val ∧ v.val ≤ k)
  have hinj : Set.InjOn (fun v : Fin n => v.val) (S : Set (Fin n)) := by
    intro v hv w hw h
    exact Fin.ext h
  have hsub : S.image (fun v => v.val) ⊆ Finset.Icc 2 k := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    simpa [S] using hv
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj] at hcard
  simpa [S, Nat.card_Icc] using hcard

/-- At most `k-1` new edges are used. -/
theorem added_edges_le {n k : ℕ} (hn : 0 < n) :
    ((completion n k hn).edgeSet \ (SimpleGraph.cycleGraph n).edgeSet).ncard ≤ k - 1 := by
  have hsub : (completion n k hn).edgeSet \ (SimpleGraph.cycleGraph n).edgeSet ⊆
      (starEdges n k hn : Set (Sym2 (Fin n))) := by
    intro e he
    rw [completion, SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_fromEdgeSet] at he
    exact (he.1.resolve_left he.2).1
  exact (Set.ncard_le_ncard hsub).trans (by simpa using star_card hn)

private theorem successive_adj {n k : ℕ} (hn : 0 < n) {u v : Fin n}
    (h : u.val + 1 = v.val) : (completion n k hn).Adj u v :=
  cycle_le_completion n k hn (SimpleGraph.pathGraph_le_cycleGraph
    (SimpleGraph.pathGraph_adj.mpr (Or.inl h)))

private theorem hub_adj {n k : ℕ} (hn : 0 < n) {v : Fin n}
    (hv : 1 ≤ v.val ∧ v.val ≤ k) :
    (completion n k hn).Adj ⟨0, hn⟩ v := by
  by_cases h : v.val = 1
  · exact successive_adj hn (by simpa using h.symm)
  · apply (show SimpleGraph.fromEdgeSet (starEdges n k hn : Set (Sym2 (Fin n))) ≤
        completion n k hn from le_sup_right)
    apply (SimpleGraph.fromEdgeSet_adj _).mpr
    constructor
    · apply Finset.mem_image.mpr
      exact ⟨v, by simp; omega, rfl⟩
    · intro he
      have he := congrArg Fin.val he
      dsimp at he
      omega

/-- A lower-labelled neighbour inside the set gives a path to the least-labelled root. -/
private theorem connected_of_predecessor {n : ℕ} {G : SimpleGraph (Fin n)}
    {C : Finset (Fin n)} (r : Fin n) (hr : r ∈ C)
    (hp : ∀ v ∈ C, v ≠ r → ∃ u ∈ C, u.val < v.val ∧ G.Adj u v) :
    (G.induce (C : Set (Fin n))).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨⟨r, hr⟩, ?_⟩
  have reach : ∀ m : ℕ, ∀ (v : Fin n) (hv : v ∈ C), v.val = m →
      (G.induce (C : Set (Fin n))).Reachable ⟨r, hr⟩ ⟨v, hv⟩ := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro v hv hm
      by_cases he : v = r
      · subst v
        exact SimpleGraph.Reachable.rfl
      · obtain ⟨u, hu, huv, hadj⟩ := hp v hv he
        exact (ih u.val (by omega) u hu rfl).trans
          (show (G.induce (C : Set (Fin n))).Adj ⟨u, hu⟩ ⟨v, hv⟩ from hadj).reachable
  intro v
  exact reach v.val.val v.val v.property rfl

/-- Any core subset containing the hub, together with a tail prefix, is connected. -/
theorem hub_tail_connected {n k j : ℕ} (hn : 0 < n) (_hk : k < n)
    (_hj : k ≤ j) (_hjn : j ≤ n) (S : Finset ℕ)
    (hS : ∀ x ∈ S, 2 ≤ x ∧ x ≤ k) :
    (completion n k hn |>.induce
      (vertices n (insert 1 (S ∪ Finset.Icc (k + 1) j)) : Set (Fin n))).Connected := by
  classical
  let C := vertices n (insert 1 (S ∪ Finset.Icc (k + 1) j))
  have hr : (⟨0, hn⟩ : Fin n) ∈ C := by simp [C]
  apply connected_of_predecessor ⟨0, hn⟩ hr
  intro v hv he
  have hv0 : 0 < v.val := by
    by_contra h
    apply he
    exact Fin.ext (by dsimp; omega)
  by_cases hvk : v.val ≤ k
  · exact ⟨⟨0, hn⟩, hr, hv0, hub_adj hn ⟨hv0, hvk⟩⟩
  · have hvlabel : v.val + 1 ∈ insert 1 (S ∪ Finset.Icc (k + 1) j) :=
      mem_vertices.mp hv
    have hvj : v.val + 1 ≤ j := by
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_Icc] at hvlabel
      rcases hvlabel with h | h | h
      · omega
      · have := hS _ h
        omega
      · omega
    let u : Fin n := ⟨v.val - 1, by omega⟩
    have hu : u ∈ C := by
      apply mem_vertices.mpr
      apply Finset.mem_insert_of_mem
      apply Finset.mem_union_right
      apply Finset.mem_Icc.mpr
      dsimp [u]
      omega
    exact ⟨u, hu, by dsimp [u]; omega, successive_adj hn (by dsimp [u]; omega)⟩

/-- A consecutive interval of positive labels induces a connected path. -/
theorem interval_connected {n k l j : ℕ} (hn : 0 < n)
    (hl : 1 ≤ l) (hlj : l ≤ j) (hjn : j ≤ n) :
    (completion n k hn |>.induce (vertices n (Finset.Icc l j) : Set (Fin n))).Connected := by
  classical
  let r : Fin n := ⟨l - 1, by omega⟩
  have hr : r ∈ vertices n (Finset.Icc l j) := by
    simp only [mem_vertices, Finset.mem_Icc]
    dsimp [r]
    omega
  apply connected_of_predecessor r hr
  intro v hv he
  have hvlabel := mem_vertices.mp hv
  simp only [Finset.mem_Icc] at hvlabel
  have hvlo : l ≤ v.val := by
    have : v.val ≠ l - 1 := fun h => he (Fin.ext h)
    omega
  let u : Fin n := ⟨v.val - 1, by omega⟩
  have hu : u ∈ vertices n (Finset.Icc l j) := by
    simp only [mem_vertices, Finset.mem_Icc]
    dsimp [u]
    omega
  exact ⟨u, hu, by dsimp [u]; omega, successive_adj hn (by dsimp [u]; omega)⟩

end D5.S3.Combinatorics.CycleSums.ConsecutiveCycleSumsGraph
