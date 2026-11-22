/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SevenVertexBipartite
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SevenVertexBipartite
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Bipartite]
   utility: none
   digest: Eleven edges force a four-by-three bipartition of a triangle-free seven-vertex graph. -/

module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Data.Fintype.Card

/-! A dense triangle-free graph on seven vertices has complementary independent parts. -/

set_option autoImplicit false

public section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SevenVertexBipartite

open Finset
open scoped BigOperators

/-- At least eleven edges in a triangle-free graph on seven vertices force
complementary independent parts of sizes four and three. -/
theorem seven_vertex_bipartition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = 7)
    (htriangle : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj z x → False)
    (hE : 11 ≤ G.edgeFinset.card) :
    ∃ A : Finset V, A.card = 4 ∧ (Aᶜ).card = 3 ∧
      G.IsBipartiteWith (A : Set V) (↑(Aᶜ) : Set V) := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by
    rw [hV]
    decide)
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  have hhandshake := G.sum_degrees_eq_twice_card_edges
  have hmax : (∑ x : V, G.degree x) ≤ 7 * G.degree v := calc
    _ ≤ ∑ _x : V, G.degree v := sum_le_sum fun x _ =>
      (G.degree_le_maxDegree x).trans (Nat.le_of_eq hv)
    _ = _ := by simp only [sum_const, card_univ, hV, smul_eq_mul]
  let A := G.neighborFinset v
  let B := Aᶜ
  have hAcard : A.card = G.degree v := G.card_neighborFinset_eq_degree v
  have hAmin : 4 ≤ A.card := by omega
  have hAB : A.card + B.card = 7 := (card_add_card_compl A).trans hV
  have hvB : v ∈ B := mem_compl.mpr (G.notMem_neighborFinset_self v)
  have hvNo {x : V} (hx : x ∈ B) : ¬G.Adj v x :=
    fun h => mem_compl.mp hx ((G.mem_neighborFinset v x).mpr h)
  have hA (x : V) (hx : x ∈ A) (y : V) (hy : y ∈ A) : ¬G.Adj x y :=
    fun h => htriangle v x y ((G.mem_neighborFinset v x).mp hx) h
      ((G.mem_neighborFinset v y).mp hy).symm
  let d (S : Finset V) (x : V) := (S.filter (G.Adj x)).card
  have hcap (S : Finset V) (x : V) : d S x ≤ S.card :=
    card_filter_le S (G.Adj x)
  have hzero (S : Finset V) (hind : ∀ x ∈ S, ∀ y ∈ S, ¬G.Adj x y) :
      (∑ x ∈ S, d S x) = 0 := by
    apply sum_eq_zero
    intro x hx
    exact card_filter_eq_zero_iff.mpr (hind x hx)
  have hsplit (x : V) : d A x + d B x = G.degree x := by
    have hd : Disjoint (A.filter (G.Adj x)) (B.filter (G.Adj x)) :=
      disjoint_left.mpr fun _ hyA hyB =>
        mem_compl.mp (mem_filter.mp hyB).1 (mem_filter.mp hyA).1
    have hcover : A ∪ B = univ := union_compl A
    rw [← G.card_neighborFinset_eq_degree x, G.neighborFinset_eq_filter]
    change (A.filter (G.Adj x)).card + (B.filter (G.Adj x)).card =
      (univ.filter (G.Adj x)).card
    rw [← card_union_of_disjoint hd, ← filter_union, hcover]
  have hswap : (∑ x ∈ A, d B x) = ∑ y ∈ B, d A y := calc
    _ = ∑ y ∈ B, (A.bipartiteBelow G.Adj y).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := A) (t := B) G.Adj
    _ = _ := by
      apply sum_congr rfl
      intro y _
      change (A.filter (fun x => G.Adj x y)).card = (A.filter (G.Adj y)).card
      exact congrArg Finset.card (filter_congr fun x _ => G.adj_comm x y)
  -- Crossing edges contribute twice, and the last sum counts internal B incidences.
  have hcount : 2 * G.edgeFinset.card =
      2 * (∑ x ∈ B, d A x) + ∑ x ∈ B, d B x := calc
    _ = ∑ x : V, G.degree x := hhandshake.symm
    _ = (∑ x ∈ A, G.degree x) + ∑ x ∈ B, G.degree x :=
      (sum_add_sum_compl A (fun x => G.degree x)).symm
    _ = _ := by
      simp only [← hsplit, sum_add_distrib, hzero A hA, zero_add, hswap, two_mul, add_assoc]
  have hB (x : V) (hx : x ∈ B) (y : V) (hy : y ∈ B) : ¬G.Adj x y := by
    intro hxy
    -- An internal edge uses both available vertices of B besides v.
    have hvx := hvNo hx
    have hvy := hvNo hy
    have hxv : x ≠ v := by
      rintro rfl
      exact hvy hxy
    have hyv : y ≠ v := by
      rintro rfl
      exact hvx hxy.symm
    have hvPair : v ∉ ({x, y} : Finset V) := by simp [hxv.symm, hyv.symm]
    have hthree : ({v, x, y} : Finset V).card = 3 := by
      rw [card_insert_of_notMem hvPair, card_pair hxy.ne]
    have hsubset : ({v, x, y} : Finset V) ⊆ B := by
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact hvB
      · exact hx
      · exact hy
    have hBthree : B = {v, x, y} :=
      (eq_of_subset_of_card_le hsubset (by omega)).symm
    have hBcard : B.card = 3 := by rw [hBthree, hthree]
    have hsum (f : V → ℕ) : (∑ z ∈ B, f z) = f v + (f x + f y) := by
      rw [hBthree, sum_insert hvPair, sum_pair hxy.ne]
    have hdisj : Disjoint (A.filter (G.Adj x)) (A.filter (G.Adj y)) := by
      refine disjoint_left.mpr ?_
      intro z hzX hzY
      exact htriangle x y z hxy (mem_filter.mp hzY).2 ((mem_filter.mp hzX).2).symm
    have hpair : d A x + d A y ≤ A.card := calc
      _ = (A.filter (G.Adj x) ∪ A.filter (G.Adj y)).card :=
        (card_union_of_disjoint hdisj).symm
      _ ≤ _ := card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
    have hcross : (∑ z ∈ B, d A z) ≤ (B.card - 1) * A.card := by
      rw [hsum (d A), hBcard]
      have hvcap := hcap A v
      change d A v + (d A x + d A y) ≤ 2 * A.card
      omega
    have hinternal : (∑ z ∈ B, d B z) = 2 := by
      have hxv' : ¬G.Adj x v := fun h => hvx h.symm
      have hyv' : ¬G.Adj y v := fun h => hvy h.symm
      rw [hsum (d B), hBthree]
      simp [d, filter_insert, filter_singleton, hvx, hvy, hxv', hyv', hxy, hxy.symm]
    have hAcard' : A.card = 4 := by omega
    rw [hBcard, hAcard'] at hcross
    omega
  rw [hzero B hB, add_zero] at hcount
  have hcross : (∑ x ∈ B, d A x) ≤ B.card * A.card := calc
    _ ≤ ∑ _x ∈ B, A.card := sum_le_sum fun x _ => hcap A x
    _ = _ := sum_const_nat (fun _ _ => rfl)
  have hprod : 11 ≤ B.card * A.card := by omega
  have hsizeA : A.card = 4 := by
    have hBpos := card_pos.mpr ⟨v, hvB⟩
    by_contra hne
    rcases (show B.card = 1 ∨ B.card = 2 by omega) with hb | hb
    · rw [hb, one_mul] at hprod
      omega
    · rw [hb] at hprod
      omega
  have hsizeB : B.card = 3 := by omega
  refine ⟨A, hsizeA, hsizeB, ⟨?_, ?_⟩⟩
  · exact disjoint_coe.mpr (show Disjoint A B from disjoint_compl_right)
  · intro x y hxy
    change (x ∈ A ∧ y ∈ B) ∨ (x ∈ B ∧ y ∈ A)
    by_cases hx : x ∈ A
    · exact Or.inl ⟨hx, mem_compl.mpr fun hy => hA x hx y hy hxy⟩
    · have hxb : x ∈ B := mem_compl.mpr hx
      by_cases hy : y ∈ A
      · exact Or.inr ⟨hxb, hy⟩
      · exact (hB x hxb y (mem_compl.mpr hy) hxy).elim

#print axioms seven_vertex_bipartition

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SevenVertexBipartite
