/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointSquareLeaf
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointSquareLeaf
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Maps]
   utility: none
   digest: Actual labels and high-edge incidence for paired squares with leaves. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointPentagonExclusion
import Mathlib.Combinatorics.SimpleGraph.Maps

/-! The square and leaf labels are transported from derived compressed graphs. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointSquareLeaf

open SimpleGraph GirthSliceCounting
open private SideHigh compressed compressed_degree from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression
open private SquareLeaf from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointSymmetric
open private side_high_neighbors_card high_neighbors_compressed_separated from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointTheta

attribute [local instance] Classical.propDecidable

private def sqEdges : List (Fin 5 × Fin 5) := [(0,1),(1,2),(2,3),(3,0),(0,4)]

private def sq : SimpleGraph (Fin 5) where
  Adj i j := (i,j) ∈ sqEdges ∨ (j,i) ∈ sqEdges
  symm := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩
  loopless := ⟨by intro i; fin_cases i <;> decide +kernel⟩

private instance : DecidableRel sq.Adj := fun i j =>
  inferInstanceAs (Decidable ((i,j) ∈ sqEdges ∨ (j,i) ∈ sqEdges))

private theorem square_leaf_iso {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} (hcard : Fintype.card V = 5) (hshape : SquareLeaf H) :
    Nonempty (sq ≃g H) := by
  obtain ⟨r, s, a, b, c, hnd, hr, hs, ha, hb, hc⟩ := hshape
  let v : Fin 5 → V := ![r, a, s, b, c]
  have hinj : Function.Injective v := by
    intro i j hij
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton,
      List.nodup_singleton, not_or] at hnd
    fin_cases i <;> fin_cases j <;> simp_all [v]
  have hsurj : Function.Surjective v := by
    have hu : Finset.univ.image v = (Finset.univ : Finset V) := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Finset.card_univ, hcard]
      rfl
    intro x
    have hx : x ∈ Finset.univ.image v := by rw [hu]; exact Finset.mem_univ _
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
    exact ⟨i, hi⟩
  refine ⟨{ toEquiv := Equiv.ofBijective v ⟨hinj, hsurj⟩, map_rel_iff' := ?_ }⟩
  intro i j
  change H.Adj (v i) (v j) ↔ sq.Adj i j
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton,
    List.nodup_singleton, not_or] at hnd
  fin_cases i <;> fin_cases j <;> dsimp [v] <;>
    rw [← SimpleGraph.mem_neighborFinset] <;>
    (first | rw [hr] | rw [hs] | rw [ha] | rw [hb] | rw [hc]) <;>
    simp_all [sq, sqEdges, ne_comm]

private theorem separated_square_pair (i j : Fin 5) (hne : i ≠ j)
    (hadj : ¬ sq.Adj i j) (hwedge : ∀ k, sq.Adj i k → sq.Adj j k → False) :
    ({i, j} : Finset (Fin 5)) = {2, 4} := by
  revert i j
  decide +kernel

private theorem square_cross_count
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (eL : sq ≃g compressed G L) (eR : sq ≃g compressed G R) (i : Fin 5) :
    (Finset.univ.filter (fun j : Fin 5 => G.Adj (eL i).val (eR j).val)).card + sq.degree i = 3 := by
  have hd := compressed_degree hpart hdeg hlow hg (eL i)
  rw [eL.degree_eq] at hd
  have hn := side_high_neighbors_card hpart (Finset.mem_filter.mp (eL i).property).1
  have hb : (Finset.univ.filter (fun j : Fin 5 => G.Adj (eL i).val (eR j).val)).card =
      (Finset.univ.filter (fun y : SideHigh G R => G.Adj (eL i).val y.val)).card := by
    apply Finset.card_bij (fun j _ => eR j)
    · intro j hj; simpa using (Finset.mem_filter.mp hj).2
    · intro i _ j _ he; exact eR.injective he
    · intro y hy
      exact ⟨eR.symm y, by simpa using (Finset.mem_filter.mp hy).2, by simp⟩
  rw [hb, hn]
  omega

private theorem square_leaf_high_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (eL : sq ≃g compressed G L) (eR : sq ≃g compressed G R) :
    (Finset.univ.filter (fun j : Fin 5 => G.Adj (eL 4).val (eR j).val)) = {2, 4} := by
  have hd := compressed_degree hpart hdeg hlow hg (eL 4)
  have hsq : (compressed G L).degree (eL 4) = 1 := by
    rw [eL.degree_eq]
    decide +kernel
  rw [hsq] at hd
  have hcard : (Finset.univ.filter (fun j : Fin 5 => G.Adj (eL 4).val (eR j).val)).card = 2 := by
    have hn := side_high_neighbors_card hpart (Finset.mem_filter.mp (eL 4).property).1
    have hb : (Finset.univ.filter (fun j : Fin 5 => G.Adj (eL 4).val (eR j).val)).card =
        (Finset.univ.filter (fun y : SideHigh G R => G.Adj (eL 4).val y.val)).card := by
      apply Finset.card_bij (fun j _ => eR j)
      · intro j hj; simpa using (Finset.mem_filter.mp hj).2
      · intro i _ j _ he; exact eR.injective he
      · intro y hy
        exact ⟨eR.symm y, by simpa using (Finset.mem_filter.mp hy).2, by simp⟩
    rw [hb, hn]
    omega
  obtain ⟨i, j, hij, hN⟩ := Finset.card_eq_two.mp hcard
  have hi : G.Adj (eL 4).val (eR i).val := by
    exact (Finset.mem_filter.mp (show i ∈ Finset.univ.filter
      (fun j : Fin 5 => G.Adj (eL 4).val (eR j).val) by rw [hN]; simp)).2
  have hj : G.Adj (eL 4).val (eR j).val := by
    exact (Finset.mem_filter.mp (show j ∈ Finset.univ.filter
      (fun j : Fin 5 => G.Adj (eL 4).val (eR j).val) by rw [hN]; simp)).2
  have hsep := high_neighbors_compressed_separated hpart hg
    (Finset.mem_filter.mp (eL 4).property).1 (Finset.mem_filter.mp (eL 4).property).2
    hi hj (eR.injective.ne hij)
  rw [hN]
  apply separated_square_pair i j hij
  · intro h; exact hsep.1 (eR.map_rel_iff.mpr h)
  · intro k hik hjk
    exact hsep.2 (eR k) (eR.map_rel_iff.mpr hik) (eR.map_rel_iff.mpr hjk)

private theorem square_forced_rows
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (eL : sq ≃g compressed G L) (eR : sq ≃g compressed G R) :
    (Finset.univ.filter (fun j : Fin 5 => G.Adj (eL 0).val (eR j).val)) = ∅ ∧
    (Finset.univ.filter (fun j : Fin 5 => G.Adj (eL 2).val (eR j).val)) = {4} ∧
    (Finset.univ.filter (fun j : Fin 5 => G.Adj (eL 4).val (eR j).val)) = {2, 4} := by
  have hN4 := square_leaf_high_neighbors hpart hdeg hlow hg eL eR
  have hN4' := square_leaf_high_neighbors hpart.symm hdeg hlow hg eR eL
  have h0 := square_cross_count hpart hdeg hlow hg eL eR 0
  have h2 := square_cross_count hpart hdeg hlow hg eL eR 2
  have hd0 : sq.degree 0 = 3 := by decide +kernel
  have hd2 : sq.degree 2 = 2 := by decide +kernel
  rw [hd0] at h0
  rw [hd2] at h2
  refine ⟨Finset.card_eq_zero.mp (by omega), ?_, hN4⟩
  have h24 : G.Adj (eL 2).val (eR 4).val := by
    have hm : (2 : Fin 5) ∈ Finset.univ.filter
        (fun j : Fin 5 => G.Adj (eR 4).val (eL j).val) := by rw [hN4']; decide +kernel
    exact (Finset.mem_filter.mp hm).2.symm
  apply (Finset.eq_of_subset_of_card_le ?_ (by simp only [Finset.card_singleton]; omega)).symm
  simp only [Finset.singleton_subset_iff, Finset.mem_filter, Finset.mem_univ, true_and]
  exact h24

private theorem square_cross_pairing
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (eL : sq ≃g compressed G L) (eR : sq ≃g compressed G R) :
    ((Finset.univ.filter (fun j : Fin 5 => G.Adj (eL 1).val (eR j).val)) = {1} ∧
      (Finset.univ.filter (fun j : Fin 5 => G.Adj (eL 3).val (eR j).val)) = {3}) ∨
    ((Finset.univ.filter (fun j : Fin 5 => G.Adj (eL 1).val (eR j).val)) = {3} ∧
      (Finset.univ.filter (fun j : Fin 5 => G.Adj (eL 3).val (eR j).val)) = {1}) := by
  have hcols := square_forced_rows hpart.symm hdeg hlow hg eR eL
  have hcount (i : Fin 5) (hi : i = 1 ∨ i = 3) :
      (Finset.univ.filter (fun j : Fin 5 => G.Adj (eL i).val (eR j).val)).card = 1 := by
    have hh := square_cross_count hpart hdeg hlow hg eL eR i
    have hd : sq.degree i = 2 := by rcases hi with rfl | rfl <;> decide +kernel
    rw [hd] at hh
    omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (hcount 1 (Or.inl rfl))
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp (hcount 3 (Or.inr rfl))
  have hxadj : G.Adj (eL 1).val (eR x).val := by
    exact (Finset.mem_filter.mp (show x ∈ Finset.univ.filter
      (fun j : Fin 5 => G.Adj (eL 1).val (eR j).val) by rw [hx]; simp)).2
  have hyadj : G.Adj (eL 3).val (eR y).val := by
    exact (Finset.mem_filter.mp (show y ∈ Finset.univ.filter
      (fun j : Fin 5 => G.Adj (eL 3).val (eR j).val) by rw [hy]; simp)).2
  have hallowed (i j : Fin 5) (hi : i = 1 ∨ i = 3)
      (hadj : G.Adj (eL i).val (eR j).val) : j = 1 ∨ j = 3 := by
    have hm : i ∈ Finset.univ.filter
        (fun k : Fin 5 => G.Adj (eR j).val (eL k).val) := by simpa using hadj.symm
    by_cases hj0 : j = 0
    · subst j; rw [hcols.1] at hm; simp at hm
    by_cases hj2 : j = 2
    · subst j; rw [hcols.2.1] at hm
      rcases hi with rfl | rfl <;> norm_num at hm
    by_cases hj4 : j = 4
    · subst j; rw [hcols.2.2] at hm
      rcases hi with rfl | rfl <;> norm_num at hm
    have hf : ∀ j : Fin 5, j ≠ 0 → j ≠ 2 → j ≠ 4 → j = 1 ∨ j = 3 := by decide +kernel
    exact hf j hj0 hj2 hj4
  have hx13 := hallowed 1 x (Or.inl rfl) hxadj
  have hy13 := hallowed 3 y (Or.inr rfl) hyadj
  have hxy : x ≠ y := by
    intro he
    have hh := square_cross_count hpart.symm hdeg hlow hg eR eL x
    have hd : sq.degree x = 2 := by rcases hx13 with rfl | rfl <;> decide +kernel
    rw [hd] at hh
    have hsub : ({1, 3} : Finset (Fin 5)) ⊆ Finset.univ.filter
        (fun k : Fin 5 => G.Adj (eR x).val (eL k).val) := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hxadj.symm, by rw [he]; exact hyadj.symm⟩
    have hc := Finset.card_le_card hsub
    norm_num at hc
    omega
  rcases hx13 with rfl | rfl <;> rcases hy13 with rfl | rfl
  · exact (hxy rfl).elim
  · exact Or.inl ⟨hx, hy⟩
  · exact Or.inr ⟨hx, hy⟩
  · exact (hxy rfl).elim

private def sqSwap : sq ≃g sq where
  toEquiv := Equiv.swap 1 3
  map_rel_iff' := by
    intro i j
    change sq.Adj ((Equiv.swap 1 3) i) ((Equiv.swap 1 3) j) ↔ sq.Adj i j
    revert i j
    decide +kernel

private def crossNbr : Fin 5 → Finset (Fin 5) := ![∅, {1}, {4}, {3}, {2, 4}]

private theorem paired_square_labels
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hLcard : (degreeThree G L).card = 5) (hRcard : (degreeThree G R).card = 5)
    (hL : SquareLeaf (compressed G L)) (hR : SquareLeaf (compressed G R)) :
    ∃ eL : sq ≃g compressed G L, ∃ eR : sq ≃g compressed G R,
      ∀ i j, G.Adj (eL i).val (eR j).val ↔ j ∈ crossNbr i := by
  obtain ⟨eL⟩ := square_leaf_iso (by simpa only [SideHigh, Fintype.card_coe] using hLcard) hL
  obtain ⟨eR⟩ := square_leaf_iso (by simpa only [SideHigh, Fintype.card_coe] using hRcard) hR
  obtain ⟨h0, h2, h4⟩ := square_forced_rows hpart hdeg hlow hg eL eR
  have hpairs := square_cross_pairing hpart hdeg hlow hg eL eR
  rcases hpairs with ⟨h1, h3⟩ | ⟨h1, h3⟩
  · refine ⟨eL, eR, ?_⟩
    have htable (i : Fin 5) :
        Finset.univ.filter (fun j : Fin 5 => G.Adj (eL i).val (eR j).val) = crossNbr i := by
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact h4
    intro i j
    rw [← htable i]
    simp
  · refine ⟨eL, sqSwap.trans eR, ?_⟩
    intro i j
    change G.Adj (eL i).val (eR (sqSwap j)).val ↔ j ∈ crossNbr i
    have hm : G.Adj (eL i).val (eR (sqSwap j)).val ↔
        sqSwap j ∈ Finset.univ.filter (fun k : Fin 5 => G.Adj (eL i).val (eR k).val) := by simp
    let swapNbr : Fin 5 → Finset (Fin 5) := ![∅, {3}, {4}, {1}, {2, 4}]
    have htable (i : Fin 5) :
        Finset.univ.filter (fun j : Fin 5 => G.Adj (eL i).val (eR j).val) = swapNbr i := by
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact h4
    rw [hm, htable i]
    change sqSwap j ∈ (![∅, {3}, {4}, {1}, {2, 4}] : Fin 5 → Finset (Fin 5)) i ↔ j ∈ crossNbr i
    fin_cases i <;> fin_cases j <;> decide +kernel

#print axioms paired_square_labels

end D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointSquareLeaf
