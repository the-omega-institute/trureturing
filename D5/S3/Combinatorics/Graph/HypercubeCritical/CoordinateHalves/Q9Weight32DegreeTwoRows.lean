/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9Weight32DegreeTwoRows
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9Weight32DegreeTwoRows
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9SparseSyndromeObstruction]
   utility: none
   digest: A weight-thirty-two cube support with row degrees zero, two or four has at least eighteen degree-two rows. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9SparseSyndromeObstruction
import Mathlib.Data.Finset.Powerset

/-! A local count on cube layers forces at least eighteen degree-two rows. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves
namespace Q9Weight32DegreeTwoRows

open Finset
open scoped BigOperators
open EightCubeBits (Vertex Word shell_card shell shell_symm toggle distance parity relabel)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.EightCubeBits (relabel_center relabel_shell toggle_parity)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9SparseSyndromeObstruction (weightLayer mem_weightLayer level_counts common_lower_row_of_two sum_shell_inter_comm)

def rowDegree (T : Word) (x : Vertex) : ℕ := (shell x ∩ T).card

def degreeTwoRows (T : Word) : Word :=
  univ.filter fun x => rowDegree T x = 2

@[simp] theorem mem_degreeTwoRows {T : Word} {x : Vertex} :
    x ∈ degreeTwoRows T ↔ rowDegree T x = 2 := by
  simp [degreeTwoRows]

private theorem sum_indicator (S : Word) (p : Vertex → Prop) [DecidablePred p] :
    (∑ x ∈ S, if p x then (1 : ℕ) else 0) = (S.filter p).card := by
  rw [← sum_filter]
  simp

private theorem weightLayer_disjoint {i j : ℕ} (h : i ≠ j) :
    Disjoint (weightLayer i) (weightLayer j) := by
  refine disjoint_left.mpr ?_
  intro x hx hy
  exact h ((mem_weightLayer.mp hx).symm.trans (mem_weightLayer.mp hy))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem three_lower_neighbors :
    ∀ x : Vertex, x ∈ weightLayer 3 → (shell x ∩ weightLayer 2).card = 3 := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
-- Two distinct weight-two neighbors of a weight-one row meet in one row in each layer.
private theorem lower_pair_common_cards :
    ∀ u : Vertex, u ∈ weightLayer 1 → ∀ i j : Fin 8, i ≠ j →
      toggle u i ∈ weightLayer 2 → toggle u j ∈ weightLayer 2 →
      (shell (toggle u i) ∩ shell (toggle u j) ∩ weightLayer 1).card =
        (shell (toggle u i) ∩ shell (toggle u j) ∩ weightLayer 3).card := by
  decide +kernel

private theorem pair_common_cards {x y : Vertex} (hx : x ∈ weightLayer 2)
    (hy : y ∈ weightLayer 2) (hxy : x ≠ y) :
    (shell x ∩ shell y ∩ weightLayer 1).card =
      (shell x ∩ shell y ∩ weightLayer 3).card := by
  by_cases h : (shell x ∩ shell y ∩ weightLayer 1).Nonempty
  · obtain ⟨u, hu⟩ := h
    obtain ⟨huShell, hu₁⟩ := mem_inter.mp hu
    have hux : x ∈ shell u := shell_symm.mp (mem_inter.mp huShell).1
    have huy : y ∈ shell u := shell_symm.mp (mem_inter.mp huShell).2
    obtain ⟨i, _, rfl⟩ := mem_image.mp hux
    obtain ⟨j, _, rfl⟩ := mem_image.mp huy
    exact lower_pair_common_cards u hu₁ i j (fun h => hxy (congrArg (toggle u) h)) hx hy
  · have htEmpty : ¬ (shell x ∩ shell y ∩ weightLayer 3).Nonempty := by
      rintro ⟨t, ht⟩
      obtain ⟨htShell, ht₃⟩ := mem_inter.mp ht
      have hxt : x ∈ shell t ∩ weightLayer 2 :=
        mem_inter.mpr ⟨shell_symm.mp (mem_inter.mp htShell).1, hx⟩
      have hyt : y ∈ shell t ∩ weightLayer 2 :=
        mem_inter.mpr ⟨shell_symm.mp (mem_inter.mp htShell).2, hy⟩
      exact h (common_lower_row_of_two (Or.inl rfl) t x y ht₃ hxt hyt hxy).1
    rw [not_nonempty_iff_eq_empty.mp h, not_nonempty_iff_eq_empty.mp htEmpty]

private theorem sum_choose_rowDegree (k : ℕ) (L : Word) :
    (∑ x ∈ weightLayer k, (rowDegree L x).choose 2) =
      ∑ P ∈ powersetCard 2 L, ((weightLayer k).filter fun x => P ⊆ shell x).card := by
  have habove (x : Vertex) :
      (powersetCard 2 L).bipartiteAbove (fun x P => P ⊆ shell x) x =
        powersetCard 2 (shell x ∩ L) := by
    ext P
    simp only [Finset.bipartiteAbove, mem_filter, mem_powersetCard, subset_inter_iff]
    exact ⟨fun h => ⟨⟨h.2, h.1.1⟩, h.1.2⟩, fun h => ⟨⟨h.1.2, h.2⟩, h.1.1⟩⟩
  simpa only [habove, Finset.bipartiteBelow, card_powersetCard, rowDegree] using
    sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := weightLayer k) (t := powersetCard 2 L) (fun x P => P ⊆ shell x)

-- Count each unordered pair of lower neighbors by its common row in each layer.
private theorem sum_choose_weight_three_eq_one {L : Word} (hL : L ⊆ weightLayer 2) :
    (∑ x ∈ weightLayer 3, (rowDegree L x).choose 2) =
      ∑ x ∈ weightLayer 1, (rowDegree L x).choose 2 := by
  rw [sum_choose_rowDegree 3 L, sum_choose_rowDegree 1 L]
  apply sum_congr rfl
  intro P hP
  obtain ⟨hPL, hPcard⟩ := mem_powersetCard.mp hP
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hPcard
  have hfilter (k : ℕ) :
      ((weightLayer k).filter fun u => ({x, y} : Word) ⊆ shell u) =
        shell x ∩ shell y ∩ weightLayer k := by
    ext u
    simp only [mem_filter, mem_inter, insert_subset_iff, singleton_subset_iff]
    simp only [shell_symm (x := x) (y := u), shell_symm (x := y) (y := u), and_comm]
  rw [hfilter 3, hfilter 1]
  have hx : x ∈ L := hPL (by simp)
  have hy : y ∈ L := hPL (by simp)
  exact (pair_common_cards (hL hx) (hL hy) hxy).symm

private theorem sum_rowDegree_of_layer (k m : ℕ) (S : Word)
    (h : ∀ x ∈ S, (shell x ∩ weightLayer k).card = m) :
    (∑ x ∈ weightLayer k, rowDegree S x) = S.card * m := by
  unfold rowDegree
  rw [sum_shell_inter_comm (weightLayer k) S]
  calc
    _ = ∑ _x ∈ S, m := sum_congr rfl h
    _ = _ := by simp [Nat.nsmul_eq_mul]

/-- For a support containing the origin, §4.1 gives the local inequality
    `22 ≤ n₂ + 4a₀` from the incidences in the first four layers. -/
theorem degreeTwoRows_add_four_origin {T : Word} (hsize : T.card = 32) (h0 : 0 ∈ T)
    (hdegree : ∀ x, rowDegree T x = 0 ∨ rowDegree T x = 2 ∨ rowDegree T x = 4) :
    22 ≤ (degreeTwoRows T).card + 4 * (shell 0 ∩ degreeTwoRows T).card := by
  let L := T ∩ weightLayer 2
  let P := T ∩ weightLayer 4
  let A := (weightLayer 1).filter fun x => rowDegree T x = 2
  let U := (weightLayer 3).filter fun x => 0 < rowDegree L x
  let B := (weightLayer 3).filter fun x => 0 < rowDegree L x ∧ rowDegree T x = 2
  let Tri := (weightLayer 3).filter fun x => rowDegree L x = 3
  have hLlevel : L ⊆ weightLayer 2 := inter_subset_right
  have hPlevel : P ⊆ weightLayer 4 := inter_subset_right
  have h1card : (weightLayer 1).card = 8 := by rw [level_counts.1, shell_card]
  have h0dist : distance 0 0 = 0 := by simp [distance]
  have h0not2 : (0 : Vertex) ∉ weightLayer 2 := by simp [mem_weightLayer, h0dist]
  have h0not4 : (0 : Vertex) ∉ weightLayer 4 := by simp [mem_weightLayer, h0dist]
  have hsplit1 (x : Vertex) (hx : x ∈ weightLayer 1) :
      rowDegree T x = rowDegree L x + 1 := by
    have hx0 : (0 : Vertex) ∈ shell x := shell_symm.mp (level_counts.1 ▸ hx)
    have heq : shell x ∩ T = insert 0 (shell x ∩ L) := by
      ext y
      constructor
      · intro hy
        obtain ⟨hyx, hyT⟩ := mem_inter.mp hy
        apply mem_insert.mpr
        rcases mem_insert.mp ((level_counts.2 x).1 hx hyx) with rfl | hy₂
        · exact Or.inl rfl
        · exact Or.inr (mem_inter.mpr ⟨hyx, mem_inter.mpr ⟨hyT, hy₂⟩⟩)
      · intro hy
        rcases mem_insert.mp hy with rfl | hy
        · exact mem_inter.mpr ⟨hx0, h0⟩
        · obtain ⟨hyx, hyL⟩ := mem_inter.mp hy
          exact mem_inter.mpr ⟨hyx, (mem_inter.mp hyL).1⟩
    have hnot : (0 : Vertex) ∉ shell x ∩ L :=
      fun h => h0not2 (hLlevel (mem_inter.mp h).2)
    unfold rowDegree
    rw [heq, card_insert_of_notMem hnot]
  have hfirst (x : Vertex) (hx : x ∈ weightLayer 1) :
      rowDegree L x + 2 * (if rowDegree T x = 2 then 1 else 0) = 3 ∧
      (rowDegree L x).choose 2 + 3 * (if rowDegree T x = 2 then 1 else 0) = 3 := by
    have h := hsplit1 x hx
    rcases hdegree x with h₀ | h₂ | h₄
    · omega
    · have hL : rowDegree L x = 1 := by omega
      rw [h₂, hL] <;> decide
    · have hL : rowDegree L x = 3 := by omega
      rw [h₄, hL] <;> decide
  -- Equations (4.1) through (4.3).
  have hsum1 := sum_rowDegree_of_layer 1 2 L
    (fun x hx => ((level_counts.2 x).2.1 (hLlevel hx)).1)
  have hsum3 := sum_rowDegree_of_layer 3 6 L
    (fun x hx => ((level_counts.2 x).2.1 (hLlevel hx)).2)
  have hsum4 := sum_rowDegree_of_layer 3 4 P
    (fun x hx => ((level_counts.2 x).2.2.2.1 (hPlevel hx)).1)
  have hedges : L.card * 2 + 2 * A.card = 24 := by
    have h := sum_congr (rfl : weightLayer 1 = weightLayer 1)
      (fun x hx => (hfirst x hx).1)
    simpa only [sum_add_distrib, ← mul_sum, sum_indicator, hsum1,
      sum_const, Nat.nsmul_eq_mul, h1card] using h
  have hwedges :
      (∑ x ∈ weightLayer 3, (rowDegree L x).choose 2) + 3 * A.card = 24 := by
    have h := sum_congr (rfl : weightLayer 1 = weightLayer 1)
      (fun x hx => (hfirst x hx).2)
    rw [sum_choose_weight_three_eq_one hLlevel]
    simpa only [sum_add_distrib, ← mul_sum, sum_indicator,
      sum_const, Nat.nsmul_eq_mul, h1card] using h
  -- Equation (4.4), with the triangle term retained on the right.
  have hIE (x : Vertex) (hx : x ∈ weightLayer 3) :
      (if 0 < rowDegree L x then 1 else 0) + (rowDegree L x).choose 2 =
        rowDegree L x + (if rowDegree L x = 3 then 1 else 0) := by
    have hle := card_le_card (inter_subset_inter_left (s := shell x) hLlevel)
    rw [three_lower_neighbors x hx] at hle
    change rowDegree L x ≤ 3 at hle
    have h : rowDegree L x = 0 ∨ rowDegree L x = 1 ∨
        rowDegree L x = 2 ∨ rowDegree L x = 3 := by omega
    rcases h with h | h | h | h <;> rw [h] <;> decide
  have hocc :
      U.card + (∑ x ∈ weightLayer 3, (rowDegree L x).choose 2) =
        L.card * 6 + Tri.card := by
    simpa only [sum_add_distrib, sum_indicator, hsum3] using
      sum_congr (rfl : weightLayer 3 = weightLayer 3) hIE
  have hLP : Disjoint L P :=
    (weightLayer_disjoint (by decide : (2 : ℕ) ≠ 4)).mono hLlevel hPlevel
  have hsplit3 (x : Vertex) (hx : x ∈ weightLayer 3) :
      rowDegree T x = rowDegree L x + rowDegree P x := by
    have heq : shell x ∩ T = (shell x ∩ L) ∪ (shell x ∩ P) := by
      ext y
      constructor
      · intro hy
        obtain ⟨hyx, hyT⟩ := mem_inter.mp hy
        apply mem_union.mpr
        rcases mem_union.mp ((level_counts.2 x).2.2.1 hx hyx) with hy₂ | hy₄
        · exact Or.inl (mem_inter.mpr ⟨hyx, mem_inter.mpr ⟨hyT, hy₂⟩⟩)
        · exact Or.inr (mem_inter.mpr ⟨hyx, mem_inter.mpr ⟨hyT, hy₄⟩⟩)
      · intro hy
        rcases mem_union.mp hy with hy | hy
        · obtain ⟨hyx, hyL⟩ := mem_inter.mp hy
          exact mem_inter.mpr ⟨hyx, (mem_inter.mp hyL).1⟩
        · obtain ⟨hyx, hyP⟩ := mem_inter.mp hy
          exact mem_inter.mpr ⟨hyx, (mem_inter.mp hyP).1⟩
    have hdisj := hLP.mono (inter_subset_right : shell x ∩ L ⊆ L)
      (inter_subset_right : shell x ∩ P ⊆ P)
    unfold rowDegree
    rw [heq, card_union_of_disjoint hdisj]
  -- Equation (4.5), allowing nonnegative contributions from rows outside U.
  have hupper (x : Vertex) (hx : x ∈ weightLayer 3) :
      4 * (if 0 < rowDegree L x then 1 else 0) ≤
        rowDegree L x + rowDegree P x +
          2 * (if 0 < rowDegree L x ∧ rowDegree T x = 2 then 1 else 0) := by
    by_cases hpos : 0 < rowDegree L x
    · have hs := hsplit3 x hx
      rcases hdegree x with h₀ | h₂ | h₄
      · omega
      · simp [hpos, h₂] <;> omega
      · have hne : rowDegree T x ≠ 2 := by omega
        simp [hpos, hne] <;> omega
    · simp [hpos]
  have hcapacity3 : 4 * U.card ≤ L.card * 6 + P.card * 4 + 2 * B.card := by
    have h := sum_le_sum (s := weightLayer 3) (fun x hx => hupper x hx)
    simpa only [sum_add_distrib, ← mul_sum, sum_indicator, hsum3, hsum4] using h
  -- Equations (4.6) and (4.7).
  have hcap : L.card + P.card + 1 ≤ 32 := by
    have hzero : (0 : Vertex) ∉ L ∪ P := by
      intro h
      rcases mem_union.mp h with h | h
      · exact h0not2 (hLlevel h)
      · exact h0not4 (hPlevel h)
    have hsub : insert 0 (L ∪ P) ⊆ T := by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact h0
      · rcases mem_union.mp hx with hx | hx
        · exact (mem_inter.mp hx).1
        · exact (mem_inter.mp hx).1
    have h := card_le_card hsub
    rwa [card_insert_of_notMem hzero, card_union_of_disjoint hLP, hsize] at h
  have hb : 22 + 2 * Tri.card ≤ B.card + 5 * A.card := by omega
  have hrows : A.card + B.card ≤ (degreeTwoRows T).card := by
    have hAB : Disjoint A B := (weightLayer_disjoint (by decide : (1 : ℕ) ≠ 3)).mono
      (filter_subset _ _) (filter_subset _ _)
    have hsub : A ∪ B ⊆ degreeTwoRows T := by
      intro x hx
      apply mem_degreeTwoRows.mpr
      rcases mem_union.mp hx with hx | hx
      · exact (mem_filter.mp hx).2
      · exact (mem_filter.mp hx).2.2
    have h := card_le_card hsub
    rwa [card_union_of_disjoint hAB] at h
  have hA : A = shell 0 ∩ degreeTwoRows T := by
    ext x
    simp [A, level_counts.1]
  rw [← hA]
  omega

/-- Transport the local bound to any site of the support by cube translation. -/
theorem degreeTwoRows_add_four_at_site {T : Word} (hsize : T.card = 32)
    (hdegree : ∀ x, rowDegree T x = 0 ∨ rowDegree T x = 2 ∨ rowDegree T x = 4)
    (t : Vertex) (ht : t ∈ T) :
    22 ≤ (degreeTwoRows T).card + 4 * (shell t ∩ degreeTwoRows T).card := by
  let σ := Equiv.refl (Fin 8)
  let e := relabel σ t
  have he : e t = 0 := relabel_center σ t
  have hshell (x : Vertex) : (shell x).map e.toEmbedding = shell (e x) :=
    relabel_shell σ t x
  have hrow (x : Vertex) :
      rowDegree (T.map e.toEmbedding) (e x) = rowDegree T x := by
    unfold rowDegree
    rw [← hshell, ← map_inter, card_map]
  have hrows :
      degreeTwoRows (T.map e.toEmbedding) = (degreeTwoRows T).map e.toEmbedding := by
    ext x
    obtain ⟨y, rfl⟩ := e.surjective x
    simp only [mem_map_equiv, Equiv.symm_apply_apply, mem_degreeTwoRows, hrow]
  have h0 : (0 : Vertex) ∈ T.map e.toEmbedding := by
    rw [← he, mem_map_equiv, Equiv.symm_apply_apply]
    exact ht
  have hdegree' (x : Vertex) :
      rowDegree (T.map e.toEmbedding) x = 0 ∨ rowDegree (T.map e.toEmbedding) x = 2 ∨
        rowDegree (T.map e.toEmbedding) x = 4 := by
    obtain ⟨y, rfl⟩ := e.surjective x
    simpa only [hrow] using hdegree y
  have h := degreeTwoRows_add_four_origin (T := T.map e.toEmbedding)
    (by rwa [card_map]) h0 hdegree'
  rw [hrows, card_map, ← he, ← hshell, ← map_inter, card_map] at h
  exact h

/-- A 32-site support of the eight-cube with degrees in `{0, 2, 4}`
    has at least 18 rows of degree two. -/
theorem eighteen_le_degreeTwoRows {T : Word} (hsize : T.card = 32)
    (hdegree : ∀ x, rowDegree T x = 0 ∨ rowDegree T x = 2 ∨ rowDegree T x = 4) :
    18 ≤ (degreeTwoRows T).card := by
  have hinc :
      (∑ t ∈ T, (shell t ∩ degreeTwoRows T).card) = (degreeTwoRows T).card * 2 := by
    rw [sum_shell_inter_comm]
    calc
      _ = ∑ _x ∈ degreeTwoRows T, (2 : ℕ) :=
        sum_congr rfl (fun _ hx => mem_degreeTwoRows.mp hx)
      _ = _ := by simp [Nat.nsmul_eq_mul]
  have h := sum_le_sum (s := T) (fun t ht => degreeTwoRows_add_four_at_site hsize hdegree t ht)
  simp only [sum_add_distrib, ← mul_sum, sum_const, Nat.nsmul_eq_mul, hsize, hinc] at h
  omega

/-- For a monochromatic support, the degree hypothesis is needed only on the
    opposite parity class. -/
theorem eighteen_le_degreeTwoRows_of_monochromatic {T : Word} {p : ZMod 2}
    (hsize : T.card = 32) (hcolor : ∀ t ∈ T, parity t = p)
    (hdegree : ∀ x, parity x ≠ p →
      rowDegree T x = 0 ∨ rowDegree T x = 2 ∨ rowDegree T x = 4) :
    18 ≤ (degreeTwoRows T).card := by
  apply eighteen_le_degreeTwoRows hsize
  intro x
  by_cases hx : parity x = p
  · left
    unfold rowDegree
    apply card_eq_zero.mpr
    ext t
    simp only [mem_inter, notMem_empty, iff_false]
    rintro ⟨htx, htT⟩
    obtain ⟨i, _, rfl⟩ := mem_image.mp htx
    have h := hcolor _ htT
    rw [toggle_parity, hx] at h
    have hzero : (1 : ZMod 2) = 0 :=
      add_right_cancel (show (1 : ZMod 2) + p = 0 + p by simpa only [zero_add] using h)
    exact one_ne_zero hzero
  · exact hdegree x hx

end Q9Weight32DegreeTwoRows
end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves
