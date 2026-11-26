/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SixtySixPointSupport/WeightLayerParity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SixtySixPointSupport/WeightLayerParity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Parity of consecutive Boolean weight layers forces an even total coordinate deficit. -/

import Mathlib.Algebra.BigOperators.Ring.Nat
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary

/-! Exterior Huang cancellation imposes parity constraints on Boolean weight layers. -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q IsBalanced flip)
attribute [local instance] Classical.propDecidable

open D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
  (directions regular_directions exterior_even)

namespace D5.S3.Combinatorics.Graph.HypercubeCritical

private def trueDirections (x : Q 9) : Finset (Fin 9) :=
  univ.filter fun j => x j = true

/-- The number of true coordinates of a Boolean cube vertex. -/
def booleanWeight (x : Q 9) : ℕ := (trueDirections x).card

private lemma weight_flip (x : Q 9) (i : Fin 9) :
    booleanWeight (flip x i) = if x i = true then booleanWeight x - 1 else booleanWeight x + 1 := by
  have hmem (v : Q 9) (j : Fin 9) : j ∈ trueDirections v ↔ v j = true := by
    simp [trueDirections]
  have hflip (j : Fin 9) (hj : j ≠ i) : flip x i j = x j :=
    Function.update_of_ne hj _ _
  by_cases h : x i = true
  · have he : trueDirections (flip x i) = (trueDirections x).erase i := by
      ext j
      by_cases hj : j = i
      · subst j
        simp [trueDirections, h]
      · simp [mem_erase, hmem, hflip j hj, hj]
    rw [ite_eq_left h, booleanWeight, he, card_erase_of_mem (by simp [trueDirections, h])]
    rfl
  · have hf : x i = false := Bool.eq_false_of_not_eq_true h
    have he : trueDirections (flip x i) = insert i (trueDirections x) := by
      ext j
      by_cases hj : j = i
      · subst j
        simp [trueDirections, hf]
      · simp [mem_insert, hmem, hflip j hj, hj]
    rw [ite_eq_right h, booleanWeight, he, card_insert_of_notMem (by simp [trueDirections, hf])]
    rfl

private lemma weight_layer_directions (x : Q 9) (k : ℕ) :
    (univ.filter fun i => booleanWeight (flip x i) = k + 1).card =
      (if booleanWeight x = k then 9 - k else 0) +
        (if booleanWeight x = k + 2 then k + 2 else 0) := by
  by_cases hlo : booleanWeight x = k
  · have hne : k - 1 ≠ k + 1 := by omega
    have he : (univ.filter fun i => booleanWeight (flip x i) = k + 1) =
        univ \ trueDirections x := by
      ext i
      cases hi : x i <;> simp [weight_flip, hi, hlo, hne, trueDirections]
    rw [he, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
    change 9 - booleanWeight x = _
    simp [hlo]
  by_cases hhi : booleanWeight x = k + 2
  · have he : (univ.filter fun i => booleanWeight (flip x i) = k + 1) = trueDirections x := by
      ext i
      cases hi : x i <;> simp [weight_flip, hi, hhi, trueDirections]
    rw [he]
    change booleanWeight x = _
    simp [hhi]
  have he : (univ.filter fun i => booleanWeight (flip x i) = k + 1) = ∅ := by
    apply filter_eq_empty_iff.mpr
    intro i _
    rw [weight_flip]
    split <;> omega
  simp [he, hlo, hhi]

/-- Huang cancellation pairs every even Boolean weight layer with its successor
modulo two. The degree toward the odd layer is odd on the lower layer and even
on the upper layer. -/
theorem balanced_cube_even_adjacent_layers {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set _)).IsRegularOfDegree 3) (hb : IsBalanced C)
    (k : ℕ) (hk : Even k) (hkmax : k ≤ 8) :
    Even (C.filter (fun x => booleanWeight x = k ∨ booleanWeight x = k + 1)).card := by
  let T : Finset (Q 9) := univ.filter fun x => booleanWeight x = k + 1
  have hodd (x : Q 9) : Odd (directions C x).card ↔ x ∈ C := by
    by_cases hx : x ∈ C
    · simp [hx, regular_directions C hr hx, Nat.odd_iff]
    · have he := exterior_even C hr hb x hx
      simp [hx, ← Nat.not_even_iff_odd, he]
  have hpar : Even (∑ x ∈ T, (directions C x).card) ↔
      Even (C.filter fun x => booleanWeight x = k + 1).card := by
    rw [even_sum_iff_even_card_odd]
    simp_rw [hodd]
    have he : T.filter (· ∈ C) = C.filter (fun x => booleanWeight x = k + 1) := by
      ext x
      simp [T, and_comm]
    rw [he]
  have hsum : (∑ x ∈ T, (directions C x).card) =
      (9 - k) * (C.filter fun x => booleanWeight x = k).card +
        (k + 2) * (C.filter fun x => booleanWeight x = k + 2).card := by
    calc
      _ = ∑ i : Fin 9, ∑ x : Q 9, if booleanWeight x = k + 1 ∧ flip x i ∈ C then 1 else 0 := by
        simp only [directions, card_filter]
        rw [sum_comm]
        apply sum_congr rfl
        intro i _
        simp only [T, sum_filter]
        apply sum_congr rfl
        intro x _
        split <;> simp_all
      _ = ∑ i : Fin 9, ∑ x : Q 9, if x ∈ C ∧ booleanWeight (flip x i) = k + 1 then 1 else 0 := by
        apply sum_congr rfl
        intro i _
        let e : Q 9 ≃ Q 9 :=
          ⟨(flip · i), (flip · i), (fun x => BalancedCriticalSpectrum.flip_flip x i),
            (fun x => BalancedCriticalSpectrum.flip_flip x i)⟩
        conv_lhs => rw [← e.sum_comp]
        simp [e, and_comm]
      _ = ∑ x ∈ C, (univ.filter fun i => booleanWeight (flip x i) = k + 1).card := by
        simp only [card_filter]
        rw [sum_comm]
        have hfilter : (univ.filter fun x : Q 9 => x ∈ C) = C := by
          ext x
          simp
        conv_rhs => rw [← hfilter, sum_filter]
        apply sum_congr rfl
        intro x _
        by_cases hx : x ∈ C <;> simp [hx]
      _ = _ := by
        simp_rw [fun x => weight_layer_directions x k]
        rw [sum_add_distrib, ← sum_filter, ← sum_filter, sum_const, sum_const]
        simp [Nat.mul_comm]
  rw [hsum, Nat.even_iff, Nat.even_iff] at hpar
  rw [filter_or, card_union_of_disjoint]
  · rw [Nat.even_iff]
    have hlo : (9 - k) % 2 = 1 := by
      have h := Nat.even_iff.mp hk
      omega
    have hhi : (k + 2) % 2 = 0 := by
      have h := Nat.even_iff.mp hk
      omega
    rw [Nat.add_mod, Nat.mul_mod (9 - k), Nat.mul_mod (k + 2), hlo, hhi] at hpar
    simp only [one_mul, zero_mul, Nat.mod_mod] at hpar
    omega
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    have h2 := (mem_filter.mp hx).2
    have h3 := (mem_filter.mp hy).2
    omega

private lemma weight_parity_ne_of_adj {x y : Q 9} (hxy : (hypercube 9).Adj x y) :
    booleanWeight x % 2 ≠ booleanWeight y % 2 := by
  change (univ.filter fun i => x i ≠ y i).card = 1 at hxy
  obtain ⟨i, hi⟩ := card_eq_one.mp hxy
  have he : flip x i = y := by
    ext j
    have hd : x j ≠ y j ↔ j = i := by
      have hj := congrArg (fun s : Finset (Fin 9) => j ∈ s) hi
      simpa using hj
    by_cases hji : j = i
    · subst j
      have hj := hd.mpr rfl
      cases hx : x i <;> cases hy : y i <;>
        simp_all [BalancedCriticalSpectrum.flip_apply_same]
    · have hj : x j = y j := Classical.not_not.mp (fun h => hji (hd.mp h))
      exact (Function.update_of_ne hji _ _).trans hj
  rw [← he, weight_flip]
  split
  · rename_i hx
    have hpositive : 0 < booleanWeight x :=
      card_pos.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hx⟩⟩
    omega
  · omega

private lemma cubic_odd_weight_half_card {C : Finset (Q 9)} (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) :
    (C.filter (fun x => booleanWeight x % 2 = 1)).card = 33 := by
  let V := (C : Set (Q 9))
  let E : Finset V := univ.filter (fun x => booleanWeight x.val % 2 = 0)
  let O : Finset V := univ.filter (fun x => booleanWeight x.val % 2 = 1)
  have hdis : Disjoint E O := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have h0 := (mem_filter.mp hx).2
    have h1 := (mem_filter.mp hy).2
    omega
  have hparts : ((hypercube 9).induce V).IsBipartiteWith (E : Set V) (O : Set V) := by
    constructor
    · exact Finset.disjoint_coe.mpr hdis
    · intro x y hxy
      have hne : booleanWeight x.val % 2 ≠ booleanWeight y.val % 2 :=
        weight_parity_ne_of_adj hxy
      change (x ∈ E ∧ y ∈ O) ∨ (x ∈ O ∧ y ∈ E)
      simp only [E, O, mem_filter, mem_univ, true_and]
      omega
  have hsum := SimpleGraph.isBipartiteWith_sum_degrees_eq hparts
  have hdegree (v : V) : ((hypercube 9).induce V).degree v = 3 := hreg.degree_eq v
  simp only [hdegree, sum_const, smul_eq_mul] at hsum
  have hu : E ∪ O = univ := by
    ext x
    simp only [E, O, mem_union, mem_filter, mem_univ, true_and, iff_true]
    omega
  have hsize := congrArg Finset.card hu
  rw [card_union_of_disjoint hdis, card_univ, show Fintype.card V = 66 by simpa [V] using hC] at hsize
  have himage : O.image Subtype.val = C.filter (fun x => booleanWeight x % 2 = 1) := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      exact mem_filter.mpr ⟨y.property, (mem_filter.mp hy).2⟩
    · intro hx
      obtain ⟨hxC, hxodd⟩ := mem_filter.mp hx
      exact mem_image.mpr ⟨⟨x, hxC⟩, mem_filter.mpr ⟨mem_univ _, hxodd⟩, rfl⟩
  rw [← himage, card_image_of_injective _ Subtype.val_injective]
  omega

/-- A 66-vertex Huang-balanced cubic support has total Boolean weight
congruent to one modulo four. -/
theorem balanced_sixty_six_weight_mod_four {C : Finset (Q 9)} (hc : C.card = 66)
    (hr : ((hypercube 9).induce (C : Set _)).IsRegularOfDegree 3) (hb : IsBalanced C) :
    (∑ x ∈ C, booleanWeight x) % 4 = 1 := by
  have he : Even (∑ x ∈ C, booleanWeight x / 2) := by
    rw [even_sum_iff_even_card_odd]
    have hfilter : (C.filter fun x => Odd (booleanWeight x / 2)) =
        C.filter (fun x => (booleanWeight x = 2 ∨ booleanWeight x = 3) ∨
          (booleanWeight x = 6 ∨ booleanWeight x = 7)) := by
      ext x
      simp only [mem_filter]
      refine and_congr_right fun hx => ?_
      have h : booleanWeight x ≤ 9 := by
        simpa [booleanWeight] using card_le_univ (trueDirections x)
      rw [Nat.odd_iff]
      omega
    rw [hfilter, filter_or, card_union_of_disjoint]
    · exact (balanced_cube_even_adjacent_layers hr hb 2 (by decide) (by decide)).add
        (balanced_cube_even_adjacent_layers hr hb 6 (by decide) (by decide))
    · apply Finset.disjoint_left.mpr
      intro x hx hy
      have hlo := (mem_filter.mp hx).2
      have hhi := (mem_filter.mp hy).2
      omega
  have hodd : (∑ x ∈ C, booleanWeight x % 2) = 33 := by
    have ht (x : Q 9) : booleanWeight x % 2 = if booleanWeight x % 2 = 1 then 1 else 0 := by
      split <;> omega
    calc
      _ = ∑ x ∈ C, if booleanWeight x % 2 = 1 then 1 else 0 := sum_congr rfl (fun x _ => ht x)
      _ = 33 := by
        rw [← sum_filter, sum_const, cubic_odd_weight_half_card hc hr]
        rfl
  have hs : (∑ x ∈ C, booleanWeight x) =
      2 * (∑ x ∈ C, booleanWeight x / 2) + ∑ x ∈ C, booleanWeight x % 2 := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl (fun x _ => by omega)
  rw [hodd] at hs
  obtain ⟨k, hk⟩ := he
  omega

private lemma profile_sum_weight {C : Finset (Q 9)} (r : Fin 9 → ℤ)
    (hhalf : ∀ i, ((C.filter (fun x => x i = true)).card : ℤ) + 2 * r i = 33) :
    ((∑ x ∈ C, booleanWeight x : ℕ) : ℤ) = 297 - 2 * ∑ i, r i := by
  have he : (∑ x ∈ C, booleanWeight x) = ∑ i : Fin 9, (C.filter fun x => x i = true).card := by
    simp only [booleanWeight, trueDirections, card_filter]
    exact sum_comm
  rw [he]
  push_cast
  have hi (i : Fin 9) : ((C.filter fun x => x i = true).card : ℤ) = 33 - 2 * r i := by
    linarith only [hhalf i]
  simp_rw [hi, sum_sub_distrib, ← mul_sum]
  norm_num

/-- The total normalized coordinate deficit of a 66-point balanced cubic
support is even. -/
theorem balanced_sixty_six_even_total_deficit {C : Finset (Q 9)} (hc : C.card = 66)
    (hr : ((hypercube 9).induce (C : Set _)).IsRegularOfDegree 3) (hb : IsBalanced C)
    (r : Fin 9 → ℤ) (hhalf : ∀ i, ((C.filter (fun x => x i = true)).card : ℤ) + 2 * r i = 33) :
    (∑ i, r i) % 2 = 0 := by
  have hp := balanced_sixty_six_weight_mod_four hc hr hb
  have hs := profile_sum_weight r hhalf
  have hmod : ((∑ x ∈ C, booleanWeight x : ℕ) : ℤ) % 4 = 1 := by exact_mod_cast hp
  rw [hs] at hmod
  omega

#print axioms balanced_cube_even_adjacent_layers
#print axioms balanced_sixty_six_even_total_deficit

end D5.S3.Combinatorics.Graph.HypercubeCritical
