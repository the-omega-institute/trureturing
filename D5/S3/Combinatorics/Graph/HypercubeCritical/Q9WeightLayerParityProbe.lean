import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9UniformFourDeficitsProbe

/-! Exterior Huang cancellation imposes parity constraints on Boolean weight layers. -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q IsBalanced flip)
attribute [local instance] Classical.propDecidable

open private directions regular_directions exterior_even from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private trueDirections cubic_parity_half_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixSignedModelProbe
open private cubeParity from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private distance_parity from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction
open private sum_ofFn_int from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixDistanceSumProbe

namespace D5.S3.Combinatorics.Graph.HypercubeCritical

private def weight (x : Q 9) : ℕ := (trueDirections x).card

private lemma weight_flip (x : Q 9) (i : Fin 9) :
    weight (flip x i) = if x i = true then weight x - 1 else weight x + 1 := by
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
    rw [ite_eq_left h, weight, he, card_erase_of_mem (by simp [trueDirections, h])]
    rfl
  · have hf : x i = false := Bool.eq_false_of_not_eq_true h
    have he : trueDirections (flip x i) = insert i (trueDirections x) := by
      ext j
      by_cases hj : j = i
      · subst j
        simp [trueDirections, hf]
      · simp [mem_insert, hmem, hflip j hj, hj]
    rw [ite_eq_right h, weight, he, card_insert_of_notMem (by simp [trueDirections, hf])]
    rfl

private lemma weight_layer_directions (x : Q 9) (k : ℕ) :
    (univ.filter fun i => weight (flip x i) = k + 1).card =
      (if weight x = k then 9 - k else 0) + (if weight x = k + 2 then k + 2 else 0) := by
  by_cases hlo : weight x = k
  · have hne : k - 1 ≠ k + 1 := by omega
    have he : (univ.filter fun i => weight (flip x i) = k + 1) = univ \ trueDirections x := by
      ext i
      cases hi : x i <;> simp [weight_flip, hi, hlo, hne, trueDirections]
    rw [he, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
    change 9 - weight x = _
    simp [hlo]
  by_cases hhi : weight x = k + 2
  · have he : (univ.filter fun i => weight (flip x i) = k + 1) = trueDirections x := by
      ext i
      cases hi : x i <;> simp [weight_flip, hi, hhi, trueDirections] <;> omega
    rw [he]
    change weight x = _
    simp [hhi]
  have he : (univ.filter fun i => weight (flip x i) = k + 1) = ∅ := by
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
    Even (C.filter (fun x => weight x = k ∨ weight x = k + 1)).card := by
  let T : Finset (Q 9) := univ.filter fun x => weight x = k + 1
  have hodd (x : Q 9) : Odd (directions C x).card ↔ x ∈ C := by
    by_cases hx : x ∈ C
    · norm_num [hx, regular_directions C hr hx]
    · have he := exterior_even C hr hb x hx
      simp [hx, ← Nat.not_even_iff_odd, he]
  have hpar : Even (∑ x ∈ T, (directions C x).card) ↔
      Even (C.filter fun x => weight x = k + 1).card := by
    rw [even_sum_iff_even_card_odd]
    simp_rw [hodd]
    have he : T.filter (· ∈ C) = C.filter (fun x => weight x = k + 1) := by
      ext x
      simp [T, and_comm]
    rw [he]
  have hsum : (∑ x ∈ T, (directions C x).card) =
      (9 - k) * (C.filter fun x => weight x = k).card +
        (k + 2) * (C.filter fun x => weight x = k + 2).card := by
    calc
      _ = ∑ i : Fin 9, ∑ x : Q 9, if weight x = k + 1 ∧ flip x i ∈ C then 1 else 0 := by
        simp only [directions, card_filter]
        rw [sum_comm]
        apply sum_congr rfl
        intro i _
        simp only [T, sum_filter]
        apply sum_congr rfl
        intro x _
        split <;> simp_all
      _ = ∑ i : Fin 9, ∑ x : Q 9, if x ∈ C ∧ weight (flip x i) = k + 1 then 1 else 0 := by
        apply sum_congr rfl
        intro i _
        let e : Q 9 ≃ Q 9 :=
          ⟨(flip · i), (flip · i), (fun x => BalancedCriticalSpectrum.flip_flip x i),
            (fun x => BalancedCriticalSpectrum.flip_flip x i)⟩
        conv_lhs => rw [← e.sum_comp]
        simp [e, and_comm]
      _ = ∑ x ∈ C, (univ.filter fun i => weight (flip x i) = k + 1).card := by
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
    simp only [one_mul, zero_mul, add_zero, Nat.mod_mod] at hpar
    omega
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    have h2 := (mem_filter.mp hx).2
    have h3 := (mem_filter.mp hy).2
    omega

private lemma weight_mod_two (x : Q 9) :
    weight x % 2 = 0 ↔ cubeParity x = false := by
  let zeroVertex : Q 9 := fun _ => false
  have hzero : cubeParity zeroVertex = false := by decide
  have hd : hammingDist x zeroVertex = weight x := by
    simp only [hammingDist, weight, trueDirections, zeroVertex, Bool.not_eq_false]
  simpa only [hd, hzero] using distance_parity x zeroVertex

/-- A 66-vertex Huang-balanced cubic support has total Boolean weight
congruent to one modulo four. -/
theorem balanced_sixty_six_weight_mod_four {C : Finset (Q 9)} (hc : C.card = 66)
    (hr : ((hypercube 9).induce (C : Set _)).IsRegularOfDegree 3) (hb : IsBalanced C) :
    (∑ x ∈ C, weight x) % 4 = 1 := by
  have he : Even (∑ x ∈ C, weight x / 2) := by
    rw [even_sum_iff_even_card_odd]
    have hfilter : (C.filter fun x => Odd (weight x / 2)) =
        C.filter (fun x => (weight x = 2 ∨ weight x = 3) ∨
          (weight x = 6 ∨ weight x = 7)) := by
      ext x
      simp only [mem_filter]
      refine and_congr_right fun hx => ?_
      have h : weight x ≤ 9 := by
        simpa [weight] using card_le_univ (trueDirections x)
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
  have hodd : (∑ x ∈ C, weight x % 2) = 33 := by
    have ht (x : Q 9) : weight x % 2 = if cubeParity x then 1 else 0 := by
      cases hx : cubeParity x
      · have hp := (weight_mod_two x).mpr hx
        simp [hp]
      · have hp : weight x % 2 ≠ 0 := fun h =>
          (by decide : true ≠ false) (hx.symm.trans ((weight_mod_two x).mp h))
        simp only [ite_true]
        omega
    simp_rw [ht]
    rw [← sum_filter, sum_const, cubic_parity_half_card hc hr true]
    rfl
  have hs : (∑ x ∈ C, weight x) =
      2 * (∑ x ∈ C, weight x / 2) + ∑ x ∈ C, weight x % 2 := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl (fun x _ => by omega)
  rw [hodd] at hs
  obtain ⟨k, hk⟩ := he
  omega

private lemma profile_sum_weight {C : Finset (Q 9)} (r : Fin 9 → ℤ)
    (hhalf : ∀ i, ((C.filter (fun x => x i = true)).card : ℤ) + 2 * r i = 33) :
    ((∑ x ∈ C, weight x : ℕ) : ℤ) = 297 - 2 * ∑ i, r i := by
  have he : (∑ x ∈ C, weight x) = ∑ i : Fin 9, (C.filter fun x => x i = true).card := by
    simp only [weight, trueDirections, card_filter]
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
  have hmod : ((∑ x ∈ C, weight x : ℕ) : ℤ) % 4 = 1 := by exact_mod_cast hp
  rw [hs] at hmod
  omega

/-- The residual profiles with even total deficit. -/
def sixtySixProfilesAfterWeightParity : List (List ℤ) :=
  sixtySixProfilesAfterUniformFour.filter (fun p => decide (p.sum % 2 = 0))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
-- The kernel enumerates the residual profiles of even total deficit.
theorem sixtySixProfilesAfterWeightParity_length :
    sixtySixProfilesAfterWeightParity.length = 44 := by
  decide +kernel

/-- A hypothetical 66-point Huang-balanced cubic support has one of 44
normalized profiles after the weight-layer parity exclusions. -/
theorem q9_sixty_six_mem_profiles_after_weight_parity {C : Finset (Q 9)}
    (hc : C.card = 66)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) :
    ∃ (S : Finset (Q 9)) (r : Fin 9 → ℤ),
      S.card = 66 ∧ ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3 ∧
      IsBalanced S ∧ (∀ i, ((S.filter (fun x => x i = true)).card : ℤ) + 2 * r i = 33) ∧
      List.ofFn r ∈ sixtySixProfilesAfterWeightParity := by
  obtain ⟨S, r, hs, hreg, hbal, hhalf, hprofile⟩ :=
    q9_sixty_six_mem_profiles_after_uniform_four hc hr hb
  refine ⟨S, r, hs, hreg, hbal, hhalf, ?_⟩
  rw [sixtySixProfilesAfterWeightParity, List.mem_filter, decide_eq_true_eq]
  refine ⟨hprofile, ?_⟩
  rw [sum_ofFn_int]
  exact balanced_sixty_six_even_total_deficit hs hreg hbal r hhalf

#print axioms balanced_cube_even_adjacent_layers
#print axioms q9_sixty_six_mem_profiles_after_weight_parity

end D5.S3.Combinatorics.Graph.HypercubeCritical
