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
open private trueDirections cubic_parity_half_card prefix_weight_le_of_card_le from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixSignedModelProbe
open private cubeParity from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private distance_parity from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction
open private coordinate_profile_weight_bound from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixDistanceSumProbe
open private shell from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtyShellCompositionProbe
open private sixty_six_distance_seven_le_eight from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixShellProbe

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

private lemma weight_three_directions (x : Q 9) :
    (univ.filter fun i => weight (flip x i) = 3).card =
      (if weight x = 2 then 7 else 0) + (if weight x = 4 then 4 else 0) := by
  by_cases h₂ : weight x = 2
  · have he : (univ.filter fun i => weight (flip x i) = 3) = univ \ trueDirections x := by
      ext i
      cases hi : x i <;> simp [weight_flip, hi, h₂, trueDirections]
    rw [he, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
    change 9 - weight x = _
    simp [h₂]
  by_cases h₄ : weight x = 4
  · have he : (univ.filter fun i => weight (flip x i) = 3) = trueDirections x := by
      ext i
      cases hi : x i <;> simp [weight_flip, hi, h₄, trueDirections]
    rw [he]
    change weight x = _
    simp [h₄]
  have he : (univ.filter fun i => weight (flip x i) = 3) = ∅ := by
    apply filter_eq_empty_iff.mpr
    intro i _
    rw [weight_flip]
    split <;> omega
  simp [he, h₂, h₄]

/-- The selected weight-two and weight-three layers have the same parity.
Every exterior vertex has even selected degree, while selected vertices have
odd degree. Summing across all weight-three roots counts each selected
weight-two vertex seven times and each selected weight-four vertex four times. -/
theorem balanced_cube_even_two_three_layers {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set _)).IsRegularOfDegree 3) (hb : IsBalanced C) :
    Even (C.filter (fun x => weight x = 2 ∨ weight x = 3)).card := by
  let T : Finset (Q 9) := univ.filter fun x => weight x = 3
  have hodd (x : Q 9) : Odd (directions C x).card ↔ x ∈ C := by
    by_cases hx : x ∈ C
    · norm_num [hx, regular_directions C hr hx]
    · have he := exterior_even C hr hb x hx
      simp [hx, ← Nat.not_even_iff_odd, he]
  have hpar : Even (∑ x ∈ T, (directions C x).card) ↔
      Even (C.filter fun x => weight x = 3).card := by
    rw [even_sum_iff_even_card_odd]
    simp_rw [hodd]
    have he : T.filter (· ∈ C) = C.filter (fun x => weight x = 3) := by
      ext x
      simp [T, and_comm]
    rw [he]
  have hsum : (∑ x ∈ T, (directions C x).card) =
      7 * (C.filter fun x => weight x = 2).card + 4 * (C.filter fun x => weight x = 4).card := by
    calc
      _ = ∑ i : Fin 9, ∑ x : Q 9, if weight x = 3 ∧ flip x i ∈ C then 1 else 0 := by
        simp only [directions, card_filter]
        rw [sum_comm]
        apply sum_congr rfl
        intro i _
        simp only [T, sum_filter]
        apply sum_congr rfl
        intro x _
        split <;> simp_all
      _ = ∑ i : Fin 9, ∑ x : Q 9, if x ∈ C ∧ weight (flip x i) = 3 then 1 else 0 := by
        apply sum_congr rfl
        intro i _
        let e : Q 9 ≃ Q 9 :=
          ⟨(flip · i), (flip · i), (fun x => BalancedCriticalSpectrum.flip_flip x i),
            (fun x => BalancedCriticalSpectrum.flip_flip x i)⟩
        conv_lhs => rw [← e.sum_comp]
        simp [e, and_comm]
      _ = ∑ x ∈ C, (univ.filter fun i => weight (flip x i) = 3).card := by
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
        simp_rw [weight_three_directions]
        rw [sum_add_distrib, ← sum_filter, ← sum_filter, sum_const, sum_const]
        simp [Nat.mul_comm]
  rw [hsum, Nat.even_iff, Nat.even_iff] at hpar
  rw [filter_or, card_union_of_disjoint]
  · rw [Nat.even_iff]
    rw [Nat.add_mod]
    have h := hpar
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

/-- A 66-vertex balanced cubic support of Boolean weight at most four has
total weight congruent to one modulo four. -/
theorem balanced_sixty_six_weight_mod_four {C : Finset (Q 9)} (hc : C.card = 66)
    (hr : ((hypercube 9).induce (C : Set _)).IsRegularOfDegree 3) (hb : IsBalanced C)
    (hcap : ∀ x ∈ C, weight x ≤ 4) : (∑ x ∈ C, weight x) % 4 = 1 := by
  have he : Even (∑ x ∈ C, weight x / 2) := by
    rw [even_sum_iff_even_card_odd]
    have hfilter : (C.filter fun x => Odd (weight x / 2)) =
        C.filter (fun x => weight x = 2 ∨ weight x = 3) := by
      ext x
      simp only [mem_filter]
      refine and_congr_right fun hx => ?_
      have h := hcap x hx
      rw [Nat.odd_iff]
      omega
    rw [hfilter]
    exact balanced_cube_even_two_three_layers hr hb
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

private def profileDeficit (p : List ℤ) (i : Fin 9) : ℤ :=
  p[i.val]?.getD 0

private lemma profileDeficit_ofFn (r : Fin 9 → ℤ) :
    profileDeficit (List.ofFn r) = r := by
  funext i
  simp only [profileDeficit, List.getElem?_ofFn, dif_pos i.isLt, Option.getD_some]

private def obstructedByWeightParity (r : Fin 9 → ℤ) : Prop :=
  Monotone r ∧ (∀ i, 0 ≤ r i) ∧
    (∑ i, r i) % 2 = 1 ∧ (∑ i ∈ Icc (0 : Fin 9) 4, r i) * 2 + 4 > ∑ i, r i

private instance (r : Fin 9 → ℤ) : Decidable (obstructedByWeightParity r) := by
  unfold obstructedByWeightParity Monotone
  infer_instance

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

/-- A profile of odd total deficit is impossible when its five smallest
deficits already exceed the maximum weight of a support vertex. -/
theorem no_sixty_six_weight_parity_profile {C : Finset (Q 9)} (hc : C.card = 66)
    (hr : ((hypercube 9).induce (C : Set _)).IsRegularOfDegree 3) (hb : IsBalanced C)
    (r : Fin 9 → ℤ) (hhalf : ∀ i, ((C.filter (fun x => x i = true)).card : ℤ) + 2 * r i = 33)
    (hbad : obstructedByWeightParity r) : False := by
  obtain ⟨hmono, hnonneg, hodd, hprefix⟩ := hbad
  have hd := huang_balanced_cubic_sixty_six_diameter_le_seven hc hr hb
  have hcap (x : Q 9) (hx : x ∈ C) : weight x ≤ 4 := by
    by_contra! hxw
    have hcard : (Icc (0 : Fin 9) 4).card = 5 := by decide
    have hsm := prefix_weight_le_of_card_le hmono hnonneg
      (T := trueDirections x) (a := 0) (b := 4) (fun i _ => mem_Ici.mpr (Fin.zero_le i))
      (by rw [hcard]; exact hxw)
    have hwt := coordinate_profile_weight_bound hc hr hb (fun _ => true) r hhalf hx
    rw [show (∑ i, if x i = (fun _ : Fin 9 => true) i then r i else 0) =
      ∑ i ∈ trueDirections x, r i from (sum_filter _ _).symm] at hwt
    have hs := sixty_six_distance_seven_le_eight hc hr hb hd hx
    omega
  have hp := balanced_sixty_six_weight_mod_four hc hr hb hcap
  have hs := profile_sum_weight r hhalf
  have hmod : ((∑ x ∈ C, weight x : ℕ) : ℤ) % 4 = 1 := by exact_mod_cast hp
  rw [hs] at hmod
  omega

/-- The residual profiles after systematic application of the weight-layer parity law. -/
def sixtySixProfilesAfterWeightParity : List (List ℤ) :=
  sixtySixProfilesAfterUniformFour.filter
    (fun p => !decide (obstructedByWeightParity (profileDeficit p)))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
-- Check the parity and five-smallest-coordinate inequalities on every residual profile.
theorem sixtySixProfilesAfterWeightParity_length :
    sixtySixProfilesAfterWeightParity.length = 47 := by
  decide +kernel

/-- A hypothetical 66-point Huang-balanced cubic support has one of 47
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
  simp only [sixtySixProfilesAfterWeightParity, List.mem_filter, Bool.not_eq_true',
    decide_eq_false_iff_not, profileDeficit_ofFn]
  exact ⟨hprofile, no_sixty_six_weight_parity_profile hs hreg hbal r hhalf⟩

#print axioms balanced_cube_even_two_three_layers
#print axioms q9_sixty_six_mem_profiles_after_weight_parity

end D5.S3.Combinatorics.Graph.HypercubeCritical
