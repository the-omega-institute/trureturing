/- GID: D5/S3/Fourier/Concentration/ClippedMomentWeights
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/ClippedMomentWeights
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive-part weights minimize squared mass subject to a lower moment bound. -/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-! The minimum squared mass of a probability law with a lower bound on one real moment. -/

open Finset

noncomputable section

namespace D5.S3.Fourier.Concentration.ClippedMomentWeights

private def clipped {ι : Type*} (c : ι → ℝ) (C t : ℝ) (i : ι) : ℝ :=
  max 0 (1 - t * (C - c i))

private def clippedWeight {ι : Type*} [Fintype ι] (c : ι → ℝ) (C t : ℝ) (i : ι) : ℝ :=
  clipped c C t i / (∑ j, clipped c C t j)

private theorem clipped_sum_pos {ι : Type*} [Fintype ι] (c : ι → ℝ) {C : ℝ}
    (hC : ∃ j, c j = C) (t : ℝ) : 0 < ∑ i, clipped c C t i := by
  obtain ⟨j, hj⟩ := hC
  have hle := Finset.single_le_sum (s := (Finset.univ : Finset ι))
    (f := clipped c C t) (fun i _ => le_max_left _ _) (mem_univ j)
  have ht : clipped c C t j = 1 := by simp [clipped, hj]
  linarith

private theorem clippedWeight_nonneg {ι : Type*} [Fintype ι] (c : ι → ℝ) {C : ℝ}
    (hC : ∃ j, c j = C) (t : ℝ) (i : ι) : 0 ≤ clippedWeight c C t i :=
  div_nonneg (le_max_left _ _) (clipped_sum_pos c hC t).le

private theorem clippedWeight_sum_eq_one {ι : Type*} [Fintype ι] (c : ι → ℝ) {C : ℝ}
    (hC : ∃ j, c j = C) (t : ℝ) : ∑ i, clippedWeight c C t i = 1 := by
  simp only [clippedWeight, ← sum_div]
  exact div_self (clipped_sum_pos c hC t).ne'

private theorem exists_clippedWeight_moment {ι : Type*} [Fintype ι] (c : ι → ℝ)
    {C a : ℝ} (hC : ∃ j, c j = C) (hAC : a ≤ C) :
    let mean := (∑ i, c i) / Fintype.card ι
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ (∑ i, max 0 (C - c i)⁻¹) ∧ (a ≤ mean → t = 0) ∧
      ∑ i, clippedWeight c C t i * c i = max mean a := by
  dsimp only
  let upper := ∑ i : ι, max 0 (C - c i)⁻¹
  have hupper : 0 ≤ upper := sum_nonneg fun _ _ => le_max_left _ _
  let moment (t : ℝ) := ∑ i, clippedWeight c C t i * c i
  have hzero : moment 0 = (∑ i, c i) / Fintype.card ι := by
    simp [moment, clippedWeight, clipped, mul_comm, ← sum_mul, div_eq_mul_inv]
  by_cases hmean : a ≤ (∑ i, c i) / Fintype.card ι
  · exact ⟨0, le_rfl, hupper, fun _ => rfl, hzero.trans (max_eq_left hmean).symm⟩
  have hcl (i : ι) : Continuous (fun t => clipped c C t i) := by
    unfold clipped
    fun_prop
  have hden : Continuous (fun t : ℝ => ∑ i, clipped c C t i) := by fun_prop
  have hcont : Continuous moment := by
    unfold moment clippedWeight
    apply continuous_finsetSum
    intro i _
    exact ((hcl i).div hden (fun t => (clipped_sum_pos c hC t).ne')).mul continuous_const
  have htop : C ≤ moment upper := by
    calc
      C = ∑ i, clippedWeight c C upper i * C := by
        rw [← sum_mul, clippedWeight_sum_eq_one c hC, one_mul]
      _ ≤ _ := by
        apply sum_le_sum
        intro i hi
        by_cases hlt : c i < C
        · have hb : (C - c i)⁻¹ ≤ upper :=
            (le_max_right _ _).trans
              (single_le_sum (f := fun j => max 0 (C - c j)⁻¹)
                (fun _ _ => le_max_left _ _) hi)
          have hz : (1 : ℝ) ≤ upper * (C - c i) :=
            (inv_le_iff_one_le_mul₀ (sub_pos.mpr hlt)).mp hb
          simp [clippedWeight, clipped, max_eq_left (sub_nonpos.mpr hz)]
        · exact mul_le_mul_of_nonneg_left (le_of_not_gt hlt) (clippedWeight_nonneg c hC upper i)
  have hlow := le_of_not_ge hmean
  have hm : a ∈ Set.Icc (moment 0) (moment upper) :=
    ⟨hzero.trans_le hlow, hAC.trans htop⟩
  obtain ⟨t, ht, hval⟩ := intermediate_value_Icc hupper hcont.continuousOn hm
  exact ⟨t, ht.1, ht.2, fun h => (hmean h).elim, hval.trans (max_eq_right hlow).symm⟩

private theorem clippedWeight_energy_difference {ι : Type*} [Fintype ι] (c : ι → ℝ) {C : ℝ}
    (hC : ∃ j, c j = C) (t : ℝ) (w : ι → ℝ) (hws : ∑ i, w i = 1) :
    let v := clippedWeight c C t
    let total := ∑ i, clipped c C t i
    (∑ i, w i ^ 2) - (∑ i, v i ^ 2) =
      (∑ i, (w i - v i) ^ 2) +
        2 * (t * ((∑ i, w i * c i) - ∑ i, v i * c i) +
          ∑ i, max 0 (t * (C - c i) - 1) * w i) / total := by
  dsimp only
  let v := clippedWeight c C t
  let raw (i : ι) := 1 - t * (C - c i)
  let total := ∑ i, clipped c C t i
  have hvsum : ∑ i, v i = 1 := clippedWeight_sum_eq_one c hC t
  have hraw (i : ι) :
      clipped c C t i * (w i - v i) =
        raw i * (w i - v i) + max 0 (t * (C - c i) - 1) * w i := by
    by_cases hri : 0 ≤ raw i
    · have hneg : t * (C - c i) - 1 ≤ 0 := by dsimp [raw] at hri; linarith
      change max 0 (raw i) * (w i - v i) = _
      rw [max_eq_right hri, max_eq_left hneg, zero_mul, add_zero]
    · have hneg : raw i ≤ 0 := le_of_not_ge hri
      have hv : v i = 0 := by
        change max 0 (raw i) / total = 0
        rw [max_eq_left hneg, zero_div]
      have hpos : 0 ≤ t * (C - c i) - 1 := by dsimp [raw] at hneg; linarith
      change max 0 (raw i) * (w i - v i) = _
      rw [hv, max_eq_left hneg, max_eq_right hpos]
      dsimp [raw]
      ring
  have hmoment : (∑ i, raw i * (w i - v i)) = t * ((∑ i, w i * c i) - ∑ i, v i * c i) := by
    have hsplit : (∑ i, raw i * (w i - v i)) =
        (1 - t * C) * ((∑ i, w i) - ∑ i, v i) +
          t * ((∑ i, w i * c i) - ∑ i, v i * c i) := by
      simp only [← sum_sub_distrib, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun i _ => by dsimp [raw]; ring
    rw [hsplit, hws, hvsum, sub_self, mul_zero, zero_add]
  have hdot :
      (∑ i, v i * (w i - v i)) =
        (t * ((∑ i, w i * c i) - ∑ i, v i * c i) +
          ∑ i, max 0 (t * (C - c i) - 1) * w i) / total := by
    calc
      _ = (∑ i, clipped c C t i * (w i - v i)) / total := by
        rw [sum_div]
        exact sum_congr rfl fun i _ => by dsimp [v, clippedWeight, total]; ring
      _ = _ := by simp only [hraw, sum_add_distrib, hmoment]
  have he : (∑ i, (w i - v i) ^ 2) + 2 * (∑ i, v i * (w i - v i)) =
      (∑ i, w i ^ 2) - ∑ i, v i ^ 2 := by
    rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [hdot, ← mul_div_assoc] at he
  exact he.symm

/-- A normalized affine positive part minimizes squared mass with a lower moment bound.
An attained anchor at or above the target gives a finite parameter bound. The squared-mass
difference is the squared distance plus the contributions of the moment and clipped entries. -/
theorem exists_clipped_moment_minimizer {ι : Type*} [Fintype ι] (c : ι → ℝ)
    {C a : ℝ} (hC : ∃ j, c j = C) (hAC : a ≤ C) :
    let positivePart := fun x : ℝ => max 0 x
    let mean := (∑ i, c i) / Fintype.card ι
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ (∑ i, max 0 (C - c i)⁻¹) ∧ (a ≤ mean → t = 0) ∧
      let u := fun i : ι => positivePart (1 - t * (C - c i))
      let v := fun i : ι => u i / ∑ j, u j
      (∀ i, 0 ≤ v i) ∧ (∑ i, v i) = 1 ∧ (∑ i, v i * c i) = max mean a ∧
      ∀ w : ι → ℝ, (∑ i, w i) = 1 →
        let distance := ∑ i, (w i - v i) ^ 2
        let gap := (∑ i, w i ^ 2) - ∑ i, v i ^ 2
        let correction := t * ((∑ i, w i * c i) - ∑ i, v i * c i) +
          ∑ i, max 0 (t * (C - c i) - 1) * w i
        gap = distance + 2 * correction / (∑ i, u i) ∧
          ((∀ i, 0 ≤ w i) → a ≤ (∑ i, w i * c i) → distance ≤ gap) := by
  obtain ⟨t, ht, hupper, hbecause, hmoment⟩ := exists_clippedWeight_moment c hC hAC
  refine ⟨t, ht, hupper, hbecause, clippedWeight_nonneg c hC t,
    clippedWeight_sum_eq_one c hC t, hmoment, ?_⟩
  intro w hws
  dsimp only
  have he := clippedWeight_energy_difference c hC t w hws
  dsimp only at he
  refine ⟨he, ?_⟩
  intro hw hwa
  change _ ≤ (∑ i, w i ^ 2) - ∑ i, clippedWeight c C t i ^ 2
  rw [he]
  apply le_add_of_nonneg_right
  apply div_nonneg (mul_nonneg (by norm_num) ?_) (clipped_sum_pos c hC t).le
  apply add_nonneg ?_ (sum_nonneg fun i _ => mul_nonneg (le_max_left _ _) (hw i))
  by_cases hmean : a ≤ (∑ i, c i) / Fintype.card ι
  · rw [hbecause hmean, zero_mul]
  · rw [hmoment, max_eq_right (le_of_not_ge hmean)]
    exact mul_nonneg ht (sub_nonneg.mpr hwa)

end D5.S3.Fourier.Concentration.ClippedMomentWeights
