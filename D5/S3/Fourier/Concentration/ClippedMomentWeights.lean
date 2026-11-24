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
    {C a : ℝ} (hc : ∀ i, c i ≤ C) (hC : ∃ j, c j = C)
    (ha : (∑ i, c i) / Fintype.card ι ≤ a) (hAC : a ≤ C) :
    ∃ t : ℝ, 0 ≤ t ∧ ∑ i, clippedWeight c C t i * c i = a := by
  classical
  let upper := 1 + ∑ i : ι, (C - c i)⁻¹
  have hparts : ∀ i, 0 ≤ (C - c i)⁻¹ := fun i => inv_nonneg.mpr (sub_nonneg.mpr (hc i))
  have hupper : 0 ≤ upper := add_nonneg zero_le_one (sum_nonneg fun i _ => hparts i)
  let moment (t : ℝ) := ∑ i, clippedWeight c C t i * c i
  have hcl (i : ι) : Continuous (fun t => clipped c C t i) := by
    unfold clipped
    fun_prop
  have hden : Continuous (fun t : ℝ => ∑ i, clipped c C t i) := by fun_prop
  have hcont : Continuous moment := by
    unfold moment clippedWeight
    apply continuous_finsetSum
    intro i _
    exact ((hcl i).div hden (fun t => (clipped_sum_pos c hC t).ne')).mul continuous_const
  have hzero : moment 0 = (∑ i, c i) / Fintype.card ι := by
    simp [moment, clippedWeight, clipped, mul_comm, ← sum_mul, div_eq_mul_inv]
  have htop : moment upper = C := by
    calc
      _ = ∑ i, clippedWeight c C upper i * C := by
        apply sum_congr rfl
        intro i hi
        rcases (hc i).eq_or_lt with heq | hlt
        · rw [heq]
        · have hb : (C - c i)⁻¹ ≤ upper := by
            have := Finset.single_le_sum (s := (Finset.univ : Finset ι))
              (f := fun j => (C - c j)⁻¹) (fun j _ => hparts j) hi
            dsimp only [upper]
            linarith
          have hz : (1 : ℝ) ≤ upper * (C - c i) :=
            (inv_le_iff_one_le_mul₀ (sub_pos.mpr hlt)).mp hb
          simp [clippedWeight, clipped, max_eq_left (sub_nonpos.mpr hz)]
      _ = C := by rw [← sum_mul, clippedWeight_sum_eq_one c hC, one_mul]
  have hm : a ∈ Set.Icc (moment 0) (moment upper) := by
    rw [hzero, htop]
    exact ⟨ha, hAC⟩
  obtain ⟨t, ht, hval⟩ := intermediate_value_Icc hupper hcont.continuousOn hm
  exact ⟨t, ht.1, hval⟩

private theorem clippedWeight_energy_gap {ι : Type*} [Fintype ι] (c : ι → ℝ) {C : ℝ}
    (hC : ∃ j, c j = C) {t : ℝ} (ht : 0 ≤ t) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hws : ∑ i, w i = 1)
    (hm : (∑ i, clippedWeight c C t i * c i) ≤ ∑ i, w i * c i) :
    (∑ i, (w i - clippedWeight c C t i) ^ 2) ≤
      (∑ i, w i ^ 2) - ∑ i, clippedWeight c C t i ^ 2 := by
  let v := clippedWeight c C t
  let raw (i : ι) := 1 - t * (C - c i)
  let total := ∑ i, clipped c C t i
  have hvsum : ∑ i, v i = 1 := clippedWeight_sum_eq_one c hC t
  have hraw (i : ι) :
      raw i * (w i - v i) ≤ clipped c C t i * (w i - v i) := by
    by_cases hri : 0 ≤ raw i
    · simp [clipped, ← show raw i = 1 - t * (C - c i) from rfl, max_eq_right hri]
    · have hh : raw i ≤ 0 := le_of_not_ge hri
      have hv : v i = 0 := by
        change max 0 (raw i) / total = 0
        rw [max_eq_left hh, zero_div]
      rw [hv, sub_zero]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (hw i)
  have hmoment : 0 ≤ ∑ i, raw i * (w i - v i) := by
    have hsplit : (∑ i, raw i * (w i - v i)) =
        (1 - t * C) * ((∑ i, w i) - ∑ i, v i) +
          t * ((∑ i, w i * c i) - ∑ i, v i * c i) := by
      simp only [← sum_sub_distrib, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro i _
      simp only [raw]
      ring
    rw [hsplit, hws, hvsum, sub_self, mul_zero, zero_add]
    exact mul_nonneg ht (sub_nonneg.mpr hm)
  have hdot : 0 ≤ ∑ i, v i * (w i - v i) := by
    calc
      _ ≤ (∑ i, raw i * (w i - v i)) / total :=
        div_nonneg hmoment (clipped_sum_pos c hC t).le
      _ ≤ (∑ i, clipped c C t i * (w i - v i)) / total :=
        div_le_div_of_nonneg_right (sum_le_sum fun i _ => hraw i) (clipped_sum_pos c hC t).le
      _ = _ := by
        rw [sum_div]
        apply sum_congr rfl
        intro i _
        dsimp [v, clippedWeight, total]
        ring
  have he : (∑ i, (w i - v i) ^ 2) + 2 * (∑ i, v i * (w i - v i)) =
      (∑ i, w i ^ 2) - ∑ i, v i ^ 2 := by
    rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  linarith only [he, hdot]

/-- For a target between the uniform mean and the attained maximum, some normalized positive part
of an affine function of the readout attains the target. Its squared-mass advantage over any
feasible weight is at least the squared distance to that weight. -/
theorem exists_clipped_moment_minimizer {ι : Type*} [Fintype ι] (c : ι → ℝ)
    {C a : ℝ} (hc : ∀ i, c i ≤ C) (hC : ∃ j, c j = C)
    (ha : (∑ i, c i) / Fintype.card ι ≤ a) (hAC : a ≤ C) :
    let positivePart := fun x : ℝ => max 0 x
    ∃ t : ℝ, 0 ≤ t ∧
      let u := fun i : ι => positivePart (1 - t * (C - c i))
      let v := fun i : ι => u i / ∑ j, u j
      (∀ i, 0 ≤ v i) ∧ (∑ i, v i) = 1 ∧ (∑ i, v i * c i) = a ∧
      ∀ w : ι → ℝ, (∀ i, 0 ≤ w i) → (∑ i, w i) = 1 → a ≤ (∑ i, w i * c i) →
        (∑ i, (w i - v i) ^ 2) ≤ (∑ i, w i ^ 2) - ∑ i, v i ^ 2 := by
  obtain ⟨t, ht, hmoment⟩ := exists_clippedWeight_moment c hc hC ha hAC
  refine ⟨t, ht, clippedWeight_nonneg c hC t, clippedWeight_sum_eq_one c hC t, hmoment, ?_⟩
  intro w hw hws hwa
  exact clippedWeight_energy_gap c hC ht w hw hws (hmoment.trans_le hwa)

end D5.S3.Fourier.Concentration.ClippedMomentWeights
