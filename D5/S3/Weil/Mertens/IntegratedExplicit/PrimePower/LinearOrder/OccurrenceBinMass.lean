/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/LinearOrder/OccurrenceBinMass
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/LinearOrder/OccurrenceBinMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Logarithmic counts and inverse-root masses for actual zero ordinates. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder.SpectralSampling
import D5.S3.Weil.ZetaRvm.LocalCount
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RHMobiusWindow
import Mathlib.Analysis.PSeries

/-! Unit-bin counts and coefficient masses for zeta zero occurrences. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder

open Complex MeasureTheory Finset Set Function

open D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
open D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope (on_line)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

def occurrenceFrequency (i : ℕ) : ℝ := (actualZero i).im

theorem occurrence_norm_pos (hRH : RiemannHypothesis) (i : ℕ) :
    0 < ‖actualZero i‖ := by
  have h := Complex.abs_re_le_norm (actualZero i)
  rw [on_line hRH i] at h
  norm_num at h
  linarith

private theorem band_coord_lower {k : ℤ} {γ : ℝ}
    (hγ : frequencyBin γ = k) : |(k : ℝ)| ≤ |γ| + 1 := by
  have hr := mem_frequencyBin γ
  rw [hγ] at hr
  rw [abs_le]
  exact ⟨by linarith only [hr.2, neg_abs_le γ], by linarith only [hr.1, le_abs_self γ]⟩

/-- Every finite set of actual occurrences satisfies the unit-bin logarithmic count. -/
theorem occurrence_bin_card_majorant :
    ∃ A : ℝ, 0 < A ∧ ∀ (T : Finset ℕ) (k : ℤ),
      ((T.filter (fun i => frequencyBin (occurrenceFrequency i) = k)).card : ℝ) ≤
        A * Real.log (|(k : ℝ)|+3) := by
  classical
  obtain ⟨A, hA, hcount⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  refine ⟨A, zero_lt_one.trans_le hA, ?_⟩
  intro T k
  let W := Zeta23.zerosIn (k : ℝ) ((k : ℝ)+1)
  let F := (Zeta23.zerosIn_finite (k : ℝ) ((k : ℝ)+1)).toFinset
  let I := T.filter (fun i => frequencyBin (occurrenceFrequency i) = k)
  let f (i : ℕ) : ℝ := if actualZero i ∈ F then 1 else 0
  have hF (ρ : ℂ) : ρ ∈ F ↔ ρ ∈ W := Set.Finite.mem_toFinset _
  have hIS (i : ℕ) (hi : i ∈ I) : actualZero i ∈ F := by
    have hmem := mem_frequencyBin (occurrenceFrequency i)
    rw [(Finset.mem_filter.mp hi).2] at hmem
    exact (hF _).2 ⟨D5.S3.Weil.Mertens.ZeroAbscissaPower.actual_zero i, hmem⟩
  have hSN : (I.card : ℝ) ≤ (Zeta23.zetaZeroConfig.N k ((k : ℝ)+1) : ℝ) := by
    obtain ⟨hs, hsum⟩ := D5.S3.Weil.Mertens.ZeroAbscissaPower.occurrence_finite_sum F (fun ρ hρ => ((hF ρ).1 hρ).1)
      (fun _ => 1) (fun _ => zero_le_one)
    have hsum' : (∑' i : ℕ, f i) = (Zeta23.zetaZeroConfig.N k ((k : ℝ)+1) : ℝ) := by
      rw [hsum, Zeta23.zetaZeroConfig_N, Zeta23.Ncount, finsum_mem_eq_finite_toFinset_sum _
        (Zeta23.zerosIn_finite (k : ℝ) ((k : ℝ)+1)), Nat.cast_sum]
      simp only [mul_one]
      rfl
    calc
      _ = ∑ i ∈ I, (1 : ℝ) := by simp [nsmul_eq_mul]
      _ = ∑ i ∈ I, f i := (Finset.sum_congr rfl (fun i hi => ite_eq_left (hIS i hi))).symm
      _ ≤ _ := (hs.sum_le_tsum I (fun i _ => by split_ifs <;> norm_num)).trans_eq hsum'

  exact hSN.trans (hcount k)

private theorem inverse_occurrence_le_of_bin (hRH : RiemannHypothesis) {i : ℕ} {k : ℤ}
    (hi : frequencyBin (occurrenceFrequency i) = k) :
    (‖actualZero i‖)⁻¹ ≤ 5 / (|(k : ℝ)|+1) := by
  have h := band_coord_lower hi
  have hhalf := Complex.abs_re_le_norm (actualZero i)
  rw [on_line hRH i] at hhalf
  norm_num at hhalf
  have him : |occurrenceFrequency i| ≤ ‖actualZero i‖ := Complex.abs_im_le_norm _
  have hnorm := occurrence_norm_pos hRH i
  rw [inv_eq_one_div, div_le_div_iff₀ hnorm (by positivity)]
  linarith only [h, hhalf, him]

/-- Local inverse-root mass with any positive loss in the exponent. -/
theorem occurrence_bin_power_majorant_at (hRH : RiemannHypothesis) {η : ℝ} (hη : 0 < η) :
    ∃ D : ℝ, 0 < D ∧ ∀ (T : Finset ℕ) (k : ℤ),
      ∑ i ∈ T with frequencyBin (occurrenceFrequency i) = k, (‖actualZero i‖)⁻¹ ≤
        D * (|(k : ℝ)|+1)^(η-1) := by
  obtain ⟨A, hA, hcount⟩ := occurrence_bin_card_majorant
  let L := Real.log 3 + η⁻¹
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨5*A*L, by positivity, fun T k => ?_⟩
  let x := |(k : ℝ)|+1
  have hx : 1 ≤ x := by dsimp [x]; linarith [abs_nonneg (k : ℝ)]
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hcount' : Real.log (|(k : ℝ)|+3) ≤ L*x^η := by
    have hlog := Real.log_le_rpow_div hx0.le hη
    have hpow := Real.one_le_rpow hx hη.le
    calc
      _ ≤ Real.log (3*x) := Real.log_le_log (by positivity) (by dsimp [x]; linarith [abs_nonneg (k : ℝ)])
      _ = Real.log 3 + Real.log x := Real.log_mul (by norm_num) hx0.ne'
      _ ≤ _ := by
        dsimp [L]
        have h := mul_le_mul_of_nonneg_left hpow (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3))
        rw [div_eq_mul_inv] at hlog
        nlinarith only [hlog, h]
  calc
    _ ≤ ∑ i ∈ T with frequencyBin (occurrenceFrequency i) = k, 5/x :=
      Finset.sum_le_sum (fun i hi => inverse_occurrence_le_of_bin hRH (Finset.mem_filter.mp hi).2)
    _ = ((T.filter (fun i => frequencyBin (occurrenceFrequency i) = k)).card : ℝ) * (5/x) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ A * Real.log (|(k : ℝ)|+3) * (5/x) :=
      mul_le_mul_of_nonneg_right (hcount T k) (by positivity)
    _ ≤ A * (L*x^η) * (5/x) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcount' hA.le) (by positivity)
    _ = _ := by
      change _ = 5*A*L*x^(η-1)
      rw [Real.rpow_sub hx0, Real.rpow_one]
      ring

theorem occurrence_bin_power_majorant (hRH : RiemannHypothesis) :
    ∃ D : ℝ, 0 < D ∧ ∀ (T : Finset ℕ) (k : ℤ),
      ∑ i ∈ T with frequencyBin (occurrenceFrequency i) = k, (‖actualZero i‖)⁻¹ ≤
        D * (|(k : ℝ)|+1)^(-3/4 : ℝ) := by
  simpa only [show (1/4 : ℝ)-1 = -3/4 by norm_num] using
    occurrence_bin_power_majorant_at hRH (η := 1/4) (by norm_num)

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder
