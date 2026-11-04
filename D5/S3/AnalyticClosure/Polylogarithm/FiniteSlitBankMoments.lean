/- GID: D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitBankMoments
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/Polylogarithm/FiniteSlitBankMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A signed finite bank dominates any faster outer geometric error. -/

import D5.S3.AnalyticClosure.Polylogarithm.CompositionZeroFreeCollar
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-! Signed finite-interval moments and their strict geometric comparison. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Complex Filter MeasureTheory Set Topology
open scoped ComplexConjugate

namespace D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitBankMoments

private theorem moment_lower_bound (h : ℝ → ℝ) (R : ℝ) (hR : 1 < R)
    (hc : ContinuousOn h (Icc 1 R)) (hn : ∀ x ∈ Icc 1 R, 0 ≤ h x)
    (hp : ∀ x ∈ Ioo 1 R, 0 < h x) :
    ∃ b c : ℝ, 1 < b ∧ b < R ∧ 0 < c ∧
      ∀ n : ℕ, c / b ^ n ≤ ∫ x in (1 : ℝ)..R, h x / x ^ (n + 1) := by
  let a := (2 + R) / 3
  let b := (1 + 2 * R) / 3
  have ha : 1 < a := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a, b]; linarith
  have hb : b < R := by dsimp [b]; linarith
  have hsub : Icc a b ⊆ Icc (1 : ℝ) R := fun x hx ↦
    ⟨ha.le.trans hx.1, hx.2.trans hb.le⟩
  obtain ⟨m, hm, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr hab.le) (hc.mono hsub)
  have hmpos : 0 < h m := hp m ⟨ha.trans_le hm.1, hm.2.trans_lt hb⟩
  let c := h m * (b - a) / b
  have hbpos : 0 < b := lt_trans zero_lt_one (ha.trans hab)
  refine ⟨b, c, ha.trans hab, hb, div_pos (mul_pos hmpos (sub_pos.mpr hab)) hbpos, ?_⟩
  intro n
  have hcont : ContinuousOn (fun x : ℝ ↦ h x / x ^ (n + 1)) (Icc 1 R) :=
    hc.div (continuousOn_id.pow _) (fun x hx ↦ pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1)))
  have hint : IntervalIntegrable (fun x : ℝ ↦ h x / x ^ (n + 1)) volume 1 R :=
    hcont.intervalIntegrable_of_Icc hR.le
  have hsmall : IntervalIntegrable (fun x : ℝ ↦ h x / x ^ (n + 1)) volume a b :=
    (hcont.mono hsub).intervalIntegrable_of_Icc hab.le
  have hmono := intervalIntegral.integral_mono_on hab.le
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ h m / b ^ (n + 1)) volume a b)
    hsmall (fun x hx ↦
      div_le_div₀ (hn x (hsub hx)) (hmin hx) (pow_pos (lt_of_lt_of_le zero_lt_one (hsub hx).1) _)
        (pow_le_pow_left₀ (by linarith [(hsub hx).1] : 0 ≤ x) hx.2 _))
  have hlarge := intervalIntegral.integral_mono_interval ha.le hab.le hb.le
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx ↦
      div_nonneg (hn x ⟨hx.1.le, hx.2⟩) (pow_nonneg (by linarith [hx.1] : 0 ≤ x) _))) hint
  calc
    c / b ^ n = ∫ _ in a..b, h m / b ^ (n + 1) := by
      rw [intervalIntegral.integral_const]
      dsimp [c]
      rw [pow_succ]
      field_simp [hbpos.ne'] <;> ring
    _ ≤ ∫ x in a..b, h x / x ^ (n + 1) := hmono
    _ ≤ ∫ x in (1 : ℝ)..R, h x / x ^ (n + 1) := hlarge

/-- A continuous strictly signed finite bank supplies a lower exponential scale
strictly larger than the outer-circle error scale. No coefficient or contour
identity is a premise or a conclusion of this bank-moment estimate. -/
theorem bank_dominance (h : ℝ → ℝ) (R : ℝ) (hR : 1 < R)
    (hc : ContinuousOn h (Icc 1 R)) (hn : ∀ x ∈ Icc 1 R, 0 ≤ h x)
    (hp : ∀ x ∈ Ioo 1 R, 0 < h x) :
    ∀ B : ℝ, ∀ᶠ n : ℕ in atTop,
      B / R ^ n < (1 / Real.pi) * ∫ x in (1 : ℝ)..R, h x / x ^ (n + 1) := by
  obtain ⟨b, c, hb, hbR, hcpos, hbound⟩ := moment_lower_bound h R hR hc hn hp
  intro B
  have hratio : 0 ≤ b / R := div_nonneg (by linarith) (by linarith)
  have hratio1 : b / R < 1 := (div_lt_one (by linarith)).mpr hbR
  have hlim : Tendsto (fun n : ℕ ↦ B * (b / R) ^ n) atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hratio hratio1).const_mul B
  have hev : ∀ᶠ n : ℕ in atTop, B * (b / R) ^ n < c / Real.pi :=
    hlim.eventually (gt_mem_nhds (div_pos hcpos Real.pi_pos))
  filter_upwards [hev] with n hn'
  have hbp : 0 < b ^ n := pow_pos (by linarith) _
  have hcmp : B / R ^ n < (c / b ^ n) / Real.pi := by
    rw [div_pow] at hn'
    apply (lt_div_iff₀ Real.pi_pos).2
    apply (lt_div_iff₀ hbp).2
    have := (lt_div_iff₀ Real.pi_pos).mp hn'
    convert this using 1 <;> ring
  exact hcmp.trans_le (by
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using
      div_le_div_of_nonneg_right (hbound n) Real.pi_pos.le)

#print axioms bank_dominance

end D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitBankMoments
