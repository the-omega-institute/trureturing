/- GID: D5/S3/AnalyticClosure/Polylogarithm/CompositionBanksIntegralControl
   generality: G
   mirror-B: none(waiver:private-implementation-module)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Private radial and arc estimates for positive-composition transport. -/

import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Complex Filter MeasureTheory Metric Set Topology
open scoped Interval ComplexConjugate

namespace D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksIntegralControl

private theorem radial_div_bound : ∀ (E : ℂ → ℂ) (C : ℝ) (N M : ℕ),
    0 ≤ C → 1 ≤ N → ∀ (w : ℂ), w ≠ 0 →
    (∀ ξ : ℂ, ξ ≠ 0 →
      ‖E ξ‖ ≤ C * ‖ξ‖ ^ N * (1 + ‖-Complex.log ξ‖) ^ M) →
    ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 →
      ‖w * (E ((t : ℂ) * w) / ((t : ℂ) * w))‖ ≤
        C * ‖w‖ ^ N * t ^ (N - 1) *
          (1 + ‖-Complex.log w‖ + (-Real.log t)) ^ M := by
  intro E C N M hC hN w hw hE t ht
  have ht0 : t ≠ 0 := ne_of_gt ht.1
  have htw : (t : ℂ) * w ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr ht0) hw
  have hlogt : Real.log t ≤ 0 := Real.log_nonpos ht.1.le ht.2
  have hlog : ‖-Complex.log ((t : ℂ) * w)‖ ≤
      ‖-Complex.log w‖ + (-Real.log t) := by
    rw [Complex.log_ofReal_mul ht.1 hw]
    calc
      ‖-((Real.log t : ℂ) + Complex.log w)‖ =
          ‖(-(Real.log t : ℂ)) + (-Complex.log w)‖ := by congr 1 <;> ring
      _ ≤ ‖-(Real.log t : ℂ)‖ + ‖-Complex.log w‖ := norm_add_le _ _
      _ = ‖-Complex.log w‖ + (-Real.log t) := by
        rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hlogt]
        ring
  have hintegrand :
      ‖w * (E ((t : ℂ) * w) / ((t : ℂ) * w))‖ =
        ‖E ((t : ℂ) * w)‖ / t := by
    rw [norm_mul, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht.1]
    field_simp [norm_ne_zero_iff.mpr hw]
  rw [hintegrand]
  calc
    ‖E ((t : ℂ) * w)‖ / t ≤
        (C * ‖(t : ℂ) * w‖ ^ N *
          (1 + ‖-Complex.log ((t : ℂ) * w)‖) ^ M) / t :=
      div_le_div_of_nonneg_right (hE _ htw) ht.1.le
    _ ≤ (C * ‖(t : ℂ) * w‖ ^ N *
          (1 + ‖-Complex.log w‖ + (-Real.log t)) ^ M) / t := by
      apply div_le_div_of_nonneg_right _ ht.1.le
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (pow_nonneg (norm_nonneg _) _))
      exact pow_le_pow_left₀ (by positivity) (by linarith [hlog]) M
    _ = C * ‖w‖ ^ N * (t ^ N / t) *
          (1 + ‖-Complex.log w‖ + (-Real.log t)) ^ M := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1, mul_pow]
      ring
    _ = C * ‖w‖ ^ N * t ^ (N - 1) *
          (1 + ‖-Complex.log w‖ + (-Real.log t)) ^ M := by
      have hpow : t ^ N / t = t ^ (N - 1) := by
        conv_lhs => rw [show N = (N - 1) + 1 by omega, pow_succ]
        field_simp
      rw [hpow]
private theorem radial_one_sub_bound : ∀ (E : ℂ → ℂ) (C : ℝ) (N M : ℕ),
    0 ≤ C → ∀ (w : ℂ), w ≠ 0 → ‖w‖ < 1 →
    (∀ ξ : ℂ, ξ ≠ 0 →
      ‖E ξ‖ ≤ C * ‖ξ‖ ^ N * (1 + ‖-Complex.log ξ‖) ^ M) →
    ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 →
      ‖w * (E ((t : ℂ) * w) / (1 - (t : ℂ) * w))‖ ≤
        C * ‖w‖ ^ (N + 1) * t ^ N *
          (1 + ‖-Complex.log w‖ + (-Real.log t)) ^ M * (1 - ‖w‖)⁻¹ := by
  intro E C N M hC w hw hw1 hE t ht
  have ht0 : t ≠ 0 := ne_of_gt ht.1
  have htw : (t : ℂ) * w ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr ht0) hw
  have hlogt : Real.log t ≤ 0 := Real.log_nonpos ht.1.le ht.2
  have hlog : ‖-Complex.log ((t : ℂ) * w)‖ ≤
      ‖-Complex.log w‖ + (-Real.log t) := by
    rw [Complex.log_ofReal_mul ht.1 hw]
    calc
      ‖-((Real.log t : ℂ) + Complex.log w)‖ =
          ‖(-(Real.log t : ℂ)) + (-Complex.log w)‖ := by congr 1 <;> ring
      _ ≤ ‖-(Real.log t : ℂ)‖ + ‖-Complex.log w‖ := norm_add_le _ _
      _ = ‖-Complex.log w‖ + (-Real.log t) := by
        rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hlogt]
        ring
  have hden : ‖(1 - (t : ℂ) * w)⁻¹‖ ≤ (1 - ‖w‖)⁻¹ := by
    simpa [sub_eq_add_neg, mul_neg, norm_neg] using
      (Complex.norm_one_add_mul_inv_le ⟨ht.1.le, ht.2⟩ (by simpa using hw1) (z := -w))
  calc
    ‖w * (E ((t : ℂ) * w) / (1 - (t : ℂ) * w))‖ =
        ‖w‖ * ‖E ((t : ℂ) * w)‖ * ‖(1 - (t : ℂ) * w)⁻¹‖ := by
      rw [div_eq_mul_inv, norm_mul, norm_mul, mul_assoc]
    _ ≤ ‖w‖ *
        (C * ‖(t : ℂ) * w‖ ^ N *
          (1 + ‖-Complex.log ((t : ℂ) * w)‖) ^ M) * (1 - ‖w‖)⁻¹ := by
      gcongr
      exact hE _ htw
    _ ≤ ‖w‖ *
        (C * ‖(t : ℂ) * w‖ ^ N *
          (1 + ‖-Complex.log w‖ + (-Real.log t)) ^ M) * (1 - ‖w‖)⁻¹ := by
      have hinv : 0 ≤ (1 - ‖w‖)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hw1.le)
      apply mul_le_mul_of_nonneg_right _ hinv
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg w)
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (pow_nonneg (norm_nonneg _) _))
      exact pow_le_pow_left₀ (by positivity) (by linarith [hlog]) M
    _ = C * ‖w‖ ^ (N + 1) * t ^ N *
          (1 + ‖-Complex.log w‖ + (-Real.log t)) ^ M * (1 - ‖w‖)⁻¹ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1, mul_pow, pow_succ]
      ring
private theorem radial_majorant_integrable : ∀ (a : ℝ) (N M : ℕ),
    0 ≤ a → 1 ≤ N →
    IntervalIntegrable
      (fun t : ℝ ↦ t ^ (N - 1) * (1 + a + (-Real.log t)) ^ M)
      MeasureTheory.volume 0 1 := by
  intro a N M ha hN
  have exponential_majorant_integrable : IntegrableOn
      (fun x : ℝ ↦ Real.exp (-(N : ℝ) * x) * (1 + a + x) ^ M)
      (Set.Ioi 0) := by
    let c : ℝ := 1 + a
    have hc : 0 < c := by dsimp [c]; linarith
    have hgamma : IntegrableOn
        (fun x : ℝ ↦ Real.exp (-x) * x ^ M) (Set.Ioi 0) := by
      simpa [Real.rpow_natCast] using
        (Real.GammaIntegral_convergent (s := (M : ℝ) + 1) (by positivity))
    have htailMajor : IntegrableOn
        (fun x : ℝ ↦ (2 : ℝ) ^ M * (Real.exp (-x) * x ^ M)) (Set.Ioi c) :=
      (hgamma.mono_set (Set.Ioi_subset_Ioi hc.le)).const_mul ((2 : ℝ) ^ M)
    have htail : IntegrableOn
        (fun x : ℝ ↦ Real.exp (-(N : ℝ) * x) * (1 + a + x) ^ M)
        (Set.Ioi c) := by
      apply Integrable.mono' htailMajor
      · fun_prop
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hx0 : 0 ≤ x := le_trans hc.le hx.le
        have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
        have hexp : Real.exp (-(N : ℝ) * x) ≤ Real.exp (-x) := by
          apply Real.exp_le_exp.mpr
          nlinarith
        have hpoly : (1 + a + x) ^ M ≤ (2 * x) ^ M := by
          apply pow_le_pow_left₀ (by positivity) _ M
          have hcx : c ≤ x := hx.le
          dsimp [c] at hcx
          linarith
        calc
          ‖Real.exp (-(N : ℝ) * x) * (1 + a + x) ^ M‖ =
              Real.exp (-(N : ℝ) * x) * (1 + a + x) ^ M :=
            Real.norm_of_nonneg
              (mul_nonneg (Real.exp_pos _).le (pow_nonneg (by linarith) _))
          _ ≤ Real.exp (-x) * (2 * x) ^ M :=
            mul_le_mul hexp hpoly (pow_nonneg (by linarith) _) (Real.exp_pos _).le
          _ = (2 : ℝ) ^ M * (Real.exp (-x) * x ^ M) := by rw [mul_pow]; ring
    rw [← Set.Ioc_union_Ioi_eq_Ioi hc.le, integrableOn_union]
    refine ⟨?_, htail⟩
    have hcont : ContinuousOn
        (fun x : ℝ ↦ Real.exp (-(N : ℝ) * x) * (1 + a + x) ^ M)
        (Set.Icc 0 c) := by
      fun_prop
    exact (ContinuousOn.integrableOn_Icc hcont).mono_set Set.Ioc_subset_Icc_self
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one,
    integrableOn_Ioc_iff_integrableOn_Ioo]
  let e : ℝ → ℝ := fun x ↦ Real.exp (-x)
  have himage : e '' Set.Ioi 0 = Set.Ioo 0 1 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hx)⟩
    · intro hy
      refine ⟨-Real.log y, ?_, ?_⟩
      · have hylog : Real.log y < 0 := Real.log_neg hy.1 hy.2
        exact neg_pos.mpr hylog
      · dsimp [e]
        rw [neg_neg, Real.exp_log hy.1]
  rw [← himage]
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt e (-Real.exp (-x)) (Set.Ioi 0) x := by
    intro x hx
    simpa [e, Function.comp_def] using
      ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg).hasDerivWithinAt
  have hinj : Set.InjOn e (Set.Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    dsimp [e] at hxy
    exact neg_injective (Real.exp_injective hxy)
  refine (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    hderiv hinj _).mpr ?_
  convert exponential_majorant_integrable using 1
  funext x
  dsimp [e]
  rw [abs_neg, abs_of_pos (Real.exp_pos _), Real.log_exp]
  have hexp : Real.exp (-x) * Real.exp (-x) ^ (N - 1) =
      Real.exp (-(N : ℝ) * x) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    rw [show (N : ℝ) = ((N - 1 : ℕ) : ℝ) + 1 by
      exact_mod_cast (Nat.sub_add_cancel hN).symm]
    ring
  rw [← mul_assoc, hexp, neg_neg]
private theorem radial_majorant_integral_le : ∀ (a : ℝ) (N M : ℕ),
    0 ≤ a → 1 ≤ N →
    (∫ t in (0 : ℝ)..1, t ^ (N - 1) * (1 + a + (-Real.log t)) ^ M) ≤
      (1 + a) ^ M *
        ∫ t in (0 : ℝ)..1, t ^ (N - 1) * (1 + (-Real.log t)) ^ M := by
  intro a N M ha hN
  have haInt := radial_majorant_integrable a N M ha hN
  have hzeroInt := radial_majorant_integrable 0 N M (by norm_num) hN
  have hscaled := hzeroInt.const_mul ((1 + a) ^ M)
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on zero_le_one haInt
    (by simpa only [add_zero] using hscaled)
  intro t ht
  have hlog : 0 ≤ -Real.log t := by
    exact neg_nonneg.mpr (Real.log_nonpos ht.1 ht.2)
  have hsum : 1 + a + (-Real.log t) ≤ (1 + a) * (1 + (-Real.log t)) := by
    nlinarith
  calc
    t ^ (N - 1) * (1 + a + (-Real.log t)) ^ M ≤
        t ^ (N - 1) * ((1 + a) * (1 + (-Real.log t))) ^ M := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg ht.1 _)
      exact pow_le_pow_left₀ (by positivity) hsum M
    _ = (1 + a) ^ M * (t ^ (N - 1) * (1 + (-Real.log t)) ^ M) := by
      rw [mul_pow]
      ring
private theorem radial_div_integral_bound : ∀ (E : ℂ → ℂ) (C : ℝ) (N M : ℕ),
    0 ≤ C → 1 ≤ N → ∀ (w : ℂ), w ≠ 0 →
    (∀ ξ : ℂ, ξ ≠ 0 →
      ‖E ξ‖ ≤ C * ‖ξ‖ ^ N * (1 + ‖-Complex.log ξ‖) ^ M) →
    ‖∫ t in (0 : ℝ)..1, w * (E ((t : ℂ) * w) / ((t : ℂ) * w))‖ ≤
      ∫ t in (0 : ℝ)..1,
        C * ‖w‖ ^ N * t ^ (N - 1) *
          (1 + ‖-Complex.log w‖ + (-Real.log t)) ^ M := by
  intro E C N M hC hN w hw hE
  apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
  · exact Filter.Eventually.of_forall (fun t ht ↦ radial_div_bound E C N M hC hN w hw hE t ht)
  · have hbase := radial_majorant_integrable ‖-Complex.log w‖ N M (norm_nonneg _) hN
    have hscaled := hbase.const_mul (C * ‖w‖ ^ N)
    simpa only [mul_assoc] using hscaled
private theorem radial_one_sub_integral_bound : ∀ (E : ℂ → ℂ) (C : ℝ) (N M : ℕ),
    0 ≤ C → ∀ (w : ℂ), w ≠ 0 → ‖w‖ < 1 →
    (∀ ξ : ℂ, ξ ≠ 0 →
      ‖E ξ‖ ≤ C * ‖ξ‖ ^ N * (1 + ‖-Complex.log ξ‖) ^ M) →
    ‖∫ t in (0 : ℝ)..1, w * (E ((t : ℂ) * w) / (1 - (t : ℂ) * w))‖ ≤
      ∫ t in (0 : ℝ)..1,
        C * ‖w‖ ^ (N + 1) * t ^ N *
          (1 + ‖-Complex.log w‖ + (-Real.log t)) ^ M * (1 - ‖w‖)⁻¹ := by
  intro E C N M hC w hw hw1 hE
  apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
  · exact Filter.Eventually.of_forall
      (fun t ht ↦ radial_one_sub_bound E C N M hC w hw hw1 hE t ht)
  · have hbase := radial_majorant_integrable ‖-Complex.log w‖ (N + 1) M
      (norm_nonneg _) (by omega)
    have hscaled := hbase.const_mul
      (C * ‖w‖ ^ (N + 1) * (1 - ‖w‖)⁻¹)
    simpa only [Nat.add_sub_cancel, pow_zero, one_mul, mul_assoc, mul_left_comm,
      mul_comm] using hscaled
private theorem radial_div_uniform_bound : ∀ (E : ℂ → ℂ) (C : ℝ) (N M : ℕ),
    0 ≤ C → 1 ≤ N → ∀ (w : ℂ), w ≠ 0 →
    (∀ ξ : ℂ, ξ ≠ 0 →
      ‖E ξ‖ ≤ C * ‖ξ‖ ^ N * (1 + ‖-Complex.log ξ‖) ^ M) →
    ‖∫ t in (0 : ℝ)..1, w * (E ((t : ℂ) * w) / ((t : ℂ) * w))‖ ≤
      C * ‖w‖ ^ N * (1 + ‖-Complex.log w‖) ^ M *
        ∫ t in (0 : ℝ)..1, t ^ (N - 1) * (1 + (-Real.log t)) ^ M := by
  intro E C N M hC hN w hw hE
  calc
    ‖∫ t in (0 : ℝ)..1, w * (E ((t : ℂ) * w) / ((t : ℂ) * w))‖ ≤
        ∫ t in (0 : ℝ)..1,
          C * ‖w‖ ^ N * t ^ (N - 1) *
            (1 + ‖-Complex.log w‖ + (-Real.log t)) ^ M :=
      radial_div_integral_bound E C N M hC hN w hw hE
    _ = C * ‖w‖ ^ N *
        (∫ t in (0 : ℝ)..1,
          t ^ (N - 1) * (1 + ‖-Complex.log w‖ + (-Real.log t)) ^ M) := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext t
      ring
    _ ≤ C * ‖w‖ ^ N * ((1 + ‖-Complex.log w‖) ^ M *
        ∫ t in (0 : ℝ)..1, t ^ (N - 1) * (1 + (-Real.log t)) ^ M) := by
      apply mul_le_mul_of_nonneg_left
        (radial_majorant_integral_le ‖-Complex.log w‖ N M (norm_nonneg _) hN)
      exact mul_nonneg hC (pow_nonneg (norm_nonneg _) _)
    _ = C * ‖w‖ ^ N * (1 + ‖-Complex.log w‖) ^ M *
        ∫ t in (0 : ℝ)..1, t ^ (N - 1) * (1 + (-Real.log t)) ^ M := by ring
private theorem radial_one_sub_uniform_bound : ∀ (E : ℂ → ℂ) (C : ℝ) (N M : ℕ),
    0 ≤ C → ∀ (w : ℂ), w ≠ 0 → ‖w‖ < 1 →
    (∀ ξ : ℂ, ξ ≠ 0 →
      ‖E ξ‖ ≤ C * ‖ξ‖ ^ N * (1 + ‖-Complex.log ξ‖) ^ M) →
    ‖∫ t in (0 : ℝ)..1, w * (E ((t : ℂ) * w) / (1 - (t : ℂ) * w))‖ ≤
      C * ‖w‖ ^ (N + 1) * (1 + ‖-Complex.log w‖) ^ M * (1 - ‖w‖)⁻¹ *
        ∫ t in (0 : ℝ)..1, t ^ N * (1 + (-Real.log t)) ^ M := by
  intro E C N M hC w hw hw1 hE
  have hinv : 0 ≤ (1 - ‖w‖)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hw1.le)
  calc
    ‖∫ t in (0 : ℝ)..1, w * (E ((t : ℂ) * w) / (1 - (t : ℂ) * w))‖ ≤
        ∫ t in (0 : ℝ)..1,
          C * ‖w‖ ^ (N + 1) * t ^ N *
            (1 + ‖-Complex.log w‖ + (-Real.log t)) ^ M * (1 - ‖w‖)⁻¹ :=
      radial_one_sub_integral_bound E C N M hC w hw hw1 hE
    _ = (C * ‖w‖ ^ (N + 1) * (1 - ‖w‖)⁻¹) *
        (∫ t in (0 : ℝ)..1,
          t ^ N * (1 + ‖-Complex.log w‖ + (-Real.log t)) ^ M) := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext t
      ring
    _ ≤ (C * ‖w‖ ^ (N + 1) * (1 - ‖w‖)⁻¹) *
        ((1 + ‖-Complex.log w‖) ^ M *
          ∫ t in (0 : ℝ)..1, t ^ N * (1 + (-Real.log t)) ^ M) := by
      apply mul_le_mul_of_nonneg_left
        (by simpa only [Nat.add_sub_cancel] using
          radial_majorant_integral_le ‖-Complex.log w‖ (N + 1) M (norm_nonneg _) (by omega))
      exact mul_nonneg (mul_nonneg hC (pow_nonneg (norm_nonneg _) _)) hinv
    _ = C * ‖w‖ ^ (N + 1) * (1 + ‖-Complex.log w‖) ^ M * (1 - ‖w‖)⁻¹ *
        ∫ t in (0 : ℝ)..1, t ^ N * (1 + (-Real.log t)) ^ M := by ring
private theorem inner_arc_decay : ∀ (a : ℝ) (N M : ℕ), 0 ≤ a → 1 ≤ N →
    Tendsto
      (fun eps : ℝ ↦ eps ^ N * (1 + a + |Real.log eps|) ^ M)
      (𝓝[>] 0) (𝓝 0) := by
  intro a N M ha hN
  have hNM : (-(N : ℝ)) < 0 := by
    exact neg_lt_zero.mpr (by exact_mod_cast (show 0 < N by omega))
  have hlogpow : Tendsto
      (fun eps : ℝ ↦ eps ^ N * |Real.log eps| ^ M)
      (𝓝[>] 0) (𝓝 0) := by
    have h :=
      (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (M : ℝ) hNM).tendsto_div_nhds_zero
    apply h.congr'
    filter_upwards [eventually_mem_nhdsWithin] with eps heps
    have heps0 : 0 < eps := heps
    rw [Real.rpow_natCast, Real.rpow_neg (le_of_lt heps0), div_inv_eq_mul,
      Real.rpow_natCast]
    ring
  have hsmall : ∀ᶠ eps in 𝓝[>] (0 : ℝ), eps ∈ Set.Ioo 0 (Real.exp (-1)) :=
    Ioo_mem_nhdsGT (Real.exp_pos (-1))
  have hbound : ∀ᶠ eps in 𝓝[>] (0 : ℝ),
      0 ≤ eps ^ N * (1 + a + |Real.log eps|) ^ M ∧
      eps ^ N * (1 + a + |Real.log eps|) ^ M ≤
        (2 + a) ^ M * (eps ^ N * |Real.log eps| ^ M) := by
    filter_upwards [hsmall] with eps hepsSmall
    have heps0 : 0 < eps := hepsSmall.1
    have hlog : 1 ≤ |Real.log eps| := by
      have hle : Real.log eps < -1 := by
        rw [← Real.exp_lt_exp]
        simpa [Real.exp_log heps0] using hepsSmall.2
      rw [abs_of_nonpos (hle.le.trans (by norm_num))]
      linarith
    constructor
    · positivity
    · calc
        eps ^ N * (1 + a + |Real.log eps|) ^ M ≤
            eps ^ N * ((2 + a) * |Real.log eps|) ^ M := by
          gcongr
          nlinarith [mul_le_mul_of_nonneg_left hlog ha]
        _ = (2 + a) ^ M * (eps ^ N * |Real.log eps| ^ M) := by
          rw [mul_pow]
          ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (by simpa using hlogpow.const_mul ((2 + a) ^ M))
    (hbound.mono fun _ h ↦ h.1) (hbound.mono fun _ h ↦ h.2)
end D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksIntegralControl
