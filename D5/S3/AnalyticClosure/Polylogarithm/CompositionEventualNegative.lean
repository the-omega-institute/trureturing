/- GID: D5/S3/AnalyticClosure/Polylogarithm/CompositionEventualNegative
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/Polylogarithm/CompositionEventualNegative
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict eventual negativity of the actual ordinary reciprocal coefficients. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.AnalyticClosure.Polylogarithm.CompositionSignedContour

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Complex Filter MeasureTheory Metric Set Topology
open scoped Interval ComplexConjugate

namespace D5.S3.AnalyticClosure.Polylogarithm.CompositionEventualNegative

open private actual_signed_contour from
  D5.S3.AnalyticClosure.Polylogarithm.CompositionSignedContour

private theorem positive_mass {h : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hc : ContinuousOn h (Icc 0 b)) (h0 : h 0 = 0)
    (hp : ∀ x, 0 < x → x ≤ b → 0 < h x) :
    ∃ c beta : ℝ, 0 < c ∧ beta < b ∧ ∀ n : ℕ,
      c * Real.exp (-(n : ℝ) * beta) ≤
        (1 / Real.pi) * ∫ x in 0..b, h x * Real.exp (-(n : ℝ) * x) := by
  let alpha : ℝ := b / 3
  let beta : ℝ := 2 * b / 3
  have ha : 0 < alpha := by dsimp [alpha]; positivity
  have hab : alpha < beta := by dsimp [alpha, beta]; linarith
  have hbb : beta < b := by dsimp [beta]; linarith
  have hsub : Icc alpha beta ⊆ Icc 0 b := Icc_subset_Icc ha.le hbb.le
  obtain ⟨x0, hx0, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr hab.le) (hc.mono hsub)
  have hm : 0 < h x0 := hp x0 (ha.trans_le hx0.1) (hx0.2.trans hbb.le)
  refine ⟨h x0 * (beta - alpha) / Real.pi, beta, by positivity, hbb, ?_⟩
  intro n
  let f : ℝ → ℝ := fun x ↦ h x * Real.exp (-(n : ℝ) * x)
  have hfc : ContinuousOn f (Icc 0 b) := hc.mul (by fun_prop)
  have hfi : IntervalIntegrable f volume 0 b := hfc.intervalIntegrable_of_Icc hb.le
  have hfn : ∀ x ∈ Icc 0 b, 0 ≤ f x := by
    intro x hx
    apply mul_nonneg _ (Real.exp_pos _).le
    rcases eq_or_lt_of_le hx.1 with heq | hlt
    · rw [← heq, h0]
    · exact (hp x hlt hx.2).le
  have hlocal : h x0 * Real.exp (-(n : ℝ) * beta) * (beta - alpha) ≤
      ∫ x in alpha..beta, f x := by
    calc
      _ = ∫ _ : ℝ in alpha..beta, h x0 * Real.exp (-(n : ℝ) * beta) := by
        simp [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
      _ ≤ _ := intervalIntegral.integral_mono_on hab.le intervalIntegrable_const
        (hfc.mono hsub |>.intervalIntegrable_of_Icc hab.le) (by
          intro x hx
          apply mul_le_mul (hmin hx) _ (Real.exp_pos _).le (hm.le.trans (hmin hx))
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonpos_left hx.2 (by positivity))
  have hglobal : (∫ x in alpha..beta, f x) ≤ ∫ x in 0..b, f x :=
    intervalIntegral.integral_mono_interval ha.le hab.le hbb.le
      ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _
        (fun x hx ↦ hfn x (Ioc_subset_Icc_self hx)))) hfi
  have hh := mul_le_mul_of_nonneg_left (hlocal.trans hglobal)
    (by positivity : 0 ≤ 1 / Real.pi)
  dsimp [f] at hh
  convert hh using 1 <;> ring

private theorem exponential_dominance {B c beta b : ℝ} (hc : 0 < c) (hbeta : beta < b) :
    ∀ᶠ n : ℕ in atTop,
      B * Real.exp (-(n : ℝ) * b) < c * Real.exp (-(n : ℝ) * beta) := by
  have hq0 : 0 ≤ Real.exp (beta - b) := (Real.exp_pos _).le
  have hq1 : Real.exp (beta - b) < 1 := Real.exp_lt_one_iff.mpr (sub_neg.mpr hbeta)
  have ht := tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1)
    (x := B)
  have he : ∀ᶠ n : ℕ in atTop, B * Real.exp (beta - b) ^ n < c := by
    apply ht.eventually
    simpa using Iio_mem_nhds hc
  filter_upwards [he] with n hn
  have hexp : Real.exp (-(n : ℝ) * b) =
      Real.exp (beta - b) ^ n * Real.exp (-(n : ℝ) * beta) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [hexp, ← mul_assoc]
  exact mul_lt_mul_of_pos_right hn (Real.exp_pos _)

/-- The ordinary inverse coefficients of every actual normalized composition are
strictly negative beyond a parameter-dependent positive threshold. -/
theorem result (head : ℕ+) (tail : List ℕ+) (ell : ℕ+) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      CompositionReciprocalSeries.ordinaryCoefficient head tail ell n < 0 := by
  obtain ⟨b, B, hb, h, hc, h0, hp, hbound⟩ := actual_signed_contour head tail ell
  obtain ⟨c, beta, hcpos, hbeta, hmass⟩ := positive_mass hb hc h0 hp
  obtain ⟨N, hN⟩ := eventually_atTop.mp (exponential_dominance (B := B) hcpos hbeta)
  refine ⟨max 1 N, le_max_left _ _, ?_⟩
  intro n hn
  have he := hN n ((le_max_right 1 N).trans hn)
  have hm := hmass n
  have ha := hbound n
  linarith

end D5.S3.AnalyticClosure.Polylogarithm.CompositionEventualNegative
