/- GID: D5/S3/Quantum/Analysis/MeasurableNonautonomousDysonPhillips
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/MeasurableNonautonomousDysonPhillips
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Vectorwise measurable Volterra integrals with integrable scalar clocks. -/

import D5.S3.Quantum.Analysis.StrongNonautonomousDysonPhillips
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

open scoped Nat Topology
open MeasureTheory Filter intervalIntegral
open D5.S3.Quantum.Analysis.NonautonomousDysonPhillips

namespace D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Vectorwise AE strong measurability is stable under AE strongly measurable evaluation. -/
theorem aestronglyMeasurable_evaluation {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (B : α → E →L[ℂ] E)
    (hB : ∀ x : E, AEStronglyMeasurable (fun s => B s x) μ)
    {v : α → E} (hv : AEStronglyMeasurable v μ) :
    AEStronglyMeasurable (fun s => B s (v s)) μ := by
  classical
  have hs : ∀ f : α →ₛ E, AEStronglyMeasurable (fun s => B s (f s)) μ := by
    intro f
    induction f using SimpleFunc.induction' with
    | const c => exact hB c
    | pcw h f g =>
      convert f.piecewise h.nullMeasurableSet g using 1
      ext s
      by_cases hmem : s ∈ _ <;> simp [SimpleFunc.piecewise_apply, Set.piecewise, hmem]
  have hm := hv.stronglyMeasurable_mk
  apply aestronglyMeasurable_of_tendsto_ae atTop (fun n => hs (hm.approx n))
  filter_upwards [hv.ae_eq_mk] with s hs
  rw [hs]
  exact (B s).continuous.continuousAt.tendsto.comp (hm.tendsto_approx s)

private theorem clock_ac {r t : ℝ} (hrt : r ≤ t) {g : ℝ → ℝ}
    (hg : IntegrableOn g (Set.Icc r t)) :
    AbsolutelyContinuousOnInterval (fun u => ∫ s in r..u, g s) r t := by
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hrt).mpr hg
  exact hi.absolutelyContinuousOnInterval_intervalIntegral (by simp)

private theorem ac_pow {f : ℝ → ℝ} {r t : ℝ}
    (hf : AbsolutelyContinuousOnInterval f r t) (n : ℕ) :
    AbsolutelyContinuousOnInterval (fun s => f s ^ n) r t := by
  induction n with
  | zero => simpa using (LipschitzWith.const (1 : ℝ)).absolutelyContinuousOnInterval r t
  | succ n ih => simpa only [pow_succ] using ih.fun_mul hf

/-- The L1 primitive clock has the exact factorial-weighted moment, including a zero interval. -/
theorem clock_moment {r t : ℝ} (hrt : r ≤ t) {g : ℝ → ℝ}
    (hg : IntegrableOn g (Set.Icc r t)) (n : ℕ) :
    IntervalIntegrable (fun s => g s * ((∫ z in r..s, g z)^n / n !)) volume r t ∧
    (∫ s in r..t, g s * ((∫ z in r..s, g z)^n / n !)) =
      (∫ z in r..t, g z)^(n+1) / (n+1)! := by
  let F : ℝ → ℝ := fun u => ∫ s in r..u, g s
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hrt).mpr hg
  have hF := clock_ac hrt hg
  have hpow := ac_pow hF (n+1)
  have hderiv : ∀ᵐ s, s ∈ Set.uIcc r t →
      deriv (fun u => F u ^ (n+1)) s = (n+1 : ℝ) * F s ^ n * g s := by
    filter_upwards [hi.ae_hasDerivAt_integral] with s hs hmem
    simpa [F] using ((hs hmem r (by simp)).pow (n+1)).deriv
  have hFTC := hpow.integral_deriv_eq_sub
  have heq : (fun s => deriv (fun u => F u ^ (n+1)) s) =ᵐ[volume.restrict (Set.uIcc r t)]
      (fun s => (n+1 : ℝ) * F s ^ n * g s) := by
    exact (ae_restrict_iff' measurableSet_uIcc).mpr hderiv
  have hw : IntervalIntegrable (fun s => g s * (F s ^ n / n !)) volume r t :=
    hi.mul_continuousOn ((hF.continuousOn.pow n).div_const _)
  refine ⟨hw, ?_⟩
  have heq' := intervalIntegral.integral_congr_ae_restrict heq
  change (∫ s in r..t, g s * (F s ^ n / n !)) = _
  have hfactor : (∫ s in r..t, (n+1 : ℝ) * F s ^ n * g s) =
      ((n+1 : ℝ) * n !) * (∫ s in r..t, g s * (F s ^ n / n !)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    have hn : (n ! : ℝ) ≠ 0 := by positivity
    field_simp
  rw [heq'] at hFTC
  simp only [F, intervalIntegral.integral_same, zero_pow (Nat.succ_ne_zero n), sub_zero] at hFTC
  rw [hfactor] at hFTC
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  exact (eq_div_iff (by positivity)).mpr (by simpa [mul_comm] using hFTC)

private theorem evaluation_integrable {r H : ℝ} {B : ℝ → E →L[ℂ] E}
    (hB : ∀ x : E, AEStronglyMeasurable (fun s => B s x) (volume.restrict (Set.Icc r H)))
    {g : ℝ → ℝ} (hg : IntegrableOn g (Set.Icc r H))
    (hBg : ∀ s ∈ Set.Icc r H, ‖B s‖ ≤ g s)
    {v : ℝ → E} (hv : ContinuousOn v (Set.Icc r H)) :
    IntegrableOn (fun s => B s (v s)) (Set.Icc r H) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hv
  apply (hg.mul_const C).mono'
    (aestronglyMeasurable_evaluation B hB (hv.aestronglyMeasurable measurableSet_Icc))
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  exact ((B s).le_opNorm _).trans
    (mul_le_mul (hBg s hs) (hC s hs) (norm_nonneg _) ((norm_nonneg _).trans (hBg s hs)))

end D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips
