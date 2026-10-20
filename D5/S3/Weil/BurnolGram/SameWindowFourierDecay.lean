/- GID: D5/S3/Weil/BurnolGram/SameWindowFourierDecay
   generality: I
   mirror-B: D5/B/S3/Weil/BurnolGram/SameWindowFourierDecay
   mirror-E: none(waiver:analytic-same-window-Fourier-error)
   anchors: []
   utility: none
   digest: Pay actual endpoint jumps in same-window smooth Fourier approximation. -/

import D5.S3.Weil.BurnolGram.SameWindowSmoothCutoff
import D5.S3.Weil.Convention
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Fourier decay of the actual same-window error

The interior error is smooth, but its zero extension has two endpoint
jumps. A boundary-strip derivative estimate and the actual interval
integration-by-parts formula pay both jumps before division by frequency.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.BurnolGram.SameWindowFourierDecay

open Set MeasureTheory
open D5.S3.Weil.Convention
open D5.S3.Weil.BurnolGram.SameWindowSmoothCutoff
open scoped Topology Interval ContDiff

/-- The derivative is integrated on the original window, before zero extension.
Only two strips of total length 4h pay the p' term. -/
theorem sameWindowSmoothTrial_derivative_L1_error_le (a h M M1 : ℝ)
    (hh : 0 < h) (ha : 4 * h ≤ a) (hM : 0 ≤ M) (hM1 : 0 ≤ M1)
    (p : ℝ → ℂ) (hp : ContDiff ℝ ∞ p) (heven : ∀ x, p (-x) = p x)
    (hbound : ∀ x ∈ Icc (-a) a, ‖p x‖ ≤ M)
    (hbound1 : ∀ x ∈ Icc (-a) a, ‖deriv p x‖ ≤ M1) :
    (∫ x in Icc (-a) a,
      ‖deriv (fun y => p y - sameWindowSmoothTrial a h hh p hp heven y) x‖) ≤
      2 * M + 4 * h * M1 := by
  obtain ⟨_, hplateau, hc, hvar⟩ :=
    sameWindowSmoothTrial_budget a h hh ha p hp heven
  let c : ℝ → ℂ := sameWindowCutoff a h hh
  let r : ℝ → ℂ := fun x => p x - sameWindowSmoothTrial a h hh p hp heven x
  let left := Icc (-a) (-a + 2 * h)
  let right := Icc (a - 2 * h) a
  let bound : ℝ → ℝ := fun x => left.indicator (fun _ => M1) x +
    right.indicator (fun _ => M1) x + M * ‖deriv c x‖
  have hcd : ContDiff ℝ ∞ c := (sameWindowCutoff a h hh).contDiff
  have hrd : ContDiff ℝ ∞ r :=
    hp.sub (sameWindowSmoothTrial a h hh p hp heven).contDiff
  have hd (x : ℝ) : deriv r x =
      (1 - c x) * deriv p x - deriv c x * p x := by
    change deriv (fun y => p y - c y * p y) x = _
    have hdr : HasDerivAt (fun y => p y - c y * p y)
        (deriv p x - (deriv c x * p x + c x * deriv p x)) x := by
      simpa only using!
        (hp.differentiable (by simp) x).hasDerivAt.sub
          ((hcd.differentiable (by simp) x).hasDerivAt.mul
            (hp.differentiable (by simp) x).hasDerivAt)
    rw [hdr.deriv]
    ring
  have hzero : EqOn r (fun _ => 0) (Ioo (-a + 2 * h) (a - 2 * h)) := by
    intro x hx
    dsimp [r]
    rw [hplateau x ⟨hx.1.le, hx.2.le⟩, sub_self]
  have hd_zero : EqOn (deriv r) (fun _ => 0)
      (Ioo (-a + 2 * h) (a - 2 * h)) := by
    intro x hx
    simpa only [deriv_const] using hzero.deriv isOpen_Ioo hx
  have hri : IntegrableOn (fun x => ‖deriv r x‖) (Icc (-a) a) :=
    (hrd.continuous_deriv (by simp)).norm.integrableOn_Icc
  have hci : Integrable (fun x => ‖deriv c x‖) :=
    ((hcd.continuous_deriv (by simp)).integrable_of_hasCompactSupport
      (sameWindowCutoff a h hh).hasCompactSupport.deriv).norm
  have hli : Integrable (left.indicator (fun _ : ℝ => M1)) :=
    (integrableOn_const (μ := volume) (s := left) (C := M1)
      isCompact_Icc.measure_ne_top).integrable_indicator measurableSet_Icc
  have hrighti : Integrable (right.indicator (fun _ : ℝ => M1)) :=
    (integrableOn_const (μ := volume) (s := right) (C := M1)
      isCompact_Icc.measure_ne_top).integrable_indicator measurableSet_Icc
  have hbi : Integrable bound := (hli.add hrighti).add (hci.const_mul M)
  have hnonneg (x : ℝ) : 0 ≤ bound x := by
    dsimp [bound]
    exact add_nonneg (add_nonneg
      (by by_cases hx : x ∈ left <;> simp [hx, hM1])
      (by by_cases hx : x ∈ right <;> simp [hx, hM1]))
      (mul_nonneg hM (norm_nonneg _))
  have hbase (x : ℝ) (hx : x ∈ Icc (-a) a) :
      ‖deriv r x‖ ≤ M1 + M * ‖deriv c x‖ := by
    rw [hd]
    calc
      _ ≤ ‖(1 - c x) * deriv p x‖ + ‖deriv c x * p x‖ := norm_sub_le _ _
      _ = ‖1 - c x‖ * ‖deriv p x‖ + ‖deriv c x‖ * ‖p x‖ := by
        rw [norm_mul, norm_mul]
      _ ≤ 1 * ‖deriv p x‖ + ‖deriv c x‖ * M :=
        add_le_add (mul_le_mul_of_nonneg_right (hc x) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (hbound x hx) (norm_nonneg _))
      _ ≤ M1 + M * ‖deriv c x‖ := by
        rw [one_mul, mul_comm ‖deriv c x‖ M]
        exact add_le_add (hbound1 x hx) le_rfl
  have hpoint (x : ℝ) (hx : x ∈ Icc (-a) a) : ‖deriv r x‖ ≤ bound x := by
    by_cases hl : x ∈ left
    · have hb := hbase x hx
      by_cases hr : x ∈ right <;> simp only [bound, indicator_of_mem hl]
      · rw [indicator_of_mem hr]
        linarith
      · rw [indicator_of_notMem hr]
        simpa using hb
    · by_cases hr : x ∈ right
      · simpa only [bound, indicator_of_notMem hl, indicator_of_mem hr, zero_add]
          using hbase x hx
      · have hcpoint : x ∈ Ioo (-a + 2 * h) (a - 2 * h) := by
          have hl' : ¬ (-a ≤ x ∧ x ≤ -a + 2 * h) := hl
          have hr' : ¬ (a - 2 * h ≤ x ∧ x ≤ a) := hr
          constructor
          · by_contra hn
            exact hl' ⟨hx.1, by linarith⟩
          · by_contra hn
            exact hr' ⟨by linarith, hx.2⟩
        rw [hd_zero hcpoint, norm_zero]
        exact hnonneg x
  have hint (u v : ℝ) (huv : u ≤ v) :
      (∫ x : ℝ, (Icc u v).indicator (fun _ : ℝ => M1) x) = (v - u) * M1 := by
    rw [integral_indicator measurableSet_Icc, setIntegral_const]
    simp only [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr huv),
      smul_eq_mul]
  change (∫ x in Icc (-a) a, ‖deriv r x‖) ≤ _
  calc
    _ ≤ ∫ x in Icc (-a) a, bound x :=
      setIntegral_mono_on hri hbi.integrableOn measurableSet_Icc hpoint
    _ ≤ ∫ x : ℝ, bound x :=
      setIntegral_le_integral hbi (Filter.Eventually.of_forall hnonneg)
    _ = 4 * h * M1 + M * (∫ x : ℝ, ‖deriv c x‖) := by
      change (∫ x : ℝ, left.indicator (fun _ => M1) x +
        right.indicator (fun _ => M1) x + M * ‖deriv c x‖) = _
      have hadd := integral_add (hli.add hrighti) (hci.const_mul M)
      have hsplit := integral_add hli hrighti
      simp only [Pi.add_apply] at hadd hsplit
      rw [hadd, hsplit, integral_const_mul, hint (-a) (-a + 2 * h) (by linarith),
        hint (a - 2 * h) a (by linarith)]
      ring
    _ ≤ 4 * h * M1 + M * 2 :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hvar hM)
    _ = 2 * M + 4 * h * M1 := by ring

private theorem kernel_norm (t x : ℝ) : ‖fourierKernel (t : ℂ) x‖ = 1 := by
  simp [fourierKernel, Complex.norm_exp]

private theorem kernel_hasDerivAt (t x : ℝ) :
    HasDerivAt (fourierKernel (t : ℂ))
      ((-Complex.I * (t : ℂ)) * fourierKernel (t : ℂ) x) x := by
  have hcast : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using!
      (Complex.ofRealCLM.hasDerivAt : HasDerivAt Complex.ofRealCLM (Complex.ofRealCLM 1) x)
  have hz : HasDerivAt (fun y : ℝ => -Complex.I * (t : ℂ) * (y : ℂ))
      (-Complex.I * (t : ℂ)) x := by
    simpa only [mul_one] using hcast.const_mul (-Complex.I * (t : ℂ))
  change HasDerivAt (fun y : ℝ => Complex.exp (-Complex.I * (t : ℂ) * (y : ℂ)))
    ((-Complex.I * (t : ℂ)) * Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))) x
  simpa only [mul_comm] using hz.cexp

private theorem trial_eq_zero_outside (a h : ℝ) (hh : 0 < h) (ha : 4 * h ≤ a)
    (p : ℝ → ℂ) (hp : ContDiff ℝ ∞ p) (heven : ∀ x, p (-x) = p x)
    (x : ℝ) (hx : x ∉ Ioo (-a) a) :
    sameWindowSmoothTrial a h hh p hp heven x = 0 := by
  have hs := (sameWindowSmoothTrial_budget a h hh ha p hp heven).1
  by_contra hn
  have hi := hs (subset_tsupport _ hn)
  apply hx
  exact ⟨by linarith [hi.1], by linarith [hi.2]⟩

private theorem error_fourier_eq_interval (a h : ℝ) (hh : 0 < h) (ha : 4 * h ≤ a)
    (p : ℝ → ℂ) (hp : ContDiff ℝ ∞ p) (heven : ∀ x, p (-x) = p x) (t : ℝ) :
    (∫ x : ℝ, fourierKernel (t : ℂ) x * ((Ioo (-a) a).indicator p x -
      sameWindowSmoothTrial a h hh p hp heven x)) =
    ∫ x in (-a)..a, fourierKernel (t : ℂ) x *
      (p x - sameWindowSmoothTrial a h hh p hp heven x) := by
  calc
    _ = ∫ x : ℝ, (Ioo (-a) a).indicator (fun y => fourierKernel (t : ℂ) y *
        (p y - sameWindowSmoothTrial a h hh p hp heven y)) x := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      by_cases hx : x ∈ Ioo (-a) a
      · simp only [indicator_of_mem hx]
      · simp only [indicator_of_notMem hx,
          trial_eq_zero_outside a h hh ha p hp heven x hx, sub_zero, mul_zero]
    _ = ∫ x in Ioo (-a) a, fourierKernel (t : ℂ) x *
        (p x - sameWindowSmoothTrial a h hh p hp heven x) :=
      integral_indicator measurableSet_Ioo
    _ = _ := by
      rw [intervalIntegral.integral_of_le (by linarith : -a ≤ a),
        integral_Ioc_eq_integral_Ioo]

private theorem error_endpoint_identity (a h : ℝ) (hh : 0 < h) (ha : 4 * h ≤ a)
    (p : ℝ → ℂ) (hp : ContDiff ℝ ∞ p) (heven : ∀ x, p (-x) = p x) (t : ℝ) :
    (Complex.I * (t : ℂ)) *
      (∫ x : ℝ, fourierKernel (t : ℂ) x * ((Ioo (-a) a).indicator p x -
        sameWindowSmoothTrial a h hh p hp heven x)) =
      p (-a) * fourierKernel (t : ℂ) (-a) - p a * fourierKernel (t : ℂ) a +
        ∫ x in (-a)..a,
          deriv (fun y => p y - sameWindowSmoothTrial a h hh p hp heven y) x *
            fourierKernel (t : ℂ) x := by
  let r : ℝ → ℂ := fun x => p x - sameWindowSmoothTrial a h hh p hp heven x
  let k : ℝ → ℂ := fourierKernel (t : ℂ)
  have hr : ContDiff ℝ ∞ r :=
    hp.sub (sameWindowSmoothTrial a h hh p hp heven).contDiff
  have hk : Continuous k := continuous_iff_continuousAt.mpr
    (fun x => (kernel_hasDerivAt t x).continuousAt)
  have hkd : Continuous (fun x => (-Complex.I * (t : ℂ)) * k x) :=
    continuous_const.mul hk
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hr.continuous.continuousOn hk.continuousOn
    (fun x _ => (hr.differentiable (by simp) x).hasDerivAt)
    (fun x _ => kernel_hasDerivAt t x)
    ((hr.continuous_deriv (by simp)).intervalIntegrable (-a) a)
    (hkd.intervalIntegrable (-a) a)
  have hleft :
      (∫ x in (-a)..a, r x * ((-Complex.I * (t : ℂ)) * k x)) =
      (-Complex.I * (t : ℂ)) * (∫ x in (-a)..a, k x * r x) := by
    calc
      _ = ∫ x in (-a)..a, (-Complex.I * (t : ℂ)) * (k x * r x) := by
        apply intervalIntegral.integral_congr
        intro x _
        ring
      _ = _ := intervalIntegral.integral_const_mul _ _
  rw [hleft] at hip
  have hminus : r (-a) = p (-a) := by
    dsimp [r]
    rw [trial_eq_zero_outside a h hh ha p hp heven (-a) (by simp), sub_zero]
  have hplus : r a = p a := by
    dsimp [r]
    rw [trial_eq_zero_outside a h hh ha p hp heven a (by simp), sub_zero]
  rw [hminus, hplus] at hip
  rw [error_fourier_eq_interval a h hh ha p hp heven t]
  change (Complex.I * (t : ℂ)) * (∫ x in (-a)..a, k x * r x) =
    p (-a) * k (-a) - p a * k a + ∫ x in (-a)..a, deriv r x * k x
  linear_combination -hip

/-- The actual zero-extension error has integrable Fourier integrands at every
real angular frequency. The high-frequency bound pays both endpoint jumps.
The decay quotient is asserted only away from frequency zero. -/
theorem sameWindowSmoothTrial_fourier_error_bounds (a h M M1 : ℝ)
    (hh : 0 < h) (ha : 4 * h ≤ a) (hM : 0 ≤ M) (hM1 : 0 ≤ M1)
    (p : ℝ → ℂ) (hp : ContDiff ℝ ∞ p) (heven : ∀ x, p (-x) = p x)
    (hbound : ∀ x ∈ Icc (-a) a, ‖p x‖ ≤ M)
    (hbound1 : ∀ x ∈ Icc (-a) a, ‖deriv p x‖ ≤ M1) :
    Integrable (fun x : ℝ => (Ioo (-a) a).indicator p x -
      sameWindowSmoothTrial a h hh p hp heven x) ∧
    ∀ t : ℝ,
      Integrable (fun x : ℝ => fourierKernel (t : ℂ) x *
        ((Ioo (-a) a).indicator p x - sameWindowSmoothTrial a h hh p hp heven x)) ∧
      ‖∫ x : ℝ, fourierKernel (t : ℂ) x *
        ((Ioo (-a) a).indicator p x - sameWindowSmoothTrial a h hh p hp heven x)‖ ≤
        4 * M * h ∧
      (t ≠ 0 →
        ‖∫ x : ℝ, fourierKernel (t : ℂ) x *
          ((Ioo (-a) a).indicator p x - sameWindowSmoothTrial a h hh p hp heven x)‖ ≤
          (4 * M + 4 * h * M1) / |t|) := by
  let E : ℝ → ℂ := fun x => (Ioo (-a) a).indicator p x -
    sameWindowSmoothTrial a h hh p hp heven x
  let r : ℝ → ℂ := fun x => p x - sameWindowSmoothTrial a h hh p hp heven x
  have hei : Integrable E :=
    ((hp.continuous.integrableOn_Icc.mono_set Ioo_subset_Icc_self).integrable_indicator
      measurableSet_Ioo).sub (sameWindowSmoothTrial a h hh p hp heven).integrable
  refine ⟨hei, ?_⟩
  intro t
  let k : ℝ → ℂ := fourierKernel (t : ℂ)
  let F : ℂ := ∫ x : ℝ, k x * E x
  have hk : Continuous k := continuous_iff_continuousAt.mpr
    (fun x => (kernel_hasDerivAt t x).continuousAt)
  have hki : Integrable (fun x : ℝ => k x * E x) :=
    hei.bdd_mul hk.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => (kernel_norm t x).le))
  have hlow : ‖F‖ ≤ 4 * M * h := by
    calc
      _ ≤ ∫ x : ℝ, ‖k x * E x‖ := norm_integral_le_integral_norm _
      _ = ∫ x : ℝ, ‖E x‖ := by
        simp_rw [norm_mul, show ∀ x, ‖k x‖ = 1 from kernel_norm t, one_mul]
      _ ≤ 4 * M * h := sameWindowSmoothTrial_L1_error_le a h M hh ha hM p hp heven hbound
  refine ⟨hki, hlow, ?_⟩
  intro ht
  have hab : -a ≤ a := by linarith
  have hJ : ‖∫ x in (-a)..a, deriv r x * k x‖ ≤ 2 * M + 4 * h * M1 := by
    calc
      _ ≤ ∫ x in (-a)..a, ‖deriv r x * k x‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
      _ = ∫ x in Icc (-a) a, ‖deriv r x‖ := by
        simp_rw [norm_mul, show ∀ x, ‖k x‖ = 1 from kernel_norm t, mul_one]
        rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
      _ ≤ 2 * M + 4 * h * M1 :=
        sameWindowSmoothTrial_derivative_L1_error_le a h M M1 hh ha hM hM1
          p hp heven hbound hbound1
  have hboundary : ‖p (-a) * k (-a) - p a * k a‖ ≤ 2 * M := by
    calc
      _ ≤ ‖p (-a) * k (-a)‖ + ‖p a * k a‖ := norm_sub_le _ _
      _ = ‖p (-a)‖ + ‖p a‖ := by
        rw [norm_mul, norm_mul, show ‖k (-a)‖ = 1 from kernel_norm t (-a),
          show ‖k a‖ = 1 from kernel_norm t a, mul_one, mul_one]
      _ ≤ M + M := add_le_add (hbound (-a) ⟨le_rfl, hab⟩) (hbound a ⟨hab, le_rfl⟩)
      _ = 2 * M := by ring
  have hid : (Complex.I * (t : ℂ)) * F =
      p (-a) * k (-a) - p a * k a + ∫ x in (-a)..a, deriv r x * k x :=
    error_endpoint_identity a h hh ha p hp heven t
  have hhigh : |t| * ‖F‖ ≤ 4 * M + 4 * h * M1 := by
    calc
      _ = ‖(Complex.I * (t : ℂ)) * F‖ := by
        rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
          Real.norm_eq_abs, one_mul]
      _ = ‖p (-a) * k (-a) - p a * k a + ∫ x in (-a)..a, deriv r x * k x‖ :=
        congrArg norm hid
      _ ≤ ‖p (-a) * k (-a) - p a * k a‖ + ‖∫ x in (-a)..a, deriv r x * k x‖ :=
        norm_add_le _ _
      _ ≤ 2 * M + (2 * M + 4 * h * M1) := add_le_add hboundary hJ
      _ = 4 * M + 4 * h * M1 := by ring
  apply (le_div_iff₀ (abs_pos.mpr ht)).2
  simpa only [mul_comm] using hhigh

#print axioms sameWindowSmoothTrial_derivative_L1_error_le
#print axioms sameWindowSmoothTrial_fourier_error_bounds

end D5.S3.Weil.BurnolGram.SameWindowFourierDecay
