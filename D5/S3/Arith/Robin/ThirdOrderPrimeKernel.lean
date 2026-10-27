/- GID: D5/S3/Arith/Robin/ThirdOrderPrimeKernel
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ThirdOrderPrimeKernel
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Cubic price expansion bounds the actual-prime error on the full selected domain.

Purpose: a cubic-in-price approximation of the literal selected-Euler kernel,
with absolute centered actual-prime error at most 40 ell^(-1/10) M on the
UNCHANGED complete selectedDomain of OriginalFirstClockTransport.

The weight and the clocks below are the existing D5 objects. No alternative
maximizer, label window, edge selector, strict inventory, or clock is introduced.

The prime-mass hypothesis is an EXTERNAL analytic input, not a compiled D5
theorem. Provenance: Library/ArithSums/nicolas2025comparison.md, the uniform
Guth--Maynard Corollary 1.3 statement near lines 11849--11859, and the same
common-start / H=t^(4/5) admissibility argument at A11 near lines 12619--12623;
underlying source Library/Analytic/guthmaynard2024largevalues.md and
https://arxiv.org/html/2405.20552v2. Use y=t-1 and v=H+1. At one sufficiently
late common start, y^(7/12) <= v <= y^(99/100), the relative counting error
is small, log(t+H)/log(t-1) tends to 1, and (H+1)/H tends to 1. Thus the
log-weighted actual-clock mass is <= 3H, because q < tau_q < q+1.
This file retains that finite mass statement as a premise; it does not claim
to formalize Guth--Maynard or its eventual common-start specialization.
On selectedDomain the live exclusion proof below gives the stronger q>t;
GM on (t,t+H] itself therefore suffices for the stated active-clock mass.

Existing A13 already warns that the leading triangular baseline need not
have o(M) absolute error. This result makes no novelty claim for A13,
does not prove EL.14, and does not supply a kappa or a proof of RH.
-/

import D5.S3.Arith.Robin.OriginalFirstClockTransport
import D5.S3.Arith.Robin.LogLogHigherDerivative
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic

/-! Cubic price expansion on the unchanged complete original first-clock domain. -/

noncomputable section

namespace D5.S3.Arith.Robin.ThirdOrderPrimeKernel

open Set MeasureTheory
open scoped Topology
open D5.S3.Arith.Robin.ActualRobinClockCovariance
open D5.S3.Arith.Robin.OriginalFirstClockTransport
open D5.S3.Arith.Robin.LogLogHigherDerivative
open D5.S3.Arith.Robin.DelayedAtomTransport

open private original_curve first_clock_spec selected_domain_bounds domain_compact from
  D5.S3.Arith.Robin.OriginalFirstClockTransport
open private hasDerivAt_positiveKernel from D5.S3.Arith.Robin.LogLogHigherDerivative

/- The following are derivative expressions, not replacement weight producers. -/

private def densityD1 (t : ℝ) : ℝ :=
  -(2 * (Real.log t)^2 + 3 * Real.log t + 2) /
    (t^3 * (Real.log t)^3)

private def densityD2 (t : ℝ) : ℝ :=
  (6 * (Real.log t)^3 + 11 * (Real.log t)^2 + 12 * Real.log t + 6) /
    (t^4 * (Real.log t)^4)

private def densityD3 (t : ℝ) : ℝ :=
  -(24 * (Real.log t)^4 + 50 * (Real.log t)^3 +
    70 * (Real.log t)^2 + 60 * Real.log t + 24) /
      (t^5 * (Real.log t)^5)

private theorem density_eq_positiveKernel {t : ℝ} (ht : 1 < t) :
    activationDensity t = positiveKernel 1 0 0 t := by
  have ht0 : t ≠ 0 := ne_of_gt (by linarith)
  have hl0 : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  norm_num [activationDensity, positiveKernel]
  field_simp [ht0, hl0] <;> ring

private theorem densityD1_eq_negativeKernel {t : ℝ} (ht : 1 < t) :
    densityD1 t = -positiveKernel 2 0 0 t := by
  have ht0 : t ≠ 0 := ne_of_gt (by linarith)
  have hl0 : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  norm_num [densityD1, positiveKernel]
  field_simp [ht0, hl0] <;> ring

private theorem densityD2_eq_positiveKernel {t : ℝ} (ht : 1 < t) :
    densityD2 t = positiveKernel 3 0 0 t := by
  have ht0 : t ≠ 0 := ne_of_gt (by linarith)
  have hl0 : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  norm_num [densityD2, positiveKernel]
  field_simp [ht0, hl0] <;> ring

private theorem densityD3_eq_negativeKernel {t : ℝ} (ht : 1 < t) :
    densityD3 t = -positiveKernel 4 0 0 t := by
  have ht0 : t ≠ 0 := ne_of_gt (by linarith)
  have hl0 : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  norm_num [densityD3, positiveKernel]
  field_simp [ht0, hl0] <;> ring

/- Reuse the library's general derivative engine. The four identities above
   only expand its existing kernels into the concrete rational formulas. -/
private theorem activationDensity_hasDerivAt {t : ℝ} (ht : 1 < t) :
    HasDerivAt activationDensity (densityD1 t) t := by
  have he : activationDensity =ᶠ[𝓝 t] positiveKernel 1 0 0 :=
    by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
      exact density_eq_positiveKernel hx
  exact ((hasDerivAt_positiveKernel 1 0 0 ht).congr_of_eventuallyEq he).congr_deriv
    (densityD1_eq_negativeKernel ht).symm

private theorem densityD1_hasDerivAt {t : ℝ} (ht : 1 < t) :
    HasDerivAt densityD1 (densityD2 t) t := by
  have he : densityD1 =ᶠ[𝓝 t] (fun x => -positiveKernel 2 0 0 x) :=
    by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
      exact densityD1_eq_negativeKernel hx
  have h := ((hasDerivAt_positiveKernel 2 0 0 ht).neg).congr_of_eventuallyEq he
  simpa only [neg_neg, ← densityD2_eq_positiveKernel ht] using h

private theorem densityD2_hasDerivAt {t : ℝ} (ht : 1 < t) :
    HasDerivAt densityD2 (densityD3 t) t := by
  have he : densityD2 =ᶠ[𝓝 t] positiveKernel 3 0 0 :=
    by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
      exact densityD2_eq_positiveKernel hx
  exact ((hasDerivAt_positiveKernel 3 0 0 ht).congr_of_eventuallyEq he).congr_deriv
    (densityD3_eq_negativeKernel ht).symm

private theorem densityD3_local_bound {t : ℝ} (ht : 3 ≤ t) :
    0 ≤ -densityD3 t ∧
      -densityD3 t ≤ 228 * activationDensity t / t^3 := by
  have ht0 : 0 < t := by linarith
  have hl : 1 ≤ Real.log t := by
    exact (Real.lt_log_iff_exp_lt ht0).mpr
      (Real.exp_one_lt_three.trans_le ht) |>.le
  have hl0 : 0 < Real.log t := by linarith
  have h12 : Real.log t ≤ (Real.log t)^2 := by nlinarith
  have h23 : (Real.log t)^2 ≤ (Real.log t)^3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hl) (sq_nonneg (Real.log t))]
  have h34 : (Real.log t)^3 ≤ (Real.log t)^4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hl) (pow_nonneg hl0.le 3)]
  have h14 : 1 ≤ (Real.log t)^4 := by linarith
  have hid : (228 * activationDensity t / t^3) *
      (t^5 * (Real.log t)^5) =
      228 * ((Real.log t)^4 + (Real.log t)^3) := by
    dsimp [activationDensity]
    field_simp [ht0.ne', hl0.ne'] <;> ring
  constructor
  · dsimp [densityD3]
    rw [neg_div, neg_neg]
    positivity
  · dsimp [densityD3]
    rw [neg_div, neg_neg]
    apply (div_le_iff₀ (by positivity : 0 < t^5 * (Real.log t)^5)).mpr
    rw [hid]
    nlinarith

private theorem densityD3_forward_bound {t s : ℝ} (ht : 3 ≤ t) (hts : t ≤ s) :
    0 ≤ -densityD3 s ∧
      -densityD3 s ≤ 228 * activationDensity t / t^3 := by
  have ht1 : 1 < t := by linarith
  have hs1 : 1 < s := ht1.trans_le hts
  have ht0 : 0 < t := by linarith
  have hs0 : 0 < s := ht0.trans_le hts
  have hb := densityD3_local_bound (ht.trans hts)
  have hw := original_curve.antitone_weight ht1 hs1 hts
  have hwt := original_curve.positive_weight t ht1
  refine ⟨hb.1, hb.2.trans ?_⟩
  calc
    228 * activationDensity s / s^3 ≤ 228 * activationDensity t / s^3 := by
      exact div_le_div_of_nonneg_right (by linarith) (pow_nonneg hs0.le 3)
    _ ≤ 228 * activationDensity t / t^3 := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ ht0.le hts 3)

/- A derivative comparison, used three times below. It supplies the actual
   factorial constants rather than assuming a Taylor-remainder hypothesis. -/
private theorem nonneg_of_deriv_nonneg {F F' : ℝ → ℝ} {H : ℝ}
    (hH : 0 ≤ H) (hF : ∀ v ∈ Icc 0 H, HasDerivAt F (F' v) v)
    (hzero : F 0 = 0) (hpos : ∀ v ∈ Icc 0 H, 0 ≤ F' v) :
    ∀ v ∈ Icc 0 H, 0 ≤ F v := by
  have hm : MonotoneOn F (Icc 0 H) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 H)
      (fun v hv => (hF v hv).continuousAt.continuousWithinAt) ?_ ?_
    · intro v hv
      exact (hF v (interior_subset hv)).differentiableAt.differentiableWithinAt
    · intro v hv
      rw [(hF v (interior_subset hv)).deriv]
      exact hpos v (interior_subset hv)
  intro v hv
  simpa [hzero] using hm (left_mem_Icc.mpr hH) hv hv.1

private def densityQuadratic (t v : ℝ) : ℝ :=
  activationDensity t + densityD1 t * v + densityD2 t * v^2 / 2

private theorem density_quadratic_error {t H v : ℝ} (ht : 3 ≤ t) (hH : 0 ≤ H)
    (hv : v ∈ Icc 0 H) :
    0 ≤ densityQuadratic t v - activationDensity (t+v) ∧
      densityQuadratic t v - activationDensity (t+v) ≤
        (228 * activationDensity t / t^3) * v^3 / 6 := by
  let C : ℝ := 228 * activationDensity t / t^3
  let E₂ : ℝ → ℝ := fun u => densityD2 t - densityD2 (t+u)
  let E₁ : ℝ → ℝ := fun u => densityD1 t + densityD2 t*u - densityD1 (t+u)
  let E₀ : ℝ → ℝ := fun u => densityQuadratic t u - activationDensity (t+u)
  have ht1 : 1 < t := by linarith
  have hu1 (u : ℝ) (hu : u ∈ Icc 0 H) : 1 < t+u := by linarith [hu.1]
  have hC (u : ℝ) (hu : u ∈ Icc 0 H) :
      0 ≤ -densityD3 (t+u) ∧ -densityD3 (t+u) ≤ C :=
    densityD3_forward_bound ht (by linarith [hu.1])
  have hE₂ (u : ℝ) (hu : u ∈ Icc 0 H) :
      HasDerivAt E₂ (-densityD3 (t+u)) u := by
    simpa [E₂] using (densityD2_hasDerivAt (hu1 u hu)).comp u
      ((hasDerivAt_id u).const_add t) |>.const_sub (densityD2 t)
  have hE₁ (u : ℝ) (hu : u ∈ Icc 0 H) : HasDerivAt E₁ (E₂ u) u := by
    convert (((hasDerivAt_id u).const_mul (densityD2 t)).const_add (densityD1 t)).sub
      ((densityD1_hasDerivAt (hu1 u hu)).comp u
        ((hasDerivAt_id u).const_add t)) using 1 <;> (try funext x) <;> dsimp [E₁, E₂] <;> ring
  have hE₀ (u : ℝ) (hu : u ∈ Icc 0 H) : HasDerivAt E₀ (E₁ u) u := by
    convert ((((hasDerivAt_id u).const_mul (densityD1 t)).const_add
      (activationDensity t)).add
        (((hasDerivAt_id u).pow 2).const_mul (densityD2 t) |>.div_const 2)).sub
      ((activationDensity_hasDerivAt (hu1 u hu)).comp u
        ((hasDerivAt_id u).const_add t)) using 1 <;> (try funext x) <;>
      dsimp [E₀, E₁, densityQuadratic] <;> ring
  have h₂lo : ∀ u ∈ Icc 0 H, 0 ≤ E₂ u :=
    nonneg_of_deriv_nonneg hH hE₂ (by simp [E₂]) (fun u hu => (hC u hu).1)
  have h₂hi : ∀ u ∈ Icc 0 H, E₂ u ≤ C*u := by
    have hh := nonneg_of_deriv_nonneg hH
      (F := fun u => C*u-E₂ u) (F' := fun u => C+ densityD3 (t+u))
      (fun u hu => by
        convert ((hasDerivAt_id u).const_mul C).sub (hE₂ u hu) using 1 <;> (try funext x) <;> (try dsimp [id, Function.comp_def]) <;> ring)
      (by simp [E₂]) (fun u hu => by linarith [(hC u hu).2])
    intro u hu
    linarith [hh u hu]
  have h₁lo : ∀ u ∈ Icc 0 H, 0 ≤ E₁ u :=
    nonneg_of_deriv_nonneg hH hE₁ (by simp [E₁]) h₂lo
  have h₁hi : ∀ u ∈ Icc 0 H, E₁ u ≤ C*u^2/2 := by
    have hh := nonneg_of_deriv_nonneg hH
      (F := fun u => C*u^2/2-E₁ u) (F' := fun u => C*u-E₂ u)
      (fun u hu => by
        convert ((((hasDerivAt_id u).pow 2).const_mul C).div_const 2).sub
          (hE₁ u hu) using 1 <;> (try funext x) <;> (try dsimp [id, Function.comp_def]) <;> ring)
      (by simp [E₁]) (fun u hu => by linarith [h₂hi u hu])
    intro u hu
    linarith [hh u hu]
  have h₀lo : ∀ u ∈ Icc 0 H, 0 ≤ E₀ u :=
    nonneg_of_deriv_nonneg hH hE₀ (by simp [E₀, densityQuadratic]) h₁lo
  have h₀hi : ∀ u ∈ Icc 0 H, E₀ u ≤ C*u^3/6 := by
    have hh := nonneg_of_deriv_nonneg hH
      (F := fun u => C*u^3/6-E₀ u) (F' := fun u => C*u^2/2-E₁ u)
      (fun u hu => by
        convert ((((hasDerivAt_id u).pow 3).const_mul C).div_const 6).sub
          (hE₀ u hu) using 1 <;> (try funext x) <;> (try dsimp [id, Function.comp_def]) <;> ring)
      (by simp [E₀, densityQuadratic]) (fun u hu => by linarith [h₁hi u hu])
    intro u hu
    linarith [hh u hu]
  exact ⟨h₀lo v hv, h₀hi v hv⟩

/- Offset kernels are used inside the literal half-open support, never on an
   enlarged/trimmed selectedDomain. P3 is cubic in lambda and quadratic in w. -/
private def kernelOffset (t H d u : ℝ) : ℝ :=
  (g (t+u) - g (t+H)) / (activationDensity t * d)

private def cubicOffset (t H d u : ℝ) : ℝ :=
  ((H-u) + densityD1 t / (2 * activationDensity t) * (H^2-u^2) +
    densityD2 t / (6 * activationDensity t) * (H^3-u^3)) / d

private theorem integral_densityQuadratic (t a b : ℝ) :
    (∫ v in a..b, densityQuadratic t v) =
      activationDensity t*(b-a) + densityD1 t*(b^2-a^2)/2 +
        densityD2 t*(b^3-a^3)/6 := by
  let F : ℝ → ℝ := fun v => activationDensity t*v +
    densityD1 t*v^2/2 + densityD2 t*v^3/6
  have hd (v : ℝ) : HasDerivAt F (densityQuadratic t v) v := by
    convert (((hasDerivAt_id v).const_mul (activationDensity t)).add
      ((((hasDerivAt_id v).pow 2).const_mul (densityD1 t)).div_const 2)).add
        ((((hasDerivAt_id v).pow 3).const_mul (densityD2 t)).div_const 6) using 1 <;> (try funext x) <;>
      dsimp [F, densityQuadratic] <;> ring
  have hi : IntervalIntegrable (densityQuadratic t) volume a b :=
    (show Continuous (densityQuadratic t) by unfold densityQuadratic; fun_prop).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v) hi]
  dsimp [F]
  ring

private theorem integral_density_shift {t a b : ℝ} (hta : 1 < t+a) (hab : a ≤ b) :
    (∫ v in a..b, activationDensity (t+v)) = g (t+a)-g (t+b) := by
  have hd (v : ℝ) (hv : v ∈ uIcc a b) :
      HasDerivAt (fun u => -g (t+u)) (activationDensity (t+v)) v := by
    rw [uIcc_of_le hab] at hv
    have hv1 : 1 < t+v := by linarith [hv.1]
    convert ((g_has_deriv_at hv1).comp v ((hasDerivAt_id v).const_add t)).neg using 1 <;>
      (try funext x) <;> simp
  have hi : IntervalIntegrable (fun v => activationDensity (t+v)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro v hv
    rw [uIcc_of_le hab] at hv
    have hv1 : 1 < t+v := by linarith [hv.1]
    exact ((activationDensity_hasDerivAt hv1).continuousAt.comp
      (continuousAt_const.add continuousAt_id)).continuousWithinAt
  calc
    _ = (-g (t+b)) - (-g (t+a)) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := a) (b := b) (f := fun u : ℝ => -g (t+u))
        (f' := fun u : ℝ => activationDensity (t+u)) hd hi
    _ = _ := by ring

private theorem cubic_kernel_error {t H d u : ℝ} (ht : 3 ≤ t) (hH : 0 ≤ H)
    (hd : 0 < d) (hu : u ∈ Icc 0 H) :
    0 ≤ cubicOffset t H d u - kernelOffset t H d u ∧
      cubicOffset t H d u - kernelOffset t H d u ≤
        (228 / 24 : ℝ) * (H^4-u^4) / (t^3*d) := by
  have ht1 : 1 < t := by linarith
  have hw := original_curve.positive_weight t ht1
  let E : ℝ → ℝ := fun v => densityQuadratic t v - activationDensity (t+v)
  let C : ℝ := 228 * activationDensity t / t^3
  have hE (v : ℝ) (hv : v ∈ Icc u H) : 0 ≤ E v ∧ E v ≤ C*v^3/6 :=
    density_quadratic_error ht hH ⟨hu.1.trans hv.1, hv.2⟩
  have hi : IntervalIntegrable E volume u H := by
    apply ContinuousOn.intervalIntegrable
    intro v hv
    rw [uIcc_of_le hu.2] at hv
    have hv1 : 1 < t+v := by linarith [hu.1, hv.1]
    exact ((show Continuous (densityQuadratic t) by unfold densityQuadratic; fun_prop).continuousAt.sub
      ((activationDensity_hasDerivAt hv1).continuousAt.comp
        (continuousAt_const.add continuousAt_id))).continuousWithinAt
  have hpoly : IntervalIntegrable (fun v : ℝ => C*v^3/6) volume u H :=
    (by fun_prop : Continuous (fun v : ℝ => C*v^3/6)).intervalIntegrable _ _
  have hilo : 0 ≤ ∫ v in u..H, E v :=
    intervalIntegral.integral_nonneg hu.2 (fun v hv => (hE v hv).1)
  have hihi := intervalIntegral.integral_mono_on hu.2 hi hpoly
    (fun v hv => (hE v hv).2)
  have hipoly : (∫ v in u..H, C*v^3/6) = C*(H^4-u^4)/24 := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    ring
  have heq : cubicOffset t H d u - kernelOffset t H d u =
      (∫ v in u..H, E v) / (activationDensity t*d) := by
    have hiQ : IntervalIntegrable (densityQuadratic t) volume u H :=
      (show Continuous (densityQuadratic t) by unfold densityQuadratic; fun_prop).intervalIntegrable _ _
    have hiW : IntervalIntegrable (fun v => activationDensity (t+v)) volume u H :=
      (hiQ.sub hi).congr (fun v _ => by dsimp [E]; ring)
    rw [show E = (fun v => densityQuadratic t v - activationDensity (t+v)) from rfl,
      intervalIntegral.integral_sub hiQ hiW, integral_densityQuadratic,
      integral_density_shift (by linarith [hu.1]) hu.2]
    dsimp [cubicOffset, kernelOffset]
    field_simp [hw.ne', hd.ne'] <;> ring
  rw [heq]
  refine ⟨div_nonneg hilo (mul_pos hw hd).le, ?_⟩
  calc
    (∫ v in u..H, E v) / (activationDensity t*d) ≤
        (C*(H^4-u^4)/24) / (activationDensity t*d) := by
      exact div_le_div_of_nonneg_right (hihi.trans_eq hipoly) (mul_pos hw hd).le
    _ = (228 / 24 : ℝ) * (H^4-u^4) / (t^3*d) := by
      dsimp [C]
      field_simp [hw.ne', hd.ne', (by linarith : t ≠ 0)] <;> ring

private theorem cubic_kernel_uniform_error {t H d u : ℝ} (ht : 3 ≤ t) (hH : 0 ≤ H)
    (hd : 0 < d) (hu : u ∈ Icc 0 H) :
    |kernelOffset t H d u - cubicOffset t H d u| ≤
      (19 / 2 : ℝ) * H^4 / (t^3*d) := by
  have ht0 : 0 < t := by linarith
  have he := cubic_kernel_error ht hH hd hu
  rw [abs_sub_comm, abs_of_nonneg he.1]
  refine he.2.trans ?_
  have hden : 0 < t^3*d := by positivity
  apply (div_le_div_iff_of_pos_right hden).mpr
  nlinarith [pow_nonneg hu.1 4]

private def continuumExact (t H d : ℝ) : ℝ := ∫ u in 0..H, kernelOffset t H d u

private def continuumCubic (t H d : ℝ) : ℝ := ∫ u in 0..H, cubicOffset t H d u

private def cubicCenter (t H d : ℝ) : ℝ :=
  H^2/(2*d) + densityD1 t*H^3/(3*activationDensity t*d) +
    densityD2 t*H^4/(8*activationDensity t*d)

private theorem cubic_continuum_error {t H d : ℝ} (ht : 3 ≤ t) (hH : 0 ≤ H)
    (hd : 0 < d) :
    |continuumExact t H d - continuumCubic t H d| ≤
      (38 / 5 : ℝ) * H^5 / (t^3*d) := by
  let B : ℝ → ℝ := fun u => (228 / 24 : ℝ) * (H^4-u^4) / (t^3*d)
  have hpoint (u : ℝ) (hu : u ∈ Ioc 0 H) :
      ‖kernelOffset t H d u-cubicOffset t H d u‖ ≤ B u := by
    have he := cubic_kernel_error ht hH hd ⟨hu.1.le, hu.2⟩
    rw [Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg he.1]
    exact he.2
  have hiB : IntervalIntegrable B volume 0 H :=
    (by dsimp [B]; fun_prop : Continuous B).intervalIntegrable _ _
  have hib : (∫ u in 0..H, B u) = (38 / 5 : ℝ) * H^5 / (t^3*d) := by
    have hi4 : IntervalIntegrable (fun u : ℝ => u^4) volume 0 H :=
      (show Continuous (fun u : ℝ => u^4) by fun_prop).intervalIntegrable _ _
    rw [show B = (fun u => ((228 / 24 : ℝ)/(t^3*d)) * (H^4-u^4)) by
      funext u; dsimp [B]; ring,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub intervalIntegrable_const
        hi4,
      intervalIntegral.integral_const, integral_pow]
    norm_num
    ring
  have hiK : IntervalIntegrable (kernelOffset t H d) volume 0 H := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    rw [uIcc_of_le hH] at hu
    have hu1 : 1 < t+u := by linarith [hu.1]
    exact (((g_has_deriv_at hu1).continuousAt.comp
      (continuousAt_const.add continuousAt_id)).sub continuousAt_const |>.div_const
      (activationDensity t*d)).continuousWithinAt
  have hiP : IntervalIntegrable (cubicOffset t H d) volume 0 H :=
    (by unfold cubicOffset; fun_prop : Continuous (cubicOffset t H d)).intervalIntegrable _ _
  unfold continuumExact continuumCubic
  rw [← intervalIntegral.integral_sub hiK hiP]
  simpa only [Real.norm_eq_abs, hib] using
    intervalIntegral.norm_integral_le_of_norm_le hH (Filter.Eventually.of_forall hpoint) hiB

private theorem continuumCubic_closed_form (t H d : ℝ) :
    continuumCubic t H d = cubicCenter t H d := by
  let F : ℝ → ℝ := fun u =>
    (H*u-u^2/2 + densityD1 t/(2*activationDensity t)*(H^2*u-u^3/3) +
      densityD2 t/(6*activationDensity t)*(H^3*u-u^4/4))/d
  have hF (u : ℝ) : HasDerivAt F (cubicOffset t H d u) u := by
    convert (((((hasDerivAt_id u).const_mul H).sub
      (((hasDerivAt_id u).pow 2).div_const 2)).add
      ((((hasDerivAt_id u).const_mul (H^2)).sub
        (((hasDerivAt_id u).pow 3).div_const 3)).const_mul
          (densityD1 t/(2*activationDensity t)))).add
      ((((hasDerivAt_id u).const_mul (H^3)).sub
        (((hasDerivAt_id u).pow 4).div_const 4)).const_mul
          (densityD2 t/(6*activationDensity t)))).div_const d using 1 <;> (try funext x) <;>
      dsimp [F, cubicOffset] <;> ring
  unfold continuumCubic
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hF u)
    ((by unfold cubicOffset; fun_prop : Continuous (cubicOffset t H d)).intervalIntegrable _ _)]
  dsimp [F, cubicCenter]
  ring

def actualPrimes (R t H : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊2*R⌋₊).filter (fun q => t < firstClock q ∧ firstClock q ≤ t+H)

/- The actual kernel starts with <=. It can be replaced by < only after
   consuming the existing closed first-pulse exclusion on this SAME S_X. -/
private theorem selected_firstClock_initial (X : OriginalWindow) {ell R t : ℝ}
    (hell : 243 ≤ ell) (hbounds : OriginalBounds X ell R)
    (ht : t ∈ selectedDomain X) {q : ℕ} (hq : q.Prime) :
    (t ≤ firstClock q ↔ t < firstClock q) ∧
      (t < firstClock q → t < (q : ℝ)) := by
  have hex := complete_original_first_clock_exclusion X hell hbounds q hq
  have hnot : t ∉ Icc (q : ℝ) (firstClock q) :=
    fun hc => Set.disjoint_left.mp hex ht hc
  have hne : t ≠ firstClock q := by
    intro he
    apply hnot
    rw [he]
    exact ⟨(first_clock_spec hq).1.le, le_rfl⟩
  refine ⟨⟨fun h => lt_of_le_of_ne h hne, le_of_lt⟩, ?_⟩
  intro hclock
  by_contra hqbound
  exact hnot ⟨le_of_not_gt hqbound, hclock.le⟩

private def actualPrimeResponse (R t H d : ℝ) : ℝ :=
  (∑ q ∈ actualPrimes R t H, Real.log q *
    kernelOffset t H d (firstClock q-t)) - continuumExact t H d

def canonicalActualPrimeResponse (R t H d : ℝ) : ℝ :=
  (∑ q ∈ Nat.primesLE ⌊2*R⌋₊, Real.log q *
    actualKernel g t (t+H) (activationDensity t*d) (firstClock q)) -
      continuumExact t H d

private theorem canonical_actual_response_eq
    (X : OriginalWindow) {ell R t H d : ℝ}
    (hell : 243 ≤ ell) (hbounds : OriginalBounds X ell R)
    (ht : t ∈ selectedDomain X) :
    canonicalActualPrimeResponse R t H d = actualPrimeResponse R t H d := by
  unfold canonicalActualPrimeResponse actualPrimeResponse actualPrimes
  rw [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  have hleft := (selected_firstClock_initial X hell hbounds ht
    (Nat.mem_primesLE.mp hq).2).1
  by_cases hc : t < firstClock q ∧ firstClock q ≤ t+H
  · simp [actualKernel, hleft, hc, kernelOffset,
      show t+(firstClock q-t) = firstClock q by ring]
  · simp [actualKernel, hleft, hc]

def cubicPrimeResponse (R t H d : ℝ) : ℝ :=
  (∑ q ∈ actualPrimes R t H, Real.log q *
    cubicOffset t H d (firstClock q-t)) - cubicCenter t H d

private theorem actual_prime_centered_error {R t H d : ℝ} (ht : 3 ≤ t) (hH : 0 ≤ H)
    (hd : 0 < d)
    (hGMmass : (∑ q ∈ actualPrimes R t H, Real.log q) ≤ 3 * H) :
    |actualPrimeResponse R t H d - cubicPrimeResponse R t H d| ≤
      40 * H^5 / (t^3*d) := by
  have ht0 : 0 < t := by linarith
  let A : ℝ := (19 / 2 : ℝ)*H^4/(t^3*d)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hsum : |∑ q ∈ actualPrimes R t H, Real.log q *
      (kernelOffset t H d (firstClock q-t)-cubicOffset t H d (firstClock q-t))| ≤
        (57 / 2 : ℝ)*H^5/(t^3*d) := by
    calc
      _ ≤ ∑ q ∈ actualPrimes R t H, |Real.log q *
          (kernelOffset t H d (firstClock q-t)-cubicOffset t H d (firstClock q-t))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ q ∈ actualPrimes R t H, Real.log q*A := by
        apply Finset.sum_le_sum
        intro q hq
        have hc := (Finset.mem_filter.mp hq).2
        have hu : firstClock q-t ∈ Icc 0 H := ⟨by linarith [hc.1], by linarith [hc.2]⟩
        rw [abs_mul, abs_of_nonneg (Real.log_natCast_nonneg q)]
        exact mul_le_mul_of_nonneg_left (cubic_kernel_uniform_error ht hH hd hu)
          (Real.log_natCast_nonneg q)
      _ = (∑ q ∈ actualPrimes R t H, Real.log q)*A := by rw [Finset.sum_mul]
      _ ≤ (3*H)*A := mul_le_mul_of_nonneg_right hGMmass hA
      _ = (57 / 2 : ℝ)*H^5/(t^3*d) := by dsimp [A]; ring
  have hcont := cubic_continuum_error ht hH hd
  rw [continuumCubic_closed_form] at hcont
  have heq : actualPrimeResponse R t H d - cubicPrimeResponse R t H d =
      (∑ q ∈ actualPrimes R t H, Real.log q *
        (kernelOffset t H d (firstClock q-t)-cubicOffset t H d (firstClock q-t))) -
      (continuumExact t H d-cubicCenter t H d) := by
    unfold actualPrimeResponse cubicPrimeResponse
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    ring
  rw [heq]
  calc
    _ ≤ |∑ q ∈ actualPrimes R t H, Real.log q *
        (kernelOffset t H d (firstClock q-t)-cubicOffset t H d (firstClock q-t))| +
        |continuumExact t H d-cubicCenter t H d| := abs_sub _ _
    _ ≤ (57 / 2 : ℝ)*H^5/(t^3*d) + (38 / 5 : ℝ)*H^5/(t^3*d) := add_le_add hsum hcont
    _ ≤ 40*H^5/(t^3*d) := by
      have hn : 0 ≤ H^5/(t^3*d) := by positivity
      simpa only [add_mul, mul_div_assoc] using
        mul_le_mul_of_nonneg_right (show (57 / 2 : ℝ) + 38 / 5 ≤ 40 by norm_num) hn

def windowLength (t : ℝ) : ℝ := t ^ (4 / 5 : ℝ)
def normalization (t : ℝ) : ℝ := t ^ (11 / 10 : ℝ)

private theorem cubic_scale_identity {t : ℝ} (ht : 0 < t) :
    (windowLength t)^5 / (t^3 * normalization t) = t ^ (-1 / 10 : ℝ) := by
  have hnum : (windowLength t)^5 = t ^ (4 : ℝ) := by
    dsimp [windowLength]
    rw [← Real.rpow_natCast (t ^ (4 / 5 : ℝ)) 5, ← Real.rpow_mul ht.le]
    norm_num
  have hden : t^3 * normalization t = t ^ (41 / 10 : ℝ) := by
    dsimp [normalization]
    rw [← Real.rpow_natCast t 3, ← Real.rpow_add ht]
    norm_num
  rw [hnum, hden, ← Real.rpow_sub ht]
  norm_num

private theorem actual_prime_scaled_error {R t : ℝ} (ht : 3 ≤ t)
    (hGMmass : (∑ q ∈ actualPrimes R t (windowLength t), Real.log q) ≤
      3 * windowLength t) :
    |actualPrimeResponse R t (windowLength t) (normalization t) -
      cubicPrimeResponse R t (windowLength t) (normalization t)| ≤
        40 * t ^ (-1 / 10 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have h := actual_prime_centered_error (R := R) (t := t)
    (H := windowLength t) (d := normalization t) ht
    (Real.rpow_nonneg ht0.le _) (Real.rpow_pos_of_pos ht0 _) hGMmass
  simpa only [mul_div_assoc, cubic_scale_identity ht0] using h

/- The two response integrals are over the SAME complete selectedDomain X.
   The ordinary response-integrability hypotheses are explicit; no analytic
   response estimate is hidden in them. No component count or R/ell enters. -/
theorem complete_selected_actual_prime_error
    (X : OriginalWindow) {ell R : ℝ} (hell : 243 ≤ ell)
    (hbounds : OriginalBounds X ell R)
    (hGMmass : ∀ t ∈ selectedDomain X,
      (∑ q ∈ actualPrimes R t (windowLength t), Real.log q) ≤ 3 * windowLength t)
    (hactual : IntegrableOn (fun t =>
      canonicalActualPrimeResponse R t (windowLength t) (normalization t)) (selectedDomain X))
    (hcubic : IntegrableOn (fun t =>
      cubicPrimeResponse R t (windowLength t) (normalization t)) (selectedDomain X)) :
    |(∫ t in selectedDomain X,
        canonicalActualPrimeResponse R t (windowLength t) (normalization t)) -
      (∫ t in selectedDomain X,
        cubicPrimeResponse R t (windowLength t) (normalization t))| ≤
      40 * ell ^ (-1 / 10 : ℝ) * volume.real (selectedDomain X) := by
  have hsub := selected_domain_bounds X hbounds
  have hmeas : MeasurableSet (selectedDomain X) := (domain_compact X).measurableSet
  have hfinite : volume (selectedDomain X) ≠ ⊤ :=
    (domain_compact X).measure_lt_top.ne
  let : IsFiniteMeasure (volume.restrict (selectedDomain X)) :=
    ⟨by simpa using lt_top_iff_ne_top.mpr hfinite⟩
  have hpoint : ∀ t ∈ selectedDomain X,
      ‖canonicalActualPrimeResponse R t (windowLength t) (normalization t) -
        cubicPrimeResponse R t (windowLength t) (normalization t)‖ ≤
          40 * ell ^ (-1 / 10 : ℝ) := by
    intro t ht
    have hbt := hsub ht
    have ht3 : 3 ≤ t := by linarith [hbt.1]
    have hs := actual_prime_scaled_error ht3 (hGMmass t ht)
    have hpow : t ^ (-1 / 10 : ℝ) ≤ ell ^ (-1 / 10 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hbt.1 (by norm_num)
    rw [canonical_actual_response_eq X hell hbounds ht]
    simpa only [Real.norm_eq_abs] using hs.trans (mul_le_mul_of_nonneg_left hpow (by norm_num))
  rw [← integral_sub hactual hcubic]
  have hn := MeasureTheory.norm_integral_le_of_norm_le_const
    (μ := volume.restrict (selectedDomain X))
    ((ae_restrict_iff' hmeas).mpr (Filter.Eventually.of_forall hpoint))
  simpa only [Real.norm_eq_abs, measureReal_restrict_apply_univ, mul_assoc] using hn

#print axioms complete_selected_actual_prime_error

end D5.S3.Arith.Robin.ThirdOrderPrimeKernel
