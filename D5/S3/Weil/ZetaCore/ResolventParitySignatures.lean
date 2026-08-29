/- GID: D5/S3/Weil/ZetaCore/ResolventParitySignatures
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaCore/ResolventParitySignatures
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Local resolvent differences are hyperbolic, with opposite even and odd channel signs. -/

import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Resolvent parity signatures

The first theorem constructs the two source correlations directly from spectral
measures. Shared local Green data makes their difference solve the homogeneous
second-order equation, and evenness fixes the solution to its hyperbolic cosine
mode.

The second theorem constructs the involution, convolution, and two Laplace
boundary channels directly on smooth compactly supported functions. Mathlib's
`integral_convolution` gives the two exponential identities; averaging them
cancels the cross terms and exposes the opposite even and odd signs.

Library-search audit trail (2026-08-29):
* D5 searches for local resolvent differences, hyperbolic correlation signatures,
  parity budget intervals, and generalized Rayleigh budget bounds found no exact
  frozen owner.
* Pinned Mathlib supplies `integral_convolution`, `integral_neg_eq_self`, the
  exponential and hyperbolic derivative rules, and constancy on an open interval
  from a zero derivative; these constituents are applied below.
* Pinned Mathlib has no bilateral Laplace-transform theorem or local
  constant-coefficient second-order uniqueness theorem matching either public
  statement.
-/

open MeasureTheory Set
open scoped ComplexConjugate Convolution

noncomputable section

namespace D5.S3.Weil.ZetaCore.ResolventParitySignatures

private theorem even_ode_solution_eq_cosh
    (L a : ℝ) (h d : ℝ → ℝ) (hL : 0 < L)
    (hFirst : ∀ x ∈ Ioo (-2 * L) (2 * L), HasDerivAt h (d x) x)
    (hSecond : ∀ x ∈ Ioo (-2 * L) (2 * L),
      HasDerivAt d (a ^ 2 * h x) x)
    (hEven : ∀ x, h (-x) = h x) :
    ∀ x ∈ Ioo (-2 * L) (2 * L), h x = h 0 * Real.cosh (a * x) := by
  let interval : Set ℝ := Ioo (-2 * L) (2 * L)
  have hZero : (0 : ℝ) ∈ interval := by
    change -2 * L < 0 ∧ 0 < 2 * L
    constructor <;> linarith
  have hDerivativeZero : d 0 = 0 := by
    have hReflected : HasDerivAt (fun x : ℝ => h (-x)) (-d 0) 0 := by
      have hOuter : HasDerivAt h (d (-(0 : ℝ))) (-(0 : ℝ)) :=
        hFirst (-(0 : ℝ)) (by simpa [interval] using hZero)
      have hComp := hOuter.comp 0 (hasDerivAt_neg 0)
      change HasDerivAt (fun x : ℝ => h (-x)) (d (-0) * (-1)) 0 at hComp
      simpa using hComp
    have hSame : (fun x : ℝ => h (-x)) = h := by
      funext x
      exact hEven x
    rw [hSame] at hReflected
    have hUnique := hReflected.unique (hFirst 0 hZero)
    linarith
  let conserved : ℝ → ℝ := fun x => Real.exp (-a * x) * (d x + a * h x)
  have hConservedDeriv (x : ℝ) (hx : x ∈ interval) :
      HasDerivAt conserved 0 x := by
    have hExp : HasDerivAt (fun y : ℝ => Real.exp (-a * y))
        (-a * Real.exp (-a * x)) x := by
      have hRaw : HasDerivAt (fun y : ℝ => Real.exp (-a * y))
          (Real.exp (-a * x) * (-a)) x := by
        simpa [id] using ((hasDerivAt_id x).const_mul (-a)).exp
      exact hRaw.congr_deriv (by ring)
    have hSum : HasDerivAt (fun y : ℝ => d y + a * h y)
        (a ^ 2 * h x + a * d x) x := by
      have hScaled : HasDerivAt (fun y : ℝ => a * h y) (a * d x) x := by
        simpa [id] using (hFirst x hx).const_mul a
      have hRaw := (hSecond x hx).add hScaled
      change HasDerivAt (fun y : ℝ => d y + a * h y)
        (a ^ 2 * h x + a * d x) x at hRaw
      exact hRaw
    change HasDerivAt (fun y : ℝ =>
      Real.exp (-a * y) * (d y + a * h y)) 0 x
    exact (hExp.mul hSum).congr_deriv (by ring_nf)
  have hConservedConstant :
      ∀ x ∈ interval, conserved x = conserved 0 := by
    have hDifferentiable : DifferentiableOn ℝ conserved interval := by
      intro x hx
      exact (hConservedDeriv x hx).differentiableAt.differentiableWithinAt
    have hDerivZero : interval.EqOn (deriv conserved) 0 := by
      intro x hx
      exact (hConservedDeriv x hx).deriv
    intro x hx
    exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      hDifferentiable hDerivZero hx hZero
  have hFirstOrder (x : ℝ) (hx : x ∈ interval) :
      d x + a * h x = a * h 0 * Real.exp (a * x) := by
    have hConstant := hConservedConstant x hx
    have hAtZero : conserved 0 = a * h 0 := by
      simp [conserved, hDerivativeZero]
    rw [hAtZero] at hConstant
    have hExpCancel : Real.exp (a * x) * Real.exp (-a * x) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 1
      ring_nf
    calc
      d x + a * h x = 1 * (d x + a * h x) := by ring
      _ = (Real.exp (a * x) * Real.exp (-a * x)) *
          (d x + a * h x) := by rw [hExpCancel]
      _ = Real.exp (a * x) * conserved x := by
        dsimp only [conserved]
        ring
      _ = Real.exp (a * x) * (a * h 0) := by rw [hConstant]
      _ = a * h 0 * Real.exp (a * x) := by ring
  let target : ℝ → ℝ := fun x => h 0 * Real.cosh (a * x)
  have hTargetDeriv (x : ℝ) :
      HasDerivAt target (h 0 * (a * Real.sinh (a * x))) x := by
    change HasDerivAt (fun y : ℝ => h 0 * Real.cosh (a * y))
      (h 0 * (a * Real.sinh (a * x))) x
    have hRaw : HasDerivAt (fun y : ℝ => h 0 * Real.cosh (a * y))
        (h 0 * (Real.sinh (a * x) * a)) x := by
      simpa [id] using
        (((hasDerivAt_id x).const_mul a).cosh.const_mul (h 0))
    exact hRaw.congr_deriv (by ring)
  have hTargetFirstOrder (x : ℝ) :
      h 0 * (a * Real.sinh (a * x)) + a * target x =
        a * h 0 * Real.exp (a * x) := by
    dsimp only [target]
    rw [← Real.cosh_add_sinh]
    ring
  let vanishing : ℝ → ℝ := fun x => Real.exp (a * x) * (h x - target x)
  have hVanishingDeriv (x : ℝ) (hx : x ∈ interval) :
      HasDerivAt vanishing 0 x := by
    have hExp : HasDerivAt (fun y : ℝ => Real.exp (a * y))
        (a * Real.exp (a * x)) x := by
      have hRaw : HasDerivAt (fun y : ℝ => Real.exp (a * y))
          (Real.exp (a * x) * a) x := by
        simpa [id] using ((hasDerivAt_id x).const_mul a).exp
      exact hRaw.congr_deriv (by ring)
    have hDiff : HasDerivAt (fun y : ℝ => h y - target y)
        (d x - h 0 * (a * Real.sinh (a * x))) x :=
      (hFirst x hx).sub (hTargetDeriv x)
    change HasDerivAt (fun y : ℝ =>
      Real.exp (a * y) * (h y - target y)) 0 x
    have hZeroDeriv :
        a * Real.exp (a * x) * (h x - target x) +
            Real.exp (a * x) *
              (d x - h 0 * (a * Real.sinh (a * x))) = 0 := by
      calc
        a * Real.exp (a * x) * (h x - target x) +
              Real.exp (a * x) *
                (d x - h 0 * (a * Real.sinh (a * x))) =
            Real.exp (a * x) *
              ((d x + a * h x) -
                (h 0 * (a * Real.sinh (a * x)) + a * target x)) := by ring
        _ = 0 := by rw [hFirstOrder x hx, hTargetFirstOrder x]; ring
    exact (hExp.mul hDiff).congr_deriv hZeroDeriv
  have hVanishingConstant :
      ∀ x ∈ interval, vanishing x = vanishing 0 := by
    have hDifferentiable : DifferentiableOn ℝ vanishing interval := by
      intro x hx
      exact (hVanishingDeriv x hx).differentiableAt.differentiableWithinAt
    have hDerivZero : interval.EqOn (deriv vanishing) 0 := by
      intro x hx
      exact (hVanishingDeriv x hx).deriv
    intro x hx
    exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      hDifferentiable hDerivZero hx hZero
  intro x hx
  have hConst := hVanishingConstant x hx
  have hAtZero : vanishing 0 = 0 := by
    simp [vanishing, target]
  rw [hAtZero] at hConst
  have hExpNe : Real.exp (a * x) ≠ 0 := (Real.exp_pos _).ne'
  dsimp only [vanishing] at hConst
  have : h x - target x = 0 := (mul_eq_zero.mp hConst).resolve_left hExpNe
  exact sub_eq_zero.mp this

/-- Two real-axis spectral correlations with the same local Green source differ only by the
hyperbolic cosine mode, whose coefficient is their resolvent-budget difference at zero. -/
theorem local_completion_difference
    (L a : ℝ) (ν μ : Measure ℝ) (Dν Dμ source : ℝ → ℝ)
    (hL : 0 < L)
    (hνFirst : ∀ t ∈ Ioo (-2 * L) (2 * L),
      HasDerivAt
        (fun u => ∫ ξ : ℝ, Real.cos (u * ξ) / (ξ ^ 2 + a ^ 2) ∂ν)
        (Dν t) t)
    (hμFirst : ∀ t ∈ Ioo (-2 * L) (2 * L),
      HasDerivAt
        (fun u => ∫ ξ : ℝ, Real.cos (u * ξ) / (ξ ^ 2 + a ^ 2) ∂μ)
        (Dμ t) t)
    (hνSecond : ∀ t ∈ Ioo (-2 * L) (2 * L),
      HasDerivAt Dν
        (a ^ 2 * (∫ ξ : ℝ, Real.cos (t * ξ) / (ξ ^ 2 + a ^ 2) ∂ν) + source t) t)
    (hμSecond : ∀ t ∈ Ioo (-2 * L) (2 * L),
      HasDerivAt Dμ
        (a ^ 2 * (∫ ξ : ℝ, Real.cos (t * ξ) / (ξ ^ 2 + a ^ 2) ∂μ) + source t) t) :
    ∀ t, |t| < 2 * L →
      (∫ ξ : ℝ, Real.cos (t * ξ) / (ξ ^ 2 + a ^ 2) ∂ν) -
          (∫ ξ : ℝ, Real.cos (t * ξ) / (ξ ^ 2 + a ^ 2) ∂μ) =
        ((∫ ξ : ℝ, Real.cos (0 * ξ) / (ξ ^ 2 + a ^ 2) ∂ν) -
          (∫ ξ : ℝ, Real.cos (0 * ξ) / (ξ ^ 2 + a ^ 2) ∂μ)) *
          Real.cosh (a * t) := by
  let Hν : ℝ → ℝ := fun t =>
    ∫ ξ : ℝ, Real.cos (t * ξ) / (ξ ^ 2 + a ^ 2) ∂ν
  let Hμ : ℝ → ℝ := fun t =>
    ∫ ξ : ℝ, Real.cos (t * ξ) / (ξ ^ 2 + a ^ 2) ∂μ
  let h : ℝ → ℝ := fun t => Hν t - Hμ t
  let d : ℝ → ℝ := fun t => Dν t - Dμ t
  have hFirst : ∀ x ∈ Ioo (-2 * L) (2 * L), HasDerivAt h (d x) x := by
    intro x hx
    exact (hνFirst x hx).sub (hμFirst x hx)
  have hSecond : ∀ x ∈ Ioo (-2 * L) (2 * L),
      HasDerivAt d (a ^ 2 * h x) x := by
    intro x hx
    change HasDerivAt (fun t => Dν t - Dμ t)
      (a ^ 2 * (Hν x - Hμ x)) x
    exact ((hνSecond x hx).sub (hμSecond x hx)).congr_deriv (by
      dsimp only [Hν, Hμ]
      ring)
  have hEven : ∀ x, h (-x) = h x := by
    intro x
    dsimp only [h, Hν, Hμ]
    congr 1 <;>
      apply integral_congr_ae <;>
      filter_upwards with ξ <;>
      rw [show -x * ξ = -(x * ξ) by ring, Real.cos_neg]
  have hCore := even_ode_solution_eq_cosh L a h d hL hFirst hSecond hEven
  intro t ht
  have htInterval : t ∈ Ioo (-2 * L) (2 * L) := by
    constructor <;> linarith [(abs_lt.mp ht).1, (abs_lt.mp ht).2]
  simpa only [h, Hν, Hμ] using hCore t htInterval

private theorem weighted_integrable
    (r : ℝ) (f : ℝ → ℂ) (hf : Continuous f)
    (hfSupport : HasCompactSupport f) :
    Integrable (fun x : ℝ => (Real.exp (r * x) : ℂ) * f x) := by
  apply Continuous.integrable_of_hasCompactSupport
  · fun_prop
  · exact hfSupport.mul_left

private theorem weighted_convolution_integral
    (r : ℝ) (f h : ℝ → ℂ)
    (hf : Continuous f) (hfSupport : HasCompactSupport f)
    (hh : Continuous h) (hhSupport : HasCompactSupport h) :
    (∫ t : ℝ, (Real.exp (r * t) : ℂ) *
        (f ⋆[ContinuousLinearMap.mul ℂ ℂ]
          (fun x => conj (h (-x)))) t) =
      (∫ x : ℝ, (Real.exp (r * x) : ℂ) * f x) *
        conj (∫ x : ℝ, (Real.exp (-r * x) : ℂ) * h x) := by
  let F : ℝ → ℂ := fun x => (Real.exp (r * x) : ℂ) * f x
  let G : ℝ → ℂ := fun x => (Real.exp (r * x) : ℂ) * conj (h (-x))
  have hFContinuous : Continuous F := by
    fun_prop
  have hFSupport : HasCompactSupport F := by
    exact hfSupport.mul_left
  have hFIntegrable : Integrable F :=
    hFContinuous.integrable_of_hasCompactSupport hFSupport
  have hNegSupport : HasCompactSupport (fun x : ℝ => h (-x)) := by
    simpa [Function.comp_def, Homeomorph.neg] using
      hhSupport.comp_homeomorph (Homeomorph.neg ℝ)
  have hConjSupport : HasCompactSupport (fun x : ℝ => conj (h (-x))) := by
    exact hNegSupport.comp_left (by simp)
  have hGContinuous : Continuous G := by
    fun_prop
  have hGSupport : HasCompactSupport G := by
    exact hConjSupport.mul_left
  have hGIntegrable : Integrable G :=
    hGContinuous.integrable_of_hasCompactSupport hGSupport
  have hPointwise (t : ℝ) :
      (Real.exp (r * t) : ℂ) *
          (f ⋆[ContinuousLinearMap.mul ℂ ℂ]
            (fun x => conj (h (-x)))) t =
        (F ⋆[ContinuousLinearMap.mul ℂ ℂ] G) t := by
    simp only [MeasureTheory.convolution_def]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [F, G]
    change ((Real.exp (r * t) : ℝ) : ℂ) *
        (f x * conj (h (-(t - x)))) =
      (((Real.exp (r * x) : ℝ) : ℂ) * f x) *
        (((Real.exp (r * (t - x)) : ℝ) : ℂ) * conj (h (-(t - x))))
    have hExp : Real.exp (r * t) =
        Real.exp (r * x) * Real.exp (r * (t - x)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hExp]
    push_cast
    ring
  have hGIntegral :
      (∫ x : ℝ, G x) =
        conj (∫ x : ℝ, (Real.exp (-r * x) : ℂ) * h x) := by
    rw [← integral_conj,
      ← integral_neg_eq_self (fun x : ℝ => G x) volume]
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [G]
    rw [map_mul]
    simp only [Complex.conj_ofReal, neg_neg]
    congr 2
    congr 1
    ring
  calc
    (∫ t : ℝ, (Real.exp (r * t) : ℂ) *
        (f ⋆[ContinuousLinearMap.mul ℂ ℂ]
          (fun x => conj (h (-x)))) t) =
        ∫ t : ℝ, (F ⋆[ContinuousLinearMap.mul ℂ ℂ] G) t := by
          apply integral_congr_ae
          filter_upwards with t
          exact hPointwise t
    _ = (∫ x : ℝ, F x) * ∫ x : ℝ, G x := by
      simpa using integral_convolution
        (ContinuousLinearMap.mul ℂ ℂ) hFIntegrable hGIntegrable
    _ = (∫ x : ℝ, (Real.exp (r * x) : ℂ) * f x) *
        conj (∫ x : ℝ, (Real.exp (-r * x) : ℂ) * h x) := by
      rw [hGIntegral]

/-- The hyperbolic-cosine pairing of a convolution with involution is the positive even
Laplace-channel product minus the odd Laplace-channel product. -/
theorem cosh_correlation_signature
    (a : ℝ) (f h : ℝ → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfSupport : HasCompactSupport f)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhSupport : HasCompactSupport h) :
    (∫ t : ℝ, (Real.cosh (a * t) : ℂ) *
        (f ⋆[ContinuousLinearMap.mul ℂ ℂ]
          (fun x => conj (h (-x)))) t) =
      (∫ x : ℝ, (Real.cosh (a * x) : ℂ) * f x) *
          conj (∫ x : ℝ, (Real.cosh (a * x) : ℂ) * h x) -
        (∫ x : ℝ, (Real.sinh (a * x) : ℂ) * f x) *
          conj (∫ x : ℝ, (Real.sinh (a * x) : ℂ) * h x) := by
  let hTilde : ℝ → ℂ := fun x => conj (h (-x))
  let k : ℝ → ℂ := f ⋆[ContinuousLinearMap.mul ℂ ℂ] hTilde
  have hTildeContinuous : Continuous hTilde := by
    fun_prop
  have hTildeSupport : HasCompactSupport hTilde := by
    have hNegSupport : HasCompactSupport (fun x : ℝ => h (-x)) := by
      simpa [Function.comp_def, Homeomorph.neg] using
        hhSupport.comp_homeomorph (Homeomorph.neg ℝ)
    exact hNegSupport.comp_left (by simp)
  have hkContinuous : Continuous k := by
    exact hfSupport.continuous_convolution_left
      (ContinuousLinearMap.mul ℂ ℂ) hf.continuous hTildeContinuous.locallyIntegrable
  have hkSupport : HasCompactSupport k := by
    exact hfSupport.convolution (ContinuousLinearMap.mul ℂ ℂ) hTildeSupport
  have hfp := weighted_integrable a f hf.continuous hfSupport
  have hfm := weighted_integrable (-a) f hf.continuous hfSupport
  have hhp := weighted_integrable a h hh.continuous hhSupport
  have hhm := weighted_integrable (-a) h hh.continuous hhSupport
  have hkp := weighted_integrable a k hkContinuous hkSupport
  have hkm := weighted_integrable (-a) k hkContinuous hkSupport
  have hPlus := weighted_convolution_integral a f h
    hf.continuous hfSupport hh.continuous hhSupport
  have hMinus := weighted_convolution_integral (-a) f h
    hf.continuous hfSupport hh.continuous hhSupport
  change (∫ t : ℝ, (Real.exp (a * t) : ℂ) * k t) = _ at hPlus
  change (∫ t : ℝ, (Real.exp (-a * t) : ℂ) * k t) = _ at hMinus
  simp only [neg_neg] at hMinus
  have hCoshK :
      (∫ t : ℝ, (Real.cosh (a * t) : ℂ) * k t) =
        ((∫ t : ℝ, (Real.exp (a * t) : ℂ) * k t) +
          ∫ t : ℝ, (Real.exp (-a * t) : ℂ) * k t) / 2 := by
    rw [show (fun t : ℝ => (Real.cosh (a * t) : ℂ) * k t) =
        fun t => ((Real.exp (a * t) : ℂ) * k t +
          (Real.exp (-a * t) : ℂ) * k t) / 2 by
      funext t
      simp only [Real.cosh_eq, Complex.ofReal_div, Complex.ofReal_add,
        Complex.ofReal_exp]
      norm_num [div_eq_mul_inv]
      ring]
    rw [integral_div, integral_add hkp hkm]
  have hCoshF :
      (∫ x : ℝ, (Real.cosh (a * x) : ℂ) * f x) =
        ((∫ x : ℝ, (Real.exp (a * x) : ℂ) * f x) +
          ∫ x : ℝ, (Real.exp (-a * x) : ℂ) * f x) / 2 := by
    rw [show (fun x : ℝ => (Real.cosh (a * x) : ℂ) * f x) =
        fun x => ((Real.exp (a * x) : ℂ) * f x +
          (Real.exp (-a * x) : ℂ) * f x) / 2 by
      funext x
      simp only [Real.cosh_eq, Complex.ofReal_div, Complex.ofReal_add,
        Complex.ofReal_exp]
      norm_num [div_eq_mul_inv]
      ring]
    rw [integral_div, integral_add hfp hfm]
  have hSinhF :
      (∫ x : ℝ, (Real.sinh (a * x) : ℂ) * f x) =
        ((∫ x : ℝ, (Real.exp (a * x) : ℂ) * f x) -
          ∫ x : ℝ, (Real.exp (-a * x) : ℂ) * f x) / 2 := by
    rw [show (fun x : ℝ => (Real.sinh (a * x) : ℂ) * f x) =
        fun x => ((Real.exp (a * x) : ℂ) * f x -
          (Real.exp (-a * x) : ℂ) * f x) / 2 by
      funext x
      simp only [Real.sinh_eq, Complex.ofReal_div, Complex.ofReal_sub,
        Complex.ofReal_exp]
      norm_num [div_eq_mul_inv]
      ring]
    rw [integral_div, integral_sub hfp hfm]
  have hCoshH :
      (∫ x : ℝ, (Real.cosh (a * x) : ℂ) * h x) =
        ((∫ x : ℝ, (Real.exp (a * x) : ℂ) * h x) +
          ∫ x : ℝ, (Real.exp (-a * x) : ℂ) * h x) / 2 := by
    rw [show (fun x : ℝ => (Real.cosh (a * x) : ℂ) * h x) =
        fun x => ((Real.exp (a * x) : ℂ) * h x +
          (Real.exp (-a * x) : ℂ) * h x) / 2 by
      funext x
      simp only [Real.cosh_eq, Complex.ofReal_div, Complex.ofReal_add,
        Complex.ofReal_exp]
      norm_num [div_eq_mul_inv]
      ring]
    rw [integral_div, integral_add hhp hhm]
  have hSinhH :
      (∫ x : ℝ, (Real.sinh (a * x) : ℂ) * h x) =
        ((∫ x : ℝ, (Real.exp (a * x) : ℂ) * h x) -
          ∫ x : ℝ, (Real.exp (-a * x) : ℂ) * h x) / 2 := by
    rw [show (fun x : ℝ => (Real.sinh (a * x) : ℂ) * h x) =
        fun x => ((Real.exp (a * x) : ℂ) * h x -
          (Real.exp (-a * x) : ℂ) * h x) / 2 by
      funext x
      simp only [Real.sinh_eq, Complex.ofReal_div, Complex.ofReal_sub,
        Complex.ofReal_exp]
      norm_num [div_eq_mul_inv]
      ring]
    rw [integral_div, integral_sub hhp hhm]
  change (∫ t : ℝ, (Real.cosh (a * t) : ℂ) * k t) = _
  rw [hCoshK, hCoshF, hSinhF, hCoshH, hSinhH, hPlus, hMinus]
  simp only [map_add, map_sub, map_div₀, map_ofNat]
  ring

#print axioms local_completion_difference
#print axioms cosh_correlation_signature

end D5.S3.Weil.ZetaCore.ResolventParitySignatures
