/- GID: D5/S3/Weil/TestFunctions/FourierLaplaceClosedStripDecay
   generality: I
   mirror-B: D5/B/S3/Weil/TestFunctions/FourierLaplaceClosedStripDecay
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fourier-Laplace transforms of Weil test functions decay uniformly on closed strips. -/

import D5.S3.Weil.TestFunctions
import D5.S3.Weil.FourierLaplace
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/- Library-search audit trail (2026-09-03):
   * The exact declaration shape `fourierLaplace_decay_closedStrip` and the
     closed-strip conclusion were absent from `D5/` on `origin/dev`.
   * The existing `fourierLaplace_apply` declaration is the canonical transform
     integral; no second transform primitive is introduced here.
   * Pinned Mathlib supplies `integral_mul_deriv_eq_deriv_mul_of_integrable`,
     `ContDiff.iterate_deriv`, `HasCompactSupport.deriv`,
     `norm_integral_le_integral_norm`, `Complex.norm_exp`, and
     `Complex.abs_re_le_norm`, which are used directly below.

   The theorem is uniform for every nonnegative strip width `eta`; it makes no
   claim about zero sums or a separator limit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open D5.S3.Weil.Convention
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace
open scoped ContDiff Convolution

namespace D5.S3.Weil.TestFunctions.FourierLaplaceClosedStripDecay

private theorem fourier_laplace_iterate_deriv
    (q : ℕ) (g : ℝ → ℂ) (hgSmooth : ContDiff ℝ ∞ g)
    (hgCompact : HasCompactSupport g) (z : ℂ) :
    (∫ x : ℝ, Complex.exp (-Complex.I * z * (x : ℂ)) * ((deriv^[q]) g) x) =
      (Complex.I * z) ^ q *
        (∫ x : ℝ, Complex.exp (-Complex.I * z * (x : ℂ)) * g x) := by
  have hcompact (n : ℕ) : HasCompactSupport ((deriv^[n]) g) := by
    induction n with
    | zero => simpa
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact ih.deriv
  induction q with
  | zero => simp
  | succ q ih =>
      let v : ℝ → ℂ := (deriv^[q]) g
      let v' : ℝ → ℂ := (deriv^[q + 1]) g
      let u : ℝ → ℂ := fun x =>
        Complex.exp (-Complex.I * z * (x : ℂ))
      let u' : ℝ → ℂ := fun x =>
        (-Complex.I * z) * Complex.exp (-Complex.I * z * (x : ℂ))
      have hvSmooth : ContDiff ℝ ∞ v :=
        ContDiff.iterate_deriv q hgSmooth
      have hvCompact : HasCompactSupport v := by
        simpa only [v] using hcompact q
      have hv'Compact : HasCompactSupport v' := by
        simpa only [v, v', Function.iterate_succ_apply'] using hvCompact.deriv
      have huDeriv (x : ℝ) : HasDerivAt u (u' x) x := by
        have hinner : HasDerivAt (fun y : ℝ =>
            (-Complex.I * z) * (y : ℂ)) (-Complex.I * z) x :=
          by simpa using
            ((hasDerivAt_id x).ofReal_comp).const_mul (-Complex.I * z)
        simpa only [u, u', neg_mul, mul_comm] using hinner.cexp
      have hvDeriv (x : ℝ) : HasDerivAt v (v' x) x := by
        simpa only [v, v', Function.iterate_succ_apply'] using
          (hvSmooth.differentiable (by simp) x).hasDerivAt
      have huv' : Integrable (u * v') :=
        ((by fun_prop : Continuous u).mul
          (ContDiff.iterate_deriv (q + 1) hgSmooth).continuous).integrable_of_hasCompactSupport
          hv'Compact.mul_left
      have hu'v : Integrable (u' * v) :=
        (by fun_prop : Continuous (u' * v)).integrable_of_hasCompactSupport
          hvCompact.mul_left
      have huv : Integrable (u * v) :=
        (by fun_prop : Continuous (u * v)).integrable_of_hasCompactSupport
          hvCompact.mul_left
      have hparts := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
        (u := u) (u' := u') (v := v) (v' := v')
        (fun x _ => huDeriv x) (fun x _ => hvDeriv x) huv' hu'v huv
      change (∫ x : ℝ, u x * v' x) = _
      rw [hparts]
      change -(∫ x : ℝ, ((-Complex.I * z) * u x) * v x) = _
      rw [show (fun x : ℝ => ((-Complex.I * z) * u x) * v x) =
          fun x => (-Complex.I * z) * (u x * v x) by
        funext x
        ring]
      rw [integral_const_mul, ih, pow_succ]
      ring

private theorem fourierLaplace_bound_closedStrip_raw
    (g : ℝ → ℂ) (hgContinuous : Continuous g) (hgCompact : HasCompactSupport g)
    (η : ℝ) (w : ℂ) (hw : |w.im| ≤ η) :
    ‖∫ x : ℝ, Complex.exp (-Complex.I * w * (x : ℂ)) * g x‖ ≤
      ∫ x : ℝ, Real.exp (η * |x|) * ‖g x‖ := by
  have htwisted : Integrable
      (fun x : ℝ => Complex.exp (-Complex.I * w * (x : ℂ)) * g x) := by
    apply ((by fun_prop : Continuous (fun x : ℝ =>
      Complex.exp (-Complex.I * w * (x : ℂ)))).mul hgContinuous).integrable_of_hasCompactSupport
    exact hgCompact.mul_left
  have hmajor : Integrable (fun x : ℝ => Real.exp (η * |x|) * ‖g x‖) := by
    apply (by fun_prop : Continuous (fun x : ℝ =>
      Real.exp (η * |x|) * ‖g x‖)).integrable_of_hasCompactSupport
    exact hgCompact.norm.mul_left
  refine (norm_integral_le_integral_norm _).trans
    (integral_mono htwisted.norm hmajor ?_)
  intro x
  change ‖Complex.exp (-Complex.I * w * (x : ℂ)) * g x‖ ≤
    Real.exp (η * |x|) * ‖g x‖
  rw [norm_mul, Complex.norm_exp]
  have hre : (-Complex.I * w * (x : ℂ)).re = w.im * x := by
    simp [Complex.mul_re]
  rw [hre]
  apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  calc
    w.im * x ≤ |w.im * x| := le_abs_self _
    _ = |w.im| * |x| := abs_mul _ _
    _ ≤ η * |x| := mul_le_mul_of_nonneg_right hw (abs_nonneg x)

/-- The specific weighted zeroth-plus-second-derivative constant. -/
def closedStripJetBudget (b : WeilTestFunction) (η : ℝ) : ℝ :=
  (∫ x : ℝ, Real.exp (η * |x|) * ‖b x‖) +
    ∫ x : ℝ, Real.exp (η * |x|) * ‖((deriv^[2]) (b : ℝ → ℂ)) x‖

/-- The original integration-by-parts proof gives this specific two-jet budget. -/
theorem closedStripJetBudget_spec
    (b : WeilTestFunction) (η : ℝ) (_hη : 0 ≤ η) :
    0 ≤ closedStripJetBudget b η ∧ ∀ w : ℂ, |w.im| ≤ η →
      ‖fourierLaplace b w‖ ≤ closedStripJetBudget b η / (1 + w.re ^ 2) := by
  let d2 : ℝ → ℂ := (deriv^[2]) (b : ℝ → ℂ)
  let C0 : ℝ := ∫ x : ℝ, Real.exp (η * |x|) * ‖b x‖
  let C2 : ℝ := ∫ x : ℝ, Real.exp (η * |x|) * ‖d2 x‖
  have hd2Smooth : ContDiff ℝ ∞ d2 := by
    exact ContDiff.iterate_deriv 2 b.contDiff
  have hd2Compact : HasCompactSupport d2 := by
    have hcompact (n : ℕ) : HasCompactSupport ((deriv^[n]) (b : ℝ → ℂ)) := by
      induction n with
      | zero => simpa using b.hasCompactSupport
      | succ n ih =>
          rw [Function.iterate_succ_apply']
          exact ih.deriv
    exact hcompact 2
  change 0 ≤ C0 + C2 ∧ ∀ w : ℂ, |w.im| ≤ η →
    ‖fourierLaplace b w‖ ≤ (C0 + C2) / (1 + w.re ^ 2)
  constructor
  · dsimp only [C0, C2]
    exact add_nonneg (integral_nonneg fun x =>
      mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
      (integral_nonneg fun x =>
        mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
  · intro w hw
    have h0raw := fourierLaplace_bound_closedStrip_raw
      (b : ℝ → ℂ) b.continuous b.hasCompactSupport η w hw
    have h0 : ‖fourierLaplace b w‖ ≤ C0 := by
      simpa only [fourierLaplace_apply, C0] using h0raw
    have h2raw := fourierLaplace_bound_closedStrip_raw
      d2 hd2Smooth.continuous hd2Compact η w hw
    have hderiv :
        (∫ x : ℝ, Complex.exp (-Complex.I * w * (x : ℂ)) * d2 x) =
          (Complex.I * w) ^ 2 * fourierLaplace b w := by
      simpa only [d2, fourierLaplace_apply] using
        fourier_laplace_iterate_deriv 2 (b : ℝ → ℂ)
          b.contDiff b.hasCompactSupport w
    have h2 :
        ‖(Complex.I * w) ^ 2 * fourierLaplace b w‖ ≤ C2 := by
      rw [← hderiv]
      simpa only [d2, C2] using h2raw
    have h2' : ‖w‖ ^ 2 * ‖fourierLaplace b w‖ ≤ C2 := by
      calc
        ‖w‖ ^ 2 * ‖fourierLaplace b w‖ =
            ‖(Complex.I * w) ^ 2 * fourierLaplace b w‖ := by
          simp only [norm_mul, Complex.norm_pow, Complex.norm_I, one_mul]
        _ ≤ C2 := h2
    have hre : w.re ^ 2 ≤ ‖w‖ ^ 2 := by
      calc
        w.re ^ 2 = |w.re| ^ 2 := by rw [sq_abs]
        _ ≤ ‖w‖ ^ 2 := by gcongr; exact Complex.abs_re_le_norm w
    have hreal2 : w.re ^ 2 * ‖fourierLaplace b w‖ ≤ C2 :=
      (mul_le_mul_of_nonneg_right hre (norm_nonneg _)).trans h2'
    have hcombined :
        (1 + w.re ^ 2) * ‖fourierLaplace b w‖ ≤ C0 + C2 := by
      calc
        (1 + w.re ^ 2) * ‖fourierLaplace b w‖ =
            ‖fourierLaplace b w‖ +
              w.re ^ 2 * ‖fourierLaplace b w‖ := by ring
        _ ≤ C0 + C2 := add_le_add h0 hreal2
    have hden : 0 < 1 + w.re ^ 2 := by positivity
    apply (le_div_iff₀ hden).2
    simpa only [C0, C2, mul_comm] using hcombined

/-- The original public existential interface is preserved. -/
theorem fourierLaplace_decay_closedStrip
    (b : WeilTestFunction) (η : ℝ) (hη : 0 ≤ η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, |w.im| ≤ η →
      ‖fourierLaplace b w‖ ≤ C / (1 + w.re ^ 2) :=
  ⟨closedStripJetBudget b η, closedStripJetBudget_spec b η hη⟩

private theorem weighted_norm_integral_le_support
    (g : ℝ → ℂ) (hg : Continuous g) (hc : HasCompactSupport g)
    (B η J : ℝ) (hη : 0 ≤ η)
    (hs : tsupport g ⊆ Set.Icc (-B) B) (hJ : (∫ x : ℝ, ‖g x‖) ≤ J) :
    (∫ x : ℝ, Real.exp (η * |x|) * ‖g x‖) ≤ Real.exp (η * B) * J := by
  have hi := hg.integrable_of_hasCompactSupport hc
  have hw : Integrable (fun x : ℝ => Real.exp (η * |x|) * ‖g x‖) :=
    (by fun_prop : Continuous (fun x : ℝ => Real.exp (η * |x|) * ‖g x‖)).integrable_of_hasCompactSupport
      hc.norm.mul_left
  calc
    _ ≤ ∫ x : ℝ, Real.exp (η * B) * ‖g x‖ := by
      apply integral_mono hw (hi.norm.const_mul _)
      intro x
      by_cases hx : g x = 0
      · simp [hx]
      · have habs : |x| ≤ B := abs_le.mpr (hs (subset_tsupport g hx))
        exact mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs hη)) (norm_nonneg _)
    _ = Real.exp (η * B) * (∫ x : ℝ, ‖g x‖) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hJ (Real.exp_pos _).le

/-- Two finite unweighted L1 enclosures and a support radius bound the exact
closed-strip budget. The derivative support is inherited from the original test. -/
theorem closedStripJetBudget_le_support_jets
    (b : WeilTestFunction) (B η J0 J2 : ℝ) (hη : 0 ≤ η)
    (hs : tsupport (b : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (hJ0 : (∫ x : ℝ, ‖b x‖) ≤ J0)
    (hJ2 : (∫ x : ℝ, ‖((deriv^[2]) (b : ℝ → ℂ)) x‖) ≤ J2) :
    closedStripJetBudget b η ≤ Real.exp (η * B) * (J0 + J2) := by
  have hd2Smooth : ContDiff ℝ ∞ ((deriv^[2]) (b : ℝ → ℂ)) :=
    ContDiff.iterate_deriv 2 b.contDiff
  have hd2Compact : HasCompactSupport ((deriv^[2]) (b : ℝ → ℂ)) := by
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using
      b.hasCompactSupport.deriv.deriv
  have hd2support : tsupport ((deriv^[2]) (b : ℝ → ℂ)) ⊆ Set.Icc (-B) B := by
    have h := (tsupport_deriv_subset (f := deriv (b : ℝ → ℂ))).trans
      ((tsupport_deriv_subset (f := (b : ℝ → ℂ))).trans hs)
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using h
  have h0 := weighted_norm_integral_le_support (b : ℝ → ℂ) b.continuous
    b.hasCompactSupport B η J0 hη hs hJ0
  have h2 := weighted_norm_integral_le_support ((deriv^[2]) (b : ℝ → ℂ))
    hd2Smooth.continuous hd2Compact B η J2 hη hd2support hJ2
  unfold closedStripJetBudget
  calc
    _ ≤ Real.exp (η * B) * J0 + Real.exp (η * B) * J2 := add_le_add h0 h2
    _ = _ := by ring

example : Nonempty WeilTestFunction := ⟨standardTestFunction⟩

example (η : ℝ) (hη : 0 ≤ η) : ∃ C : ℝ, 0 ≤ C := by
  rcases fourierLaplace_decay_closedStrip standardTestFunction η hη with ⟨C, hC, _⟩
  exact ⟨C, hC⟩

#print axioms closedStripJetBudget_spec
#print axioms closedStripJetBudget_le_support_jets
#print axioms fourierLaplace_decay_closedStrip

end D5.S3.Weil.TestFunctions.FourierLaplaceClosedStripDecay
