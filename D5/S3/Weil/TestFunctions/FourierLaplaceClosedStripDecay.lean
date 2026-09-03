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

/-- For every nonnegative strip width, the transform decays quadratically in
the real direction, uniformly over the closed strip. -/
theorem fourierLaplace_decay_closedStrip
    (b : WeilTestFunction) (η : ℝ) (_hη : 0 ≤ η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, |w.im| ≤ η →
      ‖fourierLaplace b w‖ ≤ C / (1 + w.re ^ 2) := by
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
  refine ⟨C0 + C2, ?_, ?_⟩
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

example : Nonempty WeilTestFunction := ⟨standardTestFunction⟩

example (η : ℝ) (hη : 0 ≤ η) : ∃ C : ℝ, 0 ≤ C := by
  rcases fourierLaplace_decay_closedStrip standardTestFunction η hη with ⟨C, hC, _⟩
  exact ⟨C, hC⟩

#print axioms fourierLaplace_decay_closedStrip

end D5.S3.Weil.TestFunctions.FourierLaplaceClosedStripDecay
