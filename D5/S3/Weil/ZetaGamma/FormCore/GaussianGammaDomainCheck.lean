import D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanCharge
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
import D5.S3.Analytic.Fourier.XiThetaTransform
import D5.S3.Weil.BurnolGram.SameWindowLogarithmicError
import D5.S3.Weil.ZetaGamma.LogarithmicFormContinuity
import D5.S3.Weil.ZetaRvm.CountByIntegral
import Batteries.Tactic.OpenPrivate
import D5.S3.Zeros.Jensen.OriginalPrimalTailResponse
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic
import D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData

/-
Transient exact-application fragment, not compiled or admitted.
Reuses the original primal-mode jets and the existing N=1 tail estimates.
The translated ray is allowed to start at any a >= 0; all derivative orders
are covered. The original kernel is identified only on the open positive ray,
which is sufficient for the integral and the endpoint at positive infinity.
-/


set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft

open Real Set MeasureTheory Filter Polynomial
open scoped Topology
open D5.S3.Zeros.Jensen.OriginalPrimalTailProjection
open D5.S3.Zeros.Jensen.OriginalPrimalTailResponse
open D5.S3.Analytic.Fourier.ThetaDifferentialKernel
open private jetSize jet_eval_bound endpointConstant shiftedBudget
  primalJet_zero primalJet_deriv tailJet_deriv tailJet_continuous
  tailJet_endpoint from D5.S3.Zeros.Jensen.OriginalPrimalTailProjection
open private original_source_split from
  D5.S3.Zeros.Jensen.OriginalPrimalTailResponse

private def fullJet (r : ℕ) (x : ℝ) : ℝ :=
  primalJet r 1 x + tailJet r 1 x

private theorem fullJet_deriv (r : ℕ) (x : ℝ) :
    HasDerivAt (fullJet r) (fullJet (r+1) x) x :=
  (primalJet_deriv r 1 x).add (tailJet_deriv r 1 (by omega) x)

private theorem fullJet_continuous (r : ℕ) : Continuous (fullJet r) :=
  continuous_iff_continuousAt.mpr (fun x => (fullJet_deriv r x).continuousAt)

private theorem fullJet_eq_iterated (r : ℕ) :
    fullJet r = iteratedDeriv r (fullJet 0) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [iteratedDeriv_succ, ← ih]
    exact funext (fun x => (fullJet_deriv r x).deriv.symm)

private theorem fullJet_zero_eq_phi {x : ℝ} (hx : 0 ≤ x) :
    fullJet 0 x = romikPhi x := by
  rw [romikPhi_eq_source, original_source_split 1 hx]
  simp only [fullJet, primalJet_zero, originalHead, Finset.Icc_self,
    Finset.sum_singleton]
  congr 1
  exact tsum_congr (fun j => primalJet_zero (1+j+1) x)

private theorem fullJet_eq_phi_derivative (r : ℕ) {x : ℝ} (hx : 0 < x) :
    fullJet r x = iteratedDeriv r romikPhi x := by
  have he : Set.EqOn (fullJet 0) romikPhi (Ioi 0) :=
    fun y hy => fullJet_zero_eq_phi hy.le
  rw [fullJet_eq_iterated]
  exact he.iteratedDeriv_of_isOpen isOpen_Ioi r hx

/- The first mode has scale pi, so the old >=12 tail hypothesis does not
   apply. A quadratic Taylor estimate gives the needed separate bound. -/
private theorem quadratic_exponent {A L x : ℝ} (hA : 1 ≤ A) (hx : 0 ≤ x) :
    L*x-A*(exp (2*x)-1) ≤ L^2/8-A*x := by
  have he := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2*x by linarith)
  have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ A by linarith)
  have hs := mul_nonneg (show 0 ≤ A-1 by linarith) (sq_nonneg x)
  have hc := sq_nonneg (2*x-L/2)
  nlinarith

private def firstConstant (r : ℕ) : ℝ :=
  jetSize r * (modeScale 1)^(r+2) * exp (-modeScale 1) *
    exp ((2*(r:ℝ)+5)^2/8)

private theorem firstConstant_nonneg (r : ℕ) : 0 ≤ firstConstant r := by
  dsimp [firstConstant, jetSize, modeScale]
  positivity

private theorem first_mode_bound (r : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    exp (x/2)*|primalJet r 1 x| ≤ firstConstant r * exp (-x) := by
  let A := modeScale 1
  let L : ℝ := 2*(r:ℝ)+5
  have hA : 1 ≤ A := by
    dsimp [A, modeScale]
    norm_num
    linarith [Real.pi_gt_three]
  have hy : 1 ≤ A*exp (2*x) := by
    have he : 1 ≤ exp (2*x) := one_le_exp (by linarith)
    nlinarith
  have hsz : 0 ≤ jetSize r :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have he : exp (x/2)*exp (x/2)*exp (-A*exp (2*x))*
      exp (2*x)^(r+2) = exp (-A)*exp (L*x-A*(exp (2*x)-1)) := by
    rw [← exp_nat_mul]
    simp only [← exp_add]
    congr 1
    dsimp [L]
    push_cast
    ring
  calc
    exp (x/2)*|primalJet r 1 x|
        ≤ exp (x/2)*(exp (x/2)*exp (-A*exp (2*x))*
            (jetSize r*(A*exp (2*x))^(r+2))) := by
      rw [primalJet, abs_mul, abs_mul, abs_of_pos (exp_pos _),
        abs_of_pos (exp_pos _)]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (jet_eval_bound r hy) (by positivity))
        (exp_pos _).le
    _ = jetSize r*A^(r+2)*exp (-A)*exp (L*x-A*(exp (2*x)-1)) := by
      rw [mul_pow]
      linear_combination (jetSize r*A^(r+2))*he
    _ ≤ jetSize r*A^(r+2)*exp (-A)*exp (L^2/8-A*x) :=
      mul_le_mul_of_nonneg_left
        (exp_le_exp.mpr (quadratic_exponent hA hx)) (by positivity)
    _ = firstConstant r*exp (-A*x) := by
      rw [show L^2/8-A*x = L^2/8 + -A*x by ring, exp_add]
      dsimp [firstConstant, L, A]
      ring
    _ ≤ firstConstant r*exp (-x) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by nlinarith))
        (firstConstant_nonneg r)

private def tailConstant (r : ℕ) : ℝ :=
  jetSize r * endpointConstant 0 r 0 * (modeScale 2)^(r+2) *
    exp (-modeScale 2) * shiftedBudget (r+2)

private theorem tailConstant_nonneg (r : ℕ) : 0 ≤ tailConstant r := by
  dsimp [tailConstant, jetSize, endpointConstant, shiftedBudget, modeScale]
  positivity

private theorem tail_mode_bound (r : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    exp (x/2)*|tailJet r 1 x| ≤ tailConstant r*exp (-x) := by
  have hb := tailJet_endpoint 0 r 0 1 (by omega) hx
  norm_num only [zero_mul, zero_div, exp_zero, pow_zero, mul_one,
    one_mul, Nat.reduceAdd] at hb
  have hA : 3/2 ≤ modeScale 2 := by
    dsimp [modeScale]
    norm_num
    linarith [Real.pi_gt_three]
  calc
    exp (x/2)*|tailJet r 1 x|
        ≤ exp (x/2)*(tailConstant r*exp (-modeScale 2*x)) :=
      mul_le_mul_of_nonneg_left hb (exp_pos _).le
    _ = tailConstant r*exp ((1/2-modeScale 2)*x) := by
      rw [show (1/2-modeScale 2)*x = x/2 + -modeScale 2*x by ring,
        exp_add]
      ring
    _ ≤ tailConstant r*exp (-x) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by nlinarith))
        (tailConstant_nonneg r)

private def fullConstant (r : ℕ) : ℝ := firstConstant r + tailConstant r

private theorem fullConstant_nonneg (r : ℕ) : 0 ≤ fullConstant r :=
  add_nonneg (firstConstant_nonneg r) (tailConstant_nonneg r)

private theorem full_bound (r : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    exp (x/2)*|fullJet r x| ≤ fullConstant r*exp (-x) := by
  calc
    _ ≤ exp (x/2)*(|primalJet r 1 x|+|tailJet r 1 x|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) (exp_pos _).le
    _ = exp (x/2)*|primalJet r 1 x|+exp (x/2)*|tailJet r 1 x| := by ring
    _ ≤ firstConstant r*exp (-x)+tailConstant r*exp (-x) :=
      add_le_add (first_mode_bound r hx) (tail_mode_bound r hx)
    _ = _ := by dsimp [fullConstant]; ring

private theorem translated_bound (r : ℕ) {a t : ℝ}
    (ha : 0 ≤ a) (ht : 0 ≤ t) :
    exp (t/2)*|fullJet r (a+t)| ≤ fullConstant r*exp (-t) := by
  calc
    _ ≤ exp ((a+t)/2)*|fullJet r (a+t)| :=
      mul_le_mul_of_nonneg_right (exp_le_exp.mpr (by linarith)) (abs_nonneg _)
    _ ≤ fullConstant r*exp (-(a+t)) := full_bound r (by linarith)
    _ ≤ fullConstant r*exp (-t) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith))
        (fullConstant_nonneg r)

/-- All original-kernel derivative orders on every nonnegative translated ray
    have the exact exponential weight required by the one-sided mean ODE. -/
theorem translated_phi_jets (r : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun t : ℝ => exp (t/2)*|iteratedDeriv r romikPhi (a+t)|)
      (Ioi 0) ∧
    Tendsto (fun t : ℝ => exp (t/2)*|iteratedDeriv r romikPhi (a+t)|)
      atTop (𝓝 0) := by
  have hc : Continuous (fun t : ℝ => exp (t/2)*|fullJet r (a+t)|) := by
    exact (by fun_prop : Continuous (fun t : ℝ => exp (t/2))).mul
      ((fullJet_continuous r).comp (continuous_const.add continuous_id)).abs
  have hi : IntegrableOn (fun t : ℝ => fullConstant r*exp (-t)) (Ioi 0) := by
    simpa only [IntegrableOn, neg_one_mul] using!
      (integrableOn_exp_mul_Ioi (show (-1:ℝ)<0 by norm_num) 0).const_mul
        (fullConstant r)
  have hj : IntegrableOn (fun t : ℝ => exp (t/2)*|fullJet r (a+t)|)
      (Ioi 0) := by
    apply hi.mono' hc.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact translated_bound r ha ht.le
  have he : Set.EqOn
      (fun t : ℝ => exp (t/2)*|fullJet r (a+t)|)
      (fun t : ℝ => exp (t/2)*|iteratedDeriv r romikPhi (a+t)|) (Ioi 0) := by
    intro t ht
    have htpos : 0 < t := ht
    change exp (t/2)*|fullJet r (a+t)| = exp (t/2)*|iteratedDeriv r romikPhi (a+t)|
    rw [fullJet_eq_phi_derivative r (by linarith : 0 < a+t)]
  refine ⟨hj.congr_fun he measurableSet_Ioi, ?_⟩
  apply squeeze_zero_norm' (a := fun t : ℝ => fullConstant r*exp (-t))
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity),
      ← fullJet_eq_phi_derivative r (by linarith : 0 < a+t)]
    exact translated_bound r ha ht.le
  · simpa only [mul_zero, neg_one_mul, Function.comp_def, id_eq] using!
      (tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (show (-1:ℝ)<0 by norm_num))).const_mul
        (fullConstant r)

end D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft

/-
Transient append fragment: concatenate after FullPhiTranslatedJets.fragment.lean
in the owning exact-check module. This shares that fragment's private fullJet
and derivative identification; no new framework or canonical declaration.
Not compiled or admitted.
-/

namespace D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft

open Real Set MeasureTheory Filter Polynomial
open scoped Topology
open D5.S3.Zeros.Jensen.OriginalPrimalTailProjection
open D5.S3.Analytic.Fourier.ThetaDifferentialKernel
open private tailJet_summable_ray from
  D5.S3.Zeros.Jensen.OriginalPrimalTailProjection
open private jet_one from D5.S3.Zeros.Jensen.OriginalPrimalTailResponse

private theorem first_polynomial_negative {z : ℝ} (hz : 6 ≤ z) :
    -8*z^3+30*z^2-15*z < 0 := by
  have hzpos : 0 < z := by linarith
  have hlin : 0 < 8*z-30 := by linarith
  have hfac : 0 < z*(8*z-30)+15 := by positivity
  have hprod := mul_pos hzpos hfac
  nlinarith

private theorem first_jet_negative_at_log_two (m : ℕ) (hm : 1 ≤ m) :
    primalJet 1 m (Real.log 2/2) < 0 := by
  have he : exp (2*(Real.log 2/2)) = 2 := by
    rw [show 2*(Real.log 2/2) = Real.log 2 by ring,
      Real.exp_log (by norm_num : (0:ℝ)<2)]
  have hmreal : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hmsq : (1:ℝ) ≤ (m:ℝ)^2 := by nlinarith
  have hscale : Real.pi ≤ modeScale m := by
    dsimp [modeScale]
    simpa using mul_le_mul_of_nonneg_left hmsq Real.pi_pos.le
  have hz : 6 ≤ modeScale m*exp (2*(Real.log 2/2)) := by
    rw [he]
    nlinarith [Real.pi_gt_three]
  have hp : (jetPolynomial 1).eval
      (modeScale m*exp (2*(Real.log 2/2))) < 0 := by
    rw [jet_one]
    exact first_polynomial_negative hz
  exact mul_neg_of_pos_of_neg
    (mul_pos (exp_pos _) (exp_pos _)) hp

/-- The derivative of the full original kernel, including every positive
    mode, is strictly negative at the natural shift delta = log(2)/2. -/
theorem phi_derivative_log_two_negative :
    deriv romikPhi (Real.log 2/2) < 0 := by
  have hdelta : 0 < Real.log 2/2 :=
    div_pos (Real.log_pos (by norm_num : (1:ℝ)<2)) (by norm_num)
  have hs := tailJet_summable_ray 1 1 (by omega) hdelta.le
  have ht : tailJet 1 1 (Real.log 2/2) ≤ 0 := by
    have hsum := hs.tsum_le_tsum
      (fun j => (first_jet_negative_at_log_two (1+j+1) (by omega)).le)
      (summable_zero : Summable (fun _ : ℕ => (0:ℝ)))
    simpa only [tailJet, tsum_zero] using hsum
  have hfull : fullJet 1 (Real.log 2/2) < 0 :=
    add_neg_of_neg_of_nonpos (first_jet_negative_at_log_two 1 (by omega)) ht
  rw [fullJet_eq_phi_derivative 1 hdelta] at hfull
  simpa only [iteratedDeriv_one] using hfull

end D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft

/- SOURCE DRAFT, NOT COMPILED. Transient exact-application fragment only.
   No new frozen declaration or mathematical-content claim is intended.
   The actual translated Romik jets must supply the hypotheses below.
   Two half-line FTC applications replace four individual IBP steps. -/


noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace RHFourJetDraft

def cosineRay (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (f t : ℂ) * Complex.cos (z * (t : ℂ))

def jetBudget (f : ℝ → ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), |f t| * Real.exp (t / 2)

private theorem strip_trig_bounds (z : ℂ) (hz : |z.im| ≤ 1 / 2)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖Complex.cos (z * (t : ℂ))‖ ≤ Real.exp (t / 2) ∧
    ‖Complex.sin (z * (t : ℂ))‖ ≤ Real.exp (t / 2) := by
  let w : ℂ := z * (t : ℂ)
  have hi : |w.im| ≤ t / 2 := by
    dsimp only [w]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_add, abs_mul, abs_of_nonneg ht]
    nlinarith [mul_le_mul_of_nonneg_right hz ht]
  have hp : ‖Complex.exp (w * Complex.I)‖ ≤ Real.exp (t / 2) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa only [Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero,
      mul_one, zero_sub, neg_neg] using neg_le_neg (abs_le.mp hi).1
  have hm : ‖Complex.exp (-w * Complex.I)‖ ≤ Real.exp (t / 2) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_im,
      mul_zero, mul_one, zero_sub, neg_neg] using (abs_le.mp hi).2
  constructor
  · have he : (2 : ℝ) * ‖Complex.cos w‖ =
        ‖Complex.exp (w * Complex.I) + Complex.exp (-w * Complex.I)‖ := by
      simpa using congrArg (fun q : ℂ => ‖q‖) (Complex.two_cos (x := w))
    have hn := norm_add_le (Complex.exp (w * Complex.I))
      (Complex.exp (-w * Complex.I))
    change ‖Complex.cos w‖ ≤ _
    linarith
  · have he : (2 : ℝ) * ‖Complex.sin w‖ =
        ‖Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)‖ := by
      simpa [norm_mul] using
        congrArg (fun q : ℂ => ‖q‖) (Complex.two_sin (x := w))
    have hn := norm_sub_le (Complex.exp (-w * Complex.I))
      (Complex.exp (w * Complex.I))
    change ‖Complex.sin w‖ ≤ _
    linarith

private theorem trig_product_integrable (f : ℝ → ℝ) (hf : Continuous f)
    (hL : IntegrableOn (fun t => |f t| * Real.exp (t / 2)) (Ioi 0))
    (z : ℂ) (hz : |z.im| ≤ 1 / 2) :
    IntegrableOn (fun t => (f t : ℂ) * Complex.cos (z * (t : ℂ))) (Ioi 0) ∧
    IntegrableOn (fun t => (f t : ℂ) * Complex.sin (z * (t : ℂ))) (Ioi 0) := by
  constructor
  · apply hL.mono' ((Complex.continuous_ofReal.comp hf).mul
      (by fun_prop)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change ‖(f t : ℂ) * Complex.cos (z * (t : ℂ))‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (strip_trig_bounds z hz ht.le).1 (abs_nonneg _)
  · apply hL.mono' ((Complex.continuous_ofReal.comp hf).mul
      (by fun_prop)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change ‖(f t : ℂ) * Complex.sin (z * (t : ℂ))‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (strip_trig_bounds z hz ht.le).2 (abs_nonneg _)

private theorem trig_product_tendsto (f : ℝ → ℝ)
    (hT : Tendsto (fun t => |f t| * Real.exp (t / 2)) atTop (𝓝 0))
    (z : ℂ) (hz : |z.im| ≤ 1 / 2) :
    Tendsto (fun t => (f t : ℂ) * Complex.cos (z * (t : ℂ))) atTop (𝓝 0) ∧
    Tendsto (fun t => (f t : ℂ) * Complex.sin (z * (t : ℂ))) atTop (𝓝 0) := by
  constructor
  · apply squeeze_zero_norm' (a := fun t => |f t| * Real.exp (t / 2))
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (strip_trig_bounds z hz ht).1 (abs_nonneg _)
    · exact hT
  · apply squeeze_zero_norm' (a := fun t => |f t| * Real.exp (t / 2))
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (strip_trig_bounds z hz ht).2 (abs_nonneg _)
    · exact hT

private theorem cosineRay_second (f0 f1 f2 : ℝ → ℝ)
    (hC0 : Continuous f0) (hC2 : Continuous f2)
    (hD0 : ∀ t ∈ Ici (0 : ℝ), HasDerivAt f0 (f1 t) t)
    (hD1 : ∀ t ∈ Ici (0 : ℝ), HasDerivAt f1 (f2 t) t)
    (hL0 : IntegrableOn (fun t => |f0 t| * Real.exp (t / 2)) (Ioi 0))
    (hL2 : IntegrableOn (fun t => |f2 t| * Real.exp (t / 2)) (Ioi 0))
    (hT0 : Tendsto (fun t => |f0 t| * Real.exp (t / 2)) atTop (𝓝 0))
    (hT1 : Tendsto (fun t => |f1 t| * Real.exp (t / 2)) atTop (𝓝 0))
    (z : ℂ) (hz : |z.im| ≤ 1 / 2) :
    cosineRay f2 z + z ^ 2 * cosineRay f0 z = -(f1 0 : ℂ) := by
  let H : ℝ → ℂ := fun t => (f1 t : ℂ) * Complex.cos (z * (t : ℂ)) +
    z * ((f0 t : ℂ) * Complex.sin (z * (t : ℂ)))
  let dH : ℝ → ℂ := fun t => (f2 t : ℂ) * Complex.cos (z * (t : ℂ)) +
    z ^ 2 * ((f0 t : ℂ) * Complex.cos (z * (t : ℂ)))
  have hd : ∀ t ∈ Ici (0 : ℝ), HasDerivAt H (dH t) t := by
    intro t ht
    have hc : HasDerivAt (fun t : ℝ => Complex.cos (z * (t : ℂ)))
        (-Complex.sin (z * (t : ℂ)) * z) t := by
      convert! (((hasDerivAt_id (t : ℂ)).const_mul z).ccos).comp_ofReal using 1 <;> simp
    have hs : HasDerivAt (fun t : ℝ => Complex.sin (z * (t : ℂ)))
        (Complex.cos (z * (t : ℂ)) * z) t := by
      convert! (((hasDerivAt_id (t : ℂ)).const_mul z).csin).comp_ofReal using 1 <;> simp
    convert! (((hD1 t ht).ofReal_comp).mul hc).add
      ((((hD0 t ht).ofReal_comp).mul hs).const_mul z) using 1 <;>
      dsimp only [H, dH] <;> ring
  have hi0 := (trig_product_integrable f0 hC0 hL0 z hz).1
  have hi2 := (trig_product_integrable f2 hC2 hL2 z hz).1
  have hi : IntegrableOn dH (Ioi 0) := hi2.add (hi0.const_mul (z ^ 2))
  have ht0 := (trig_product_tendsto f0 hT0 z hz).2
  have ht1 := (trig_product_tendsto f1 hT1 z hz).1
  have ht : Tendsto H atTop (𝓝 0) := by
    simpa only [H, mul_zero, add_zero] using ht1.add (ht0.const_mul z)
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hd hi ht
  have hI : (∫ t in Ioi (0 : ℝ), dH t) = -(f1 0 : ℂ) := by
    simpa only [H, Complex.ofReal_zero, mul_zero, Complex.cos_zero,
      Complex.sin_zero, mul_one, add_zero, zero_sub] using hftc
  calc
    cosineRay f2 z + z ^ 2 * cosineRay f0 z = ∫ t in Ioi (0 : ℝ), dH t := by
      dsimp only [cosineRay, dH]
      rw [integral_add hi2 (hi0.const_mul (z ^ 2)), integral_const_mul]
    _ = _ := hI

/-- No frequency division occurs in the exact identity; it includes z=0. -/
theorem cosineRay_fourfold (f0 f1 f2 f3 f4 : ℝ → ℝ)
    (hC0 : Continuous f0) (hC2 : Continuous f2) (hC4 : Continuous f4)
    (hD0 : ∀ t ∈ Ici (0 : ℝ), HasDerivAt f0 (f1 t) t)
    (hD1 : ∀ t ∈ Ici (0 : ℝ), HasDerivAt f1 (f2 t) t)
    (hD2 : ∀ t ∈ Ici (0 : ℝ), HasDerivAt f2 (f3 t) t)
    (hD3 : ∀ t ∈ Ici (0 : ℝ), HasDerivAt f3 (f4 t) t)
    (hL0 : IntegrableOn (fun t => |f0 t| * Real.exp (t / 2)) (Ioi 0))
    (hL2 : IntegrableOn (fun t => |f2 t| * Real.exp (t / 2)) (Ioi 0))
    (hL4 : IntegrableOn (fun t => |f4 t| * Real.exp (t / 2)) (Ioi 0))
    (hT0 : Tendsto (fun t => |f0 t| * Real.exp (t / 2)) atTop (𝓝 0))
    (hT1 : Tendsto (fun t => |f1 t| * Real.exp (t / 2)) atTop (𝓝 0))
    (hT2 : Tendsto (fun t => |f2 t| * Real.exp (t / 2)) atTop (𝓝 0))
    (hT3 : Tendsto (fun t => |f3 t| * Real.exp (t / 2)) atTop (𝓝 0))
    (z : ℂ) (hz : |z.im| ≤ 1 / 2) :
    z ^ 2 * (z ^ 2 * cosineRay f0 z + (f1 0 : ℂ)) =
      (f3 0 : ℂ) + cosineRay f4 z := by
  have h02 := cosineRay_second f0 f1 f2 hC0 hC2 hD0 hD1 hL0 hL2 hT0 hT1 z hz
  have h24 := cosineRay_second f2 f3 f4 hC2 hC4 hD2 hD3 hL2 hL4 hT2 hT3 z hz
  linear_combination z ^ 2 * h02 - h24

theorem cosineRay_norm_le (f : ℝ → ℝ) (hf : Continuous f)
    (hL : IntegrableOn (fun t => |f t| * Real.exp (t / 2)) (Ioi 0))
    (z : ℂ) (hz : |z.im| ≤ 1 / 2) : ‖cosineRay f z‖ ≤ jetBudget f := by
  have hi := (trig_product_integrable f hf hL z hz).1
  refine (norm_integral_le_integral_norm _).trans (integral_mono_ae hi.norm hL ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (strip_trig_bounds z hz ht.le).1 (abs_nonneg _)

/-- The exact identity plus the genuine fourth-jet integral gives the
    strip-uniform O(norm z ^ -2) error after multiplying v by z^2. -/
theorem cosineRay_error_of_fourfold
    (f0 f1 f3 f4 : ℝ → ℝ) (hC4 : Continuous f4)
    (hL4 : IntegrableOn (fun t => |f4 t| * Real.exp (t / 2)) (Ioi 0))
    (z : ℂ) (hz : |z.im| ≤ 1 / 2) (hz0 : z ≠ 0)
    (hid : z ^ 2 * (z ^ 2 * cosineRay f0 z + (f1 0 : ℂ)) =
      (f3 0 : ℂ) + cosineRay f4 z) :
    ‖z ^ 2 * cosineRay f0 z + (f1 0 : ℂ)‖ ≤
      (|f3 0| + jetBudget f4) / ‖z‖ ^ 2 := by
  have hb := cosineRay_norm_le f4 hC4 hL4 z hz
  have hn : ‖z ^ 2 * (z ^ 2 * cosineRay f0 z + (f1 0 : ℂ))‖ ≤
      |f3 0| + jetBudget f4 := by
    rw [hid]
    exact (norm_add_le _ _).trans (by simpa using add_le_add_left hb ‖(f3 0 : ℂ)‖)
  apply (le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hz0))).2
  simpa only [norm_mul, norm_pow, mul_comm] using hn

theorem scaled_cosineRay_error_of_fourfold
    (f0 f1 f3 f4 : ℝ → ℝ) (hC4 : Continuous f4)
    (hL4 : IntegrableOn (fun t => |f4 t| * Real.exp (t / 2)) (Ioi 0))
    (z c : ℂ) (hz : |z.im| ≤ 1 / 2) (hz0 : z ≠ 0)
    (hid : z ^ 2 * (z ^ 2 * cosineRay f0 z + (f1 0 : ℂ)) =
      (f3 0 : ℂ) + cosineRay f4 z) :
    ‖z ^ 2 * (2 * c * cosineRay f0 z) + 2 * c * (f1 0 : ℂ)‖ ≤
      (2 * ‖c‖ * (|f3 0| + jetBudget f4)) / ‖z‖ ^ 2 := by
  have hb := cosineRay_error_of_fourfold f0 f1 f3 f4 hC4 hL4 z hz hz0 hid
  calc
    _ = 2 * ‖c‖ * ‖z ^ 2 * cosineRay f0 z + (f1 0 : ℂ)‖ := by
      rw [show z ^ 2 * (2 * c * cosineRay f0 z) + 2 * c * (f1 0 : ℂ) =
        (2 * c) * (z ^ 2 * cosineRay f0 z + (f1 0 : ℂ)) by ring]
      simp only [norm_mul]
      norm_num
    _ ≤ 2 * ‖c‖ * ((|f3 0| + jetBudget f4) / ‖z‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

end RHFourJetDraft

/- Transient proof fragment for the actual shifted-Phi cosine consumer.
   Not compiled. No new canonical D5 declaration is proposed here.
   The owning exact check must supply the actual Phi jets, weighted L1 bounds,
   and half-line boundary limits before using the final consumer. -/


set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace RhTransient.ActualZeroCosineNonzero

open D5.S3.Weil.ZeroSum
open D5.S3.Weil.Convention
open D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData

-- Finite spectral balls on the actual natural-number presentation already
-- give arbitrarily large spectral norm. No new zero-count estimate is needed.
private theorem actual_gamma_arbitrarily_large (R : ℝ) :
    ∃ n : ℕ, R < ‖zetaZeroData.gamma n‖ := by
  obtain ⟨n, hn⟩ := (zetaZeroData.locallyFinite R).exists_notMem
  refine ⟨n, ?_⟩
  change R < spectralRadius (zetaZeroData.zero n)
  exact lt_of_not_ge hn

private theorem actual_gamma_half_strip (n : ℕ) :
    |(zetaZeroData.gamma n).im| ≤ (1 / 2 : ℝ) := by
  have hs := (zetaZeroData.zero_isNontrivial n).2
  have he : (zetaZeroData.gamma n).im =
      (1 / 2 : ℝ) - (zetaZeroData.zero n).re := by
    simp [ZeroData.gamma, spectralParameter, criticalAbscissa] <;> ring
  rw [he, abs_le]
  constructor <;> linarith [hs.1, hs.2]

-- This consumes the denominator-free fourth-jet remainder, so the final
-- discrete-zero existence proof needs no division by a complex spectral node.
private theorem actual_zero_nonzero_of_fourth_remainder
    (J0 : ℂ → ℂ) (A C : ℝ) (hA : A < 0) (hC : 0 ≤ C)
    (hrem : ∀ z : ℂ, |z.im| ≤ (1 / 2 : ℝ) →
      ‖z ^ 2 * (z ^ 2 * J0 z + (A : ℂ))‖ ≤ C) :
    ∃ n : ℕ, J0 (zetaZeroData.gamma n) ≠ 0 := by
  let d : ℝ := -A
  have hd : 0 < d := by dsimp [d]; linarith
  let R : ℝ := 1 + C / d
  obtain ⟨n, hn⟩ := actual_gamma_arbitrarily_large R
  refine ⟨n, ?_⟩
  intro hzero
  have hbound := hrem (zetaZeroData.gamma n) (actual_gamma_half_strip n)
  rw [hzero, mul_zero, zero_add, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_neg hA] at hbound
  change ‖zetaZeroData.gamma n‖ ^ 2 * d ≤ C at hbound
  have hdiv : 0 ≤ C / d := div_nonneg hC hd.le
  have hnorm : 1 < ‖zetaZeroData.gamma n‖ := by
    dsimp [R] at hn
    linarith
  have hratio : C / d < ‖zetaZeroData.gamma n‖ := by
    dsimp [R] at hn
    linarith
  have hlinear : C < ‖zetaZeroData.gamma n‖ * d :=
    (div_lt_iff₀ hd).mp hratio
  have hquadratic : 0 ≤
      ‖zetaZeroData.gamma n‖ * d * (‖zetaZeroData.gamma n‖ - 1) :=
    mul_nonneg (mul_nonneg (norm_nonneg _) hd.le) (by linarith)
  nlinarith

end RhTransient.ActualZeroCosineNonzero

#print axioms D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft.translated_phi_jets
#print axioms D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft.phi_derivative_log_two_negative
#print axioms RHFourJetDraft.cosineRay_fourfold

namespace D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft
open Real Set MeasureTheory Filter
open scoped Topology
open D5.S3.Analytic.Fourier.ThetaDifferentialKernel
open D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
open RHFourJetDraft

/-- A literal shifted original theta kernel has nonzero cosine transform at
    an actual zeta spectral node. No signed-form radical claim is inferred. -/
theorem actual_shifted_phi_spectrum_nonzero :
    ∃ n : ℕ, (∫ t : ℝ in Ioi 0,
      (romikPhi (Real.log 2 / 2 + t) : ℂ) *
        Complex.cos (zetaZeroData.gamma n * (t : ℂ))) ≠ 0 := by
  let a : ℝ := Real.log 2 / 2
  have ha : 0 < a := by
    exact div_pos (Real.log_pos (by norm_num : (1:ℝ)<2)) (by norm_num)
  let f : ℕ → ℝ → ℝ := fun k t => fullJet k (a+t)
  have hC (k : ℕ) : Continuous (f k) :=
    (fullJet_continuous k).comp (continuous_const.add continuous_id)
  have hD (k : ℕ) : ∀ t ∈ Ici (0:ℝ), HasDerivAt (f k) (f (k+1) t) t := by
    intro t ht
    convert! (fullJet_deriv k (a+t)).comp t ((hasDerivAt_id t).const_add a) using 1 <;>
      simp only [f, add_comm, mul_one]
  have hL (k : ℕ) : IntegrableOn
      (fun t : ℝ => |f k t| * exp (t/2)) (Ioi 0) := by
    apply ((translated_phi_jets k ha.le).1).congr_fun ?_ measurableSet_Ioi
    intro t ht
    have htpos : 0 < t := ht
    dsimp only [f]
    rw [fullJet_eq_phi_derivative k (by linarith : 0 < a+t)]
    ring
  have hT (k : ℕ) : Tendsto
      (fun t : ℝ => |f k t| * exp (t/2)) atTop (𝓝 0) := by
    apply ((translated_phi_jets k ha.le).2).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    dsimp only [f]
    rw [fullJet_eq_phi_derivative k (by linarith : 0 < a+t)]
    ring
  have hA : f 1 0 < 0 := by
    change fullJet 1 (a+0) < 0
    rw [add_zero, fullJet_eq_phi_derivative 1 ha]
    simpa only [iteratedDeriv_one] using phi_derivative_log_two_negative
  have hbudget : 0 ≤ jetBudget (f 4) :=
    integral_nonneg (fun t => mul_nonneg (abs_nonneg _) (exp_pos _).le)
  have hnz : ∃ n : ℕ, cosineRay (f 0) (zetaZeroData.gamma n) ≠ 0 := by
    apply RhTransient.ActualZeroCosineNonzero.actual_zero_nonzero_of_fourth_remainder
      (cosineRay (f 0)) (f 1 0) (|f 3 0|+jetBudget (f 4)) hA
      (add_nonneg (abs_nonneg _) hbudget)
    intro z hz
    have hid := cosineRay_fourfold (f 0) (f 1) (f 2) (f 3) (f 4)
      (hC 0) (hC 2) (hC 4) (hD 0) (hD 1) (hD 2) (hD 3)
      (hL 0) (hL 2) (hL 4) (hT 0) (hT 1) (hT 2) (hT 3) z hz
    rw [hid]
    exact (norm_add_le _ _).trans (by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using
        add_le_add (le_refl |f 3 0|) (cosineRay_norm_le (f 4) (hC 4) (hL 4) z hz))
  obtain ⟨n, hn⟩ := hnz
  refine ⟨n, ?_⟩
  have he : cosineRay (f 0) (zetaZeroData.gamma n) =
      ∫ t : ℝ in Ioi 0, (romikPhi (a+t) : ℂ) *
        Complex.cos (zetaZeroData.gamma n * (t : ℂ)) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change (fullJet 0 (a+t) : ℂ) * _ = _
    rw [fullJet_zero_eq_phi (add_nonneg ha.le (le_of_lt ht))]
  exact he ▸ hn

#print axioms actual_shifted_phi_spectrum_nonzero
end D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft

namespace D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft

open Set MeasureTheory
open D5.S3.Analytic.Fourier.ThetaDifferentialKernel
open D5.S3.Analytic.Fourier.XiThetaTransform
open D5.S3.Zeros.Jensen.NormalizedJensenDegreeLowering
open D5.S3.Zeros.Jensen.SourceThetaMomentBounds
open D5.S3.Zeros.CompletedZeta
open D5.S3.Weil.Convention D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData

/-- The original half-line cosine transform is exactly one half of xi at
    every complex frequency, with genuine absolute integrability. -/
theorem phi_halfline_cosine_eq_xi (z : ℂ) :
    IntegrableOn (fun t : ℝ => (romikPhi t : ℂ)*Complex.cos (z*(t:ℂ))) (Ioi 0) ∧
    2*(∫ t : ℝ in Ioi 0, (romikPhi t : ℂ)*Complex.cos (z*(t:ℂ))) =
      xiReading ((1/2:ℂ)+Complex.I*z) := by
  let F : ℝ → ℂ := fun t =>
    (sourceThetaKernel t : ℂ)*Complex.exp (Complex.I*z*(t:ℂ))
  have hi : Integrable F := source_theta_fourier_integrable z
  have hp : IntegrableOn F (Ioi 0) := hi.integrableOn
  have hm : IntegrableOn (fun t : ℝ => F (-t)) (Ioi 0) := by
    apply ((source_theta_fourier_integrable (-z)).integrableOn).congr_fun ?_
      measurableSet_Ioi
    intro t _
    dsimp only [F]
    rw [source_theta_even]
    push_cast
    congr 2
    ring
  have he : Set.EqOn (fun t : ℝ => F (-t)+F t)
      (fun t : ℝ => 2*((romikPhi t : ℂ)*Complex.cos (z*(t:ℂ)))) (Ioi 0) := by
    intro t _
    dsimp only [F]
    rw [source_theta_even, romikPhi_eq_source]
    push_cast
    rw [show Complex.I*z* -(t:ℂ) = -(z*(t:ℂ))*Complex.I by ring,
      show Complex.I*z*(t:ℂ) = (z*(t:ℂ))*Complex.I by ring]
    calc
      _ = (sourceThetaKernel t : ℂ)*
          (Complex.exp ((z*(t:ℂ))*Complex.I)+
            Complex.exp (-(z*(t:ℂ))*Complex.I)) := by ring
      _ = (sourceThetaKernel t : ℂ)*(2*Complex.cos (z*(t:ℂ))) := by
        rw [Complex.two_cos]
      _ = _ := by ring
  have hsumInt : IntegrableOn (fun t : ℝ => (1/2:ℂ)*(F (-t)+F t)) (Ioi 0) :=
    (hm.add hp).const_mul (1/2:ℂ)
  have hcos : IntegrableOn
      (fun t : ℝ => (romikPhi t : ℂ)*Complex.cos (z*(t:ℂ))) (Ioi 0) := by
    apply hsumInt.congr_fun ?_ measurableSet_Ioi
    intro t ht
    change (1/2:ℂ)*(F (-t)+F t) = _
    have het := he ht
    dsimp only at het
    rw [het]
    ring
  refine ⟨hcos, ?_⟩
  calc
    2*(∫ t : ℝ in Ioi 0, (romikPhi t : ℂ)*Complex.cos (z*(t:ℂ))) =
        ∫ t : ℝ in Ioi 0, 2*((romikPhi t : ℂ)*Complex.cos (z*(t:ℂ))) :=
      (integral_const_mul _ _).symm
    _ = ∫ t : ℝ in Ioi 0, F (-t)+F t :=
      setIntegral_congr_fun measurableSet_Ioi (fun t ht => (he ht).symm)
    _ = (∫ t : ℝ in Ioi 0, F (-t))+(∫ t : ℝ in Ioi 0, F t) :=
      integral_add hm hp
    _ = (∫ t : ℝ in Iic 0, F t)+(∫ t : ℝ in Ioi 0, F t) := by
      rw [integral_comp_neg_Ioi]
      simp only [neg_zero]
    _ = ∫ t : ℝ, F t :=
      intervalIntegral.integral_Iic_add_Ioi hi.integrableOn hp
    _ = xiReading ((1/2:ℂ)+Complex.I*z) := source_theta_fourier_eq_xi z

private theorem actual_zero_xi_reading (n : ℕ) :
    xiReading (zetaZeroData.zero n) = 0 := by
  have hz := zetaZeroData_isNontrivial n
  have h0 : zetaZeroData.zero n ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.zero_re] at hre
    linarith [hz.2.1]
  have h1 : zetaZeroData.zero n ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.one_re] at hre
    linarith [hz.2.2]
  have hc : completedZetaReading (zetaZeroData.zero n) = 0 :=
    Zeta23.RvM.completedRiemannZeta_eq_zero_iff.mpr hz
  rw [xi_reading_eq_completed_zeta h0 h1, hc, mul_zero]

/-- The unshifted original kernel vanishes spectrally at every actual
    nontrivial zero, even when its spectral parameter is not real. -/
theorem actual_unshifted_phi_spectrum_zero (n : ℕ) :
    (∫ t : ℝ in Ioi 0, (romikPhi t : ℂ)*
      Complex.cos (zetaZeroData.gamma n*(t:ℂ))) = 0 := by
  have h := (phi_halfline_cosine_eq_xi (zetaZeroData.gamma n)).2
  have hr : (1/2:ℂ)+Complex.I*zetaZeroData.gamma n = zetaZeroData.zero n := by
    simpa only [criticalAbscissa, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using
      (zetaZeroData.zero_eq_critical_add_I_mul_gamma n).symm
  rw [hr, actual_zero_xi_reading n] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

end D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft

namespace D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft

open Real Set MeasureTheory Filter
open scoped Topology FourierTransform
open D5.S3.Analytic.Fourier.ThetaDifferentialKernel
open D5.S3.Zeros.Jensen.SourceThetaMomentBounds
open D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open private psiSecond_eq cexp_deriv from
  D5.S3.Analytic.Fourier.XiThetaTransform

open D5.S3.Zeros.Jensen.NormalizedJensenDegreeLowering

private def literalGaussian (a x : ℝ) : ℂ :=
  (exp ((9 / 2 : ℝ) * a - exp (2 * a) * x) : ℂ)

private def gaussianRay (a t : ℝ) : ℝ :=
  (Real.pi ^ (1 / 4 : ℝ) / 4) *
    (fullJet 0 (a+t/2) + (3/2:ℝ)*psi (a+t/2) - 3*psiFirst (a+t/2))

private def gaussianRayFirst (a t : ℝ) : ℝ :=
  (Real.pi ^ (1 / 4 : ℝ) / 8) *
    (fullJet 1 (a+t/2) + (3/2:ℝ)*psiFirst (a+t/2) - 3*psiSecond (a+t/2))

private theorem gaussianRay_deriv (a t : ℝ) :
    HasDerivAt (gaussianRay a) (gaussianRayFirst a t) t := by
  have hb : HasDerivAt (fun t : ℝ => a+t/2) (1/2:ℝ) t := by
    simpa using ((hasDerivAt_id t).div_const 2).const_add a
  convert! ((((fullJet_deriv 0 (a+t/2)).comp t hb).add
      (((hasDerivAt_psi (a+t/2)).comp t hb).const_mul (3/2:ℝ))).sub
      (((hasDerivAt_psiFirst (a+t/2)).comp t hb).const_mul 3)).const_mul
      (Real.pi ^ (1/4:ℝ) / 4) using 1 <;>
    simp only [gaussianRay, gaussianRayFirst, Nat.reduceAdd] <;> ring

private theorem gaussianRay_continuous (a : ℝ) : Continuous (gaussianRay a) :=
  continuous_iff_continuousAt.mpr (fun t => (gaussianRay_deriv a t).continuousAt)

private theorem gaussianRayFirst_continuous (a : ℝ) : Continuous (gaussianRayFirst a) := by
  have hs : Continuous psiSecond := by
    rw [show psiSecond = fun x => sourceThetaKernel x + psi x / 4 from funext psiSecond_eq]
    exact source_theta_continuous.add
      ((continuous_iff_continuousAt.mpr
        (fun t => (hasDerivAt_psi t).continuousAt)).div_const 4)
  unfold gaussianRayFirst
  apply continuous_const.mul
  exact (((fullJet_continuous 1).comp (by fun_prop)).add
      (continuous_const.mul ((continuous_iff_continuousAt.mpr
        (fun t => (hasDerivAt_psiFirst t).continuousAt)).comp (by fun_prop)))).sub
      (continuous_const.mul (hs.comp (by fun_prop)))

private theorem gaussianRay_eq_series {a t : ℝ} (hb : 0 ≤ a+t/2) :
    gaussianRay a t = Real.pi ^ (9/4:ℝ) * exp ((9/2:ℝ)*(a+t/2)) *
      thetaSeries 4 (exp (2*(a+t/2))) := by
  let b : ℝ := a+t/2
  have hpi : Real.pi ^ (9/4:ℝ) = Real.pi ^ (1/4:ℝ)*Real.pi^2 := by
    rw [← Real.rpow_natCast Real.pi 2, ← Real.rpow_add Real.pi_pos]
    norm_num
  have he : exp (b/2)*exp (2*b)^2 = exp ((9/2:ℝ)*b) := by
    rw [← Real.exp_nat_mul, ← exp_add]
    congr 1
    ring
  rw [gaussianRay, fullJet_zero_eq_phi hb, romikPhi,
    omega_eq_series (exp_pos _), psi_eq_series, psiFirst]
  change (Real.pi ^ (1/4:ℝ)/4)*
    (2*exp (b/2)*(2*Real.pi^2*exp (2*b)^2*thetaSeries 4 (exp (2*b)) -
        3*Real.pi*exp (2*b)*thetaSeries 2 (exp (2*b))) +
      (3/2:ℝ)*(exp (b/2)*thetaSeries 0 (exp (2*b))) -
      3*(exp (b/2)*(thetaSeries 0 (exp (2*b))/2 -
        2*Real.pi*exp (2*b)*thetaSeries 2 (exp (2*b))))) = _
  calc
    _ = (Real.pi ^ (1/4:ℝ)*Real.pi^2)*
        (exp (b/2)*exp (2*b)^2)*thetaSeries 4 (exp (2*b)) := by ring
    _ = _ := by rw [he, ← hpi]

private theorem literalGaussian_fullHasSum (a t : ℝ) :
    HasSum (fun n : ℕ => physicalTerm (literalGaussian a) n (Real.pi*exp t))
      ((exp ((9/2:ℝ)*a)*thetaSeries 4 (exp (2*(a+t/2))) : ℝ) : ℂ) := by
  have hs := Complex.ofRealCLM.hasSum
    ((thetaSeries_summable 4 (exp_pos (2*(a+t/2)))).hasSum.mul_left
      (exp ((9/2:ℝ)*a)))
  have he : exp (2*a)*exp t = exp (2*(a+t/2)) := by
    rw [← exp_add]
    congr 1
    ring
  have hterm (n : ℕ) :
      physicalTerm (literalGaussian a) n (Real.pi*exp t) =
        ((exp ((9/2:ℝ)*a)*
          (((n:ℝ)+1)^4*exp (-Real.pi*((n:ℝ)+1)^2*exp (2*(a+t/2)))) : ℝ) : ℂ) := by
    have hx : exp ((9/2:ℝ)*a - exp (2*a)*
          (((n:ℝ)+1)^2*(Real.pi*exp t))) =
        exp ((9/2:ℝ)*a)*exp (-Real.pi*((n:ℝ)+1)^2*exp (2*(a+t/2))) := by
      rw [sub_eq_add_neg, exp_add]
      congr 1
      congr 1
      calc
        -(exp (2*a)*(((n:ℝ)+1)^2*(Real.pi*exp t))) =
            -Real.pi*((n:ℝ)+1)^2*(exp (2*a)*exp t) := by ring
        _ = _ := by rw [he]
    simp only [physicalTerm, literalGaussian, Nat.cast_add, Nat.cast_one]
    rw [hx]
    push_cast
    ring
  convert! hs using 1
  funext n
  exact hterm n

private theorem literalGaussian_fullTheta (a t : ℝ) :
    fullTheta (literalGaussian a) (Real.pi*exp t) =
      ((exp ((9/2:ℝ)*a)*thetaSeries 4 (exp (2*(a+t/2))) : ℝ) : ℂ) :=
  (literalGaussian_fullHasSum a t).tsum_eq

private theorem literalGaussian_actualProfile {a : ℝ} (ha : 0 ≤ a) :
    actualGammaProfile (literalGaussian a) =
      fun t : ℝ => if 0 ≤ t then (gaussianRay a t : ℂ) else 0 := by
  funext t
  by_cases ht : 0 ≤ t
  · have hs : (Real.pi*exp t) ^ (9/4:ℝ)*exp ((9/2:ℝ)*a) =
        Real.pi ^ (9/4:ℝ)*exp ((9/2:ℝ)*(a+t/2)) := by
      rw [Real.mul_rpow Real.pi_pos.le (exp_pos _).le, ← Real.exp_mul,
        mul_assoc, ← exp_add]
      congr 2 <;> ring
    rw [actualGammaProfile, if_pos ht, if_pos ht,
      literalGaussian_fullTheta, gaussianRay_eq_series (by linarith)]
    simpa only [Complex.ofReal_mul, mul_assoc] using
      congrArg Complex.ofReal (congrArg
        (fun v : ℝ => v*thetaSeries 4 (exp (2*(a+t/2)))) hs)
  · simp only [actualGammaProfile, if_neg ht]

private theorem halfJet_bound (r : ℕ) {a t : ℝ}
    (ha : 0 ≤ a) (ht : 0 ≤ t) :
    |fullJet r (a+t/2)| ≤ fullConstant r*exp (-t/2) := by
  have hb : 0 ≤ a+t/2 := by linarith
  calc
    _ ≤ exp ((a+t/2)/2)*|fullJet r (a+t/2)| :=
      le_mul_of_one_le_left (abs_nonneg _) (one_le_exp (by linarith))
    _ ≤ fullConstant r*exp (-(a+t/2)) := full_bound r hb
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (exp_le_exp.mpr (by linarith)) (fullConstant_nonneg r)

private def gaussianRaySize : ℝ :=
  (Real.pi ^ (1/4:ℝ)/4)*((11/2:ℝ)*fullConstant 0)

private def gaussianRayFirstSize : ℝ :=
  (Real.pi ^ (1/4:ℝ)/8)*(fullConstant 1+(21/4:ℝ)*fullConstant 0)

private theorem gaussianRaySize_nonneg : 0 ≤ gaussianRaySize := by
  dsimp [gaussianRaySize]
  exact mul_nonneg (by positivity) (mul_nonneg (by norm_num) (fullConstant_nonneg 0))

private theorem gaussianRayFirstSize_nonneg : 0 ≤ gaussianRayFirstSize := by
  dsimp [gaussianRayFirstSize]
  exact mul_nonneg (by positivity)
    (add_nonneg (fullConstant_nonneg 1)
      (mul_nonneg (by norm_num) (fullConstant_nonneg 0)))

private theorem gaussianRay_bounds {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    |gaussianRay a t| ≤ gaussianRaySize*exp (-t/2) ∧
      |gaussianRayFirst a t| ≤ gaussianRayFirstSize*exp (-t/2) := by
  let b : ℝ := a+t/2
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have h0 := halfJet_bound 0 ha ht
  have h1 := halfJet_bound 1 ha ht
  have hpsi := psi_bounds hb
  have hphi : sourceThetaKernel b = fullJet 0 b :=
    (fullJet_zero_eq_phi hb).trans (romikPhi_eq_source b) |>.symm
  rw [hphi] at hpsi
  have hpsi0 : |psi b| ≤ fullConstant 0*exp (-t/2) :=
    hpsi.1.trans ((le_abs_self _).trans h0)
  have hpsi1 : |psiFirst b| ≤ fullConstant 0*exp (-t/2) :=
    hpsi.2.trans ((le_abs_self _).trans h0)
  have hpsi2 : |psiSecond b| ≤ (5/4:ℝ)*fullConstant 0*exp (-t/2) := by
    rw [psiSecond_eq, hphi]
    have hh := abs_add_le (fullJet 0 b) (psi b/4)
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<4)] at hh
    nlinarith [hh]
  have hsum0 : |fullJet 0 b+(3/2:ℝ)*psi b-3*psiFirst b| ≤
      |fullJet 0 b+(3/2:ℝ)*psi b|+|3*psiFirst b| := by
    simpa using abs_sub_le (fullJet 0 b+(3/2:ℝ)*psi b) 0 (3*psiFirst b)
  have hsum0a := abs_add_le (fullJet 0 b) ((3/2:ℝ)*psi b)
  have hsum1 : |fullJet 1 b+(3/2:ℝ)*psiFirst b-3*psiSecond b| ≤
      |fullJet 1 b+(3/2:ℝ)*psiFirst b|+|3*psiSecond b| := by
    simpa using abs_sub_le (fullJet 1 b+(3/2:ℝ)*psiFirst b) 0 (3*psiSecond b)
  have hsum1a := abs_add_le (fullJet 1 b) ((3/2:ℝ)*psiFirst b)
  simp only [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<3/2),
    abs_of_pos (by norm_num : (0:ℝ)<3)] at hsum0 hsum0a hsum1 hsum1a
  constructor
  · rw [gaussianRay, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ Real.pi^(1/4:ℝ)/4)]
    dsimp only [gaussianRaySize]
    apply (mul_le_mul_of_nonneg_left
      (show |fullJet 0 b+(3/2:ℝ)*psi b-3*psiFirst b| ≤
        (11/2:ℝ)*fullConstant 0*exp (-t/2) by linarith)
      (by positivity : 0 ≤ Real.pi^(1/4:ℝ)/4)).trans_eq
    ring
  · rw [gaussianRayFirst, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ Real.pi^(1/4:ℝ)/8)]
    dsimp only [gaussianRayFirstSize]
    apply (mul_le_mul_of_nonneg_left
      (show |fullJet 1 b+(3/2:ℝ)*psiFirst b-3*psiSecond b| ≤
        (fullConstant 1+(21/4:ℝ)*fullConstant 0)*exp (-t/2) by nlinarith)
      (by positivity : 0 ≤ Real.pi^(1/4:ℝ)/8)).trans_eq
    ring

/- The actual envelopes pay L1 and the true endpoint; no form-domain premise. -/
private theorem gaussianRay_domains {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun t : ℝ => (gaussianRay a t : ℂ)) (Ioi 0) ∧
    IntegrableOn (fun t : ℝ => (gaussianRayFirst a t : ℂ)) (Ioi 0) ∧
    Tendsto (fun t : ℝ => (gaussianRay a t : ℂ)) atTop (𝓝 0) ∧
    Tendsto (fun t : ℝ => (gaussianRayFirst a t : ℂ)) atTop (𝓝 0) := by
  have hexp : IntegrableOn (fun t : ℝ => exp (-t/2)) (Ioi 0) := by
    convert! integrableOn_exp_mul_Ioi (show (-1/2:ℝ)<0 by norm_num) 0 using 1
    funext t
    congr 1
    ring
  have htop : Tendsto (fun t : ℝ => exp (-t/2)) atTop (𝓝 0) := by
    have hh := tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (show (-1/2:ℝ)<0 by norm_num))
    convert! hh using 1 <;> ext t <;> dsimp only [Function.comp_apply, id_eq] <;> congr 1 <;> ring
  have htail (f : ℝ → ℝ) (hf : Continuous f) (M : ℝ)
      (hbound : ∀ t, 0 ≤ t → |f t| ≤ M*exp (-t/2)) :
      IntegrableOn (fun t : ℝ => (f t : ℂ)) (Ioi 0) ∧
        Tendsto (fun t : ℝ => (f t : ℂ)) atTop (𝓝 0) := by
    constructor
    · apply (hexp.const_mul M).mono'
        (Complex.continuous_ofReal.comp hf).aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs] using hbound t ht.le
    · apply squeeze_zero_norm' (a := fun t : ℝ => M*exp (-t/2))
      · filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
        simpa only [Complex.norm_real, Real.norm_eq_abs] using hbound t ht
      · simpa only [mul_zero] using htop.const_mul M
  have h0 := htail (gaussianRay a) (gaussianRay_continuous a) gaussianRaySize
    (fun t ht => (gaussianRay_bounds ha ht).1)
  have h1 := htail (gaussianRayFirst a) (gaussianRayFirst_continuous a) gaussianRayFirstSize
    (fun t ht => (gaussianRay_bounds ha ht).2)
  exact ⟨h0.1, h1.1, h0.2, h1.2⟩

private theorem literalGaussian_profile_l1 {a : ℝ} (ha : 0 ≤ a) :
    Integrable (actualGammaProfile (literalGaussian a)) volume := by
  rw [literalGaussian_actualProfile ha]
  change Integrable ((Ici (0:ℝ)).indicator (fun t => (gaussianRay a t : ℂ))) volume
  exact (integrable_indicator_iff measurableSet_Ici).2
    ((integrableOn_Ici_iff_integrableOn_Ioi).mpr (gaussianRay_domains ha).1)

private theorem literalGaussian_fourier_ray {a : ℝ} (ha : 0 ≤ a) (ξ : ℝ) :
    unitarySourceFourier (actualGammaProfile (literalGaussian a)) ξ =
      ((Real.sqrt (2*Real.pi) : ℂ))⁻¹ *
        ∫ t : ℝ in Ioi 0, (gaussianRay a t : ℂ)*sourcePhase ξ t := by
  rw [unitarySourceFourier_eq_integral, literalGaussian_actualProfile ha]
  congr 1
  have he : (fun t : ℝ => sourcePhase ξ t *
      (if 0 ≤ t then (gaussianRay a t : ℂ) else 0)) =
      (Ici (0:ℝ)).indicator (fun t => (gaussianRay a t : ℂ)*sourcePhase ξ t) := by
    funext t
    by_cases ht : 0 ≤ t <;> simp [ht, mul_comm]
  rw [he, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]

/- One actual half-line IBP. Its endpoint is -u_a(0), retained literally. -/
private theorem gaussianRay_fourier_ibp {a : ℝ} (ha : 0 ≤ a) (ξ : ℝ) :
    (Complex.I*(ξ:ℂ))*
        (∫ t : ℝ in Ioi 0, (gaussianRay a t : ℂ)*sourcePhase ξ t) =
      -(gaussianRay a 0 : ℂ) -
        ∫ t : ℝ in Ioi 0, (gaussianRayFirst a t : ℂ)*sourcePhase ξ t := by
  let w : ℂ := Complex.I*(ξ:ℂ)
  obtain ⟨hu, hu', htop, _⟩ := gaussianRay_domains ha
  have hp : Continuous (sourcePhase ξ) := by unfold sourcePhase; fun_prop
  have hint (f : ℝ → ℂ) (hf : IntegrableOn f (Ioi (0:ℝ))) :
      IntegrableOn (fun t => f t*sourcePhase ξ t) (Ioi 0) := by
    exact hf.mul_bdd hp.aestronglyMeasurable
      (Eventually.of_forall fun t => (sourcePhase_norm ξ t).le)
  have hmul : IntegrableOn
      (fun t : ℝ => (gaussianRay a t : ℂ)*(w*sourcePhase ξ t)) (Ioi 0) := by
    have he : (fun t : ℝ => (gaussianRay a t : ℂ)*(w*sourcePhase ξ t)) =
        (fun t : ℝ => w*((gaussianRay a t : ℂ)*sourcePhase ξ t)) := by
      funext t
      ring
    rw [he]
    exact (hint _ hu).const_mul w
  have hzero : Tendsto
      (fun t : ℝ => (gaussianRay a t : ℂ)*sourcePhase ξ t)
      (𝓝[>] 0) (𝓝 (gaussianRay a 0 : ℂ)) := by
    have hc : Continuous (fun t : ℝ => (gaussianRay a t : ℂ)*sourcePhase ξ t) :=
      (Complex.continuous_ofReal.comp (gaussianRay_continuous a)).mul hp
    simpa only [Function.comp_apply, Pi.mul_apply, sourcePhase, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
      using (hc.continuousAt (x := 0)).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  have htopMul : Tendsto
      (fun t : ℝ => (gaussianRay a t : ℂ)*sourcePhase ξ t) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun t => ‖(gaussianRay a t : ℂ)‖)
    · exact Eventually.of_forall fun t => by
        simp only [norm_mul, sourcePhase_norm, mul_one, le_refl]
    · simpa only [norm_zero] using htop.norm
  have h := integral_Ioi_mul_deriv_eq_deriv_mul
    (fun t _ => (gaussianRay_deriv a t).ofReal_comp)
    (fun t _ => by
      dsimp only [sourcePhase, w]
      convert! (((hasDerivAt_id (t : ℂ)).const_mul (Complex.I*(ξ:ℂ))).cexp).comp_ofReal using 1 <;> simp <;> ring)
    hmul (hint _ hu') hzero htopMul
  have he : (∫ t : ℝ in Ioi 0,
      (gaussianRay a t : ℂ)*(w*sourcePhase ξ t)) =
      w*(∫ t : ℝ in Ioi 0, (gaussianRay a t : ℂ)*sourcePhase ξ t) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    ring
  simpa only [he, zero_sub, w] using h

private theorem gaussianRay_fourier_norm_le {a : ℝ} (ha : 0 ≤ a)
    (ξ : ℝ) (hξ : ξ ≠ 0) :
    ‖∫ t : ℝ in Ioi 0, (gaussianRay a t : ℂ)*sourcePhase ξ t‖ ≤
      (|gaussianRay a 0|+∫ t : ℝ in Ioi 0, |gaussianRayFirst a t|)/|ξ| := by
  have hJ : ‖∫ t : ℝ in Ioi 0,
      (gaussianRayFirst a t : ℂ)*sourcePhase ξ t‖ ≤
      ∫ t : ℝ in Ioi 0, |gaussianRayFirst a t| := by
    simpa only [norm_mul, sourcePhase_norm, mul_one,
      Complex.norm_real, Real.norm_eq_abs] using
      norm_integral_le_integral_norm
        (μ := volume.restrict (Ioi (0:ℝ)))
        (fun t : ℝ => (gaussianRayFirst a t : ℂ)*sourcePhase ξ t)
  apply (le_div_iff₀ (abs_pos.mpr hξ)).2
  calc
    _ = ‖(Complex.I*(ξ:ℂ))*
        (∫ t : ℝ in Ioi 0, (gaussianRay a t : ℂ)*sourcePhase ξ t)‖ := by
      simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      ring
    _ = ‖-(gaussianRay a 0 : ℂ)-
        ∫ t : ℝ in Ioi 0, (gaussianRayFirst a t : ℂ)*sourcePhase ξ t‖ :=
      congrArg norm (gaussianRay_fourier_ibp ha ξ)
    _ ≤ ‖-(gaussianRay a 0 : ℂ)‖+
        ‖∫ t : ℝ in Ioi 0, (gaussianRayFirst a t : ℂ)*sourcePhase ξ t‖ := norm_sub_le _ _
    _ ≤ _ := by
      simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs]
      linarith only [hJ]

/- Actual Fourier continuity, uniform low bound and B/|xi| high bound.
   No corresponding Fourier estimate appears as a hypothesis. -/
theorem literalGaussian_fourier_decay {a : ℝ} (ha : 0 ≤ a) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      Continuous (unitarySourceFourier (actualGammaProfile (literalGaussian a))) ∧
      (∀ ξ : ℝ, ‖unitarySourceFourier (actualGammaProfile (literalGaussian a)) ξ‖ ≤ A) ∧
      (∀ ξ : ℝ, ξ ≠ 0 →
        ‖unitarySourceFourier (actualGammaProfile (literalGaussian a)) ξ‖ ≤ B/|ξ|) := by
  let N : ℝ := (Real.sqrt (2*Real.pi))⁻¹
  let A : ℝ := N*(∫ t : ℝ in Ioi 0, |gaussianRay a t|)
  let B : ℝ := N*(|gaussianRay a 0|+∫ t : ℝ in Ioi 0, |gaussianRayFirst a t|)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hnorm : ‖((Real.sqrt (2*Real.pi) : ℂ))⁻¹‖ = N := by
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), N]
  refine ⟨A, B, mul_nonneg hN (integral_nonneg fun _ => abs_nonneg _),
    mul_nonneg hN (add_nonneg (abs_nonneg _) (integral_nonneg fun _ => abs_nonneg _)),
    ?_, ?_, ?_⟩
  · unfold unitarySourceFourier
    exact continuous_const.mul
      ((Zeta23.EF.continuous_fourier_of_integrable
        (literalGaussian_profile_l1 ha)).comp (by fun_prop))
  · intro ξ
    rw [literalGaussian_fourier_ray ha ξ, norm_mul, hnorm]
    apply mul_le_mul_of_nonneg_left _ hN
    simpa only [norm_mul, sourcePhase_norm, mul_one,
      Complex.norm_real, Real.norm_eq_abs] using norm_integral_le_integral_norm
        (μ := volume.restrict (Ioi (0:ℝ)))
        (fun t : ℝ => (gaussianRay a t : ℂ)*sourcePhase ξ t)
  · intro ξ hξ
    rw [literalGaussian_fourier_ray ha ξ, norm_mul, hnorm]
    calc
      _ ≤ N*((|gaussianRay a 0|+
          ∫ t : ℝ in Ioi 0, |gaussianRayFirst a t|)/|ξ|) :=
        mul_le_mul_of_nonneg_left (gaussianRay_fourier_norm_le ha ξ hξ) hN
      _ = B/|ξ| := by dsimp [B]; ring

open private logarithmic_envelope from
  D5.S3.Weil.BurnolGram.SameWindowLogarithmicError
open private actual_gamma_log_growth from
  D5.S3.Weil.ZetaGamma.LogarithmicFormContinuity
open private gammaRatio gammaDensity from
  D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample

/- The actual physical Gaussian belongs to the literal Gamma form domain.
   All Fourier continuity and decay hypotheses above are now discharged. -/
theorem literalGaussian_originalGammaFormDomain {a : ℝ} (ha : 0 ≤ a) (c : ℝ) :
    originalGammaFormDomain c (literalGaussian a) := by
  obtain ⟨A, B, hA, hB, hfreq, hlow, hhigh⟩ := literalGaussian_fourier_decay ha
  let U := unitarySourceFourier (actualGammaProfile (literalGaussian a))
  let W : ℝ → ℝ := fun ξ => 1 + Real.log (1 + |ξ|)
  have hlog : Integrable (fun ξ : ℝ => W ξ * ‖U ξ‖ ^ 2) :=
    (logarithmic_envelope U hfreq A B 1 hA hB (by norm_num) hlow hhigh).1
  obtain ⟨C, hC, hsymbol⟩ := actual_gamma_log_growth
  let K : ℝ := (2 / Real.sqrt Real.pi) * (C * (1 + Real.log 2)) +
    1 + 4 * Real.sqrt Real.pi + |c|
  have hsqrt : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hweight (ξ : ℝ) :
      |Symbol.gammaWeight ξ + c| ≤ K * W ξ := by
    have hW : 1 ≤ W ξ := by
      dsimp [W]
      linarith [Real.log_nonneg (show 1 ≤ 1 + |ξ| by linarith [abs_nonneg ξ])]
    have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    have hlogξ : 0 ≤ Real.log (1 + |ξ|) :=
      Real.log_nonneg (by linarith [abs_nonneg ξ])
    have hscale : W (2 * ξ) ≤ (1 + Real.log 2) * W ξ := by
      have hh : Real.log (1 + |2 * ξ|) ≤
          Real.log 2 + Real.log (1 + |ξ|) := by
        calc
          _ ≤ Real.log (2 * (1 + |ξ|)) :=
            Real.log_le_log (by positivity)
              (by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith)
          _ = _ := Real.log_mul (by norm_num) (by positivity)
      dsimp [W]
      nlinarith [mul_nonneg hlog2 hlogξ]
    have hd : gammaDensity ξ = 2 * Real.pi * Zeta23.mu (2 * ξ) := by
      have harg : (1 / 4 : ℂ) + Complex.I * ((2 * ξ : ℝ) : ℂ) / 2 =
          ((((1 : ℝ) / 4 : ℝ) : ℂ) + Complex.I * (ξ : ℂ)) := by
        push_cast
        ring
      dsimp [gammaDensity, Zeta23.mu]
      rw [harg]
      field_simp [Real.pi_ne_zero]
      <;> ring
    have hR0 : 0 ≤ gammaRatio ξ := by dsimp [gammaRatio]; positivity
    have hR1 : gammaRatio ξ ≤ 1 := by
      dsimp [gammaRatio]
      exact (div_le_one (by positivity : 0 < ξ ^ 2 + 25 / 16)).2 (by linarith)
    have hD : |gammaDensity ξ| ≤ C * ((1 + Real.log 2) * W ξ) := by
      rw [hd]
      exact (hsymbol (2 * ξ)).trans (mul_le_mul_of_nonneg_left hscale hC.le)
    have hRD : |gammaRatio ξ * gammaDensity ξ| ≤
        C * ((1 + Real.log 2) * W ξ) := by
      rw [abs_mul, abs_of_nonneg hR0]
      exact (mul_le_of_le_one_left (abs_nonneg _) hR1).trans hD
    have hconst : 0 ≤ 1 + 4 * Real.sqrt Real.pi := by positivity
    calc
      _ ≤ |(2 / Real.sqrt Real.pi) * (gammaRatio ξ * gammaDensity ξ)| +
          |1 + 4 * Real.sqrt Real.pi + c| := by
        simpa only [Symbol.gammaWeight, add_assoc] using
          abs_add_le ((2 / Real.sqrt Real.pi) * (gammaRatio ξ * gammaDensity ξ))
            (1 + 4 * Real.sqrt Real.pi + c)
      _ ≤ (2 / Real.sqrt Real.pi) *
          (C * ((1 + Real.log 2) * W ξ)) +
          (1 + 4 * Real.sqrt Real.pi + |c|) := by
        apply add_le_add
        · rw [abs_mul, abs_of_pos (div_pos (by norm_num) hsqrt)]
          exact mul_le_mul_of_nonneg_left hRD (by positivity)
        · exact (abs_add_le _ _).trans_eq (by rw [abs_of_nonneg hconst])
      _ ≤ (2 / Real.sqrt Real.pi) *
          (C * ((1 + Real.log 2) * W ξ)) +
          (1 + 4 * Real.sqrt Real.pi + |c|) * W ξ := by
        have hh : (1+4*Real.sqrt Real.pi+|c|) ≤
            (1+4*Real.sqrt Real.pi+|c|)*W ξ := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hW
            (by positivity : 0 ≤ 1+4*Real.sqrt Real.pi+|c|)
        linarith only [hh]
      _ = K * W ξ := by dsimp [K]; ring
  unfold originalGammaFormDomain
  apply (hlog.const_mul K).mono'
    (((Symbol.finiteGammaWeight_continuous.add continuous_const).mul
      (hfreq.norm.pow 2)).aestronglyMeasurable)
  exact Eventually.of_forall fun ξ => by
    simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖U ξ‖)]
    calc
      _ ≤ (K * W ξ) * ‖U ξ‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (hweight ξ) (sq_nonneg _)
      _ = K * (W ξ * ‖U ξ‖ ^ 2) := by ring

private def correctedGaussian (a : ℝ) (q : ℂ) (x : ℝ) : ℂ :=
  literalGaussian a x-q*literalGaussian 0 x

private theorem correctedGaussian_actualProfile (a : ℝ) (q : ℂ) :
    actualGammaProfile (correctedGaussian a q) =
      fun t : ℝ => actualGammaProfile (literalGaussian a) t -
        q*actualGammaProfile (literalGaussian 0) t := by
  funext t
  by_cases ht : 0 ≤ t
  · have hsA := (literalGaussian_fullHasSum a t).summable
    have hs0 := (literalGaussian_fullHasSum 0 t).summable
    have htheta : fullTheta (correctedGaussian a q) (Real.pi*exp t) =
        fullTheta (literalGaussian a) (Real.pi*exp t)-
          q*fullTheta (literalGaussian 0) (Real.pi*exp t) := by
      unfold fullTheta
      have he : (fun n : ℕ => physicalTerm (correctedGaussian a q) n (Real.pi*exp t)) =
          fun n : ℕ => physicalTerm (literalGaussian a) n (Real.pi*exp t)-
            q*physicalTerm (literalGaussian 0) n (Real.pi*exp t) := by
        funext n
        simp only [physicalTerm, correctedGaussian]
        ring
      rw [he, hsA.tsum_sub (hs0.mul_left q), tsum_mul_left]
    simp only [actualGammaProfile, if_pos ht, htheta]
    ring
  · simp only [actualGammaProfile, if_neg ht, mul_zero, sub_zero]

private theorem correctedGaussian_fourier {a : ℝ} (ha : 0 ≤ a) (q : ℂ) (ξ : ℝ) :
    unitarySourceFourier (actualGammaProfile (correctedGaussian a q)) ξ =
      unitarySourceFourier (actualGammaProfile (literalGaussian a)) ξ-
        q*unitarySourceFourier (actualGammaProfile (literalGaussian 0)) ξ := by
  have hint (f : ℝ → ℂ) (hf : Integrable f volume) :
      Integrable (fun t => sourcePhase ξ t*f t) volume := by
    exact hf.bdd_mul
      (show Continuous (sourcePhase ξ) by unfold sourcePhase; fun_prop).aestronglyMeasurable
      (Eventually.of_forall fun t => (sourcePhase_norm ξ t).le)
  rw [correctedGaussian_actualProfile a q]
  simp only [unitarySourceFourier_eq_integral]
  rw [show (fun t : ℝ => sourcePhase ξ t*
        (actualGammaProfile (literalGaussian a) t-q*actualGammaProfile (literalGaussian 0) t)) =
      (fun t : ℝ => sourcePhase ξ t*actualGammaProfile (literalGaussian a) t-
        q*(sourcePhase ξ t*actualGammaProfile (literalGaussian 0) t)) from
      funext fun t => by ring,
    integral_sub (hint _ (literalGaussian_profile_l1 ha))
      ((hint _ (literalGaussian_profile_l1 (by norm_num : (0:ℝ)≤0))).const_mul q),
    integral_const_mul]
  ring

/- Arbitrary complex cancellation is permitted. In particular q may be the
   ACTUAL charge ratio mu(g_a)/mu(g_0); mean-zero is not used to obtain a domain. -/
theorem correctedGaussian_originalGammaFormDomain {a : ℝ} (ha : 0 ≤ a)
    (q : ℂ) (c : ℝ) : originalGammaFormDomain c (correctedGaussian a q) := by
  obtain ⟨_, _, _, _, hcA, _, _⟩ := literalGaussian_fourier_decay ha
  obtain ⟨_, _, _, _, hc0, _, _⟩ :=
    literalGaussian_fourier_decay (by norm_num : (0:ℝ)≤0)
  have hfreq : Continuous
      (unitarySourceFourier (actualGammaProfile (correctedGaussian a q))) := by
    convert hcA.sub (continuous_const.mul hc0) using 1
    funext ξ
    exact correctedGaussian_fourier ha q ξ
  have hlarge := literalGaussian_originalGammaFormDomain ha |c|
  have hsmall := literalGaussian_originalGammaFormDomain (by norm_num : (0:ℝ)≤0) |c|
  unfold originalGammaFormDomain at hlarge hsmall ⊢
  apply ((hlarge.add (hsmall.const_mul (‖q‖^2))).const_mul 2).mono'
    (((Symbol.finiteGammaWeight_continuous.add continuous_const).mul
      (hfreq.norm.pow 2)).aestronglyMeasurable)
  filter_upwards with ξ
  have hg0 : 0 ≤ Symbol.gammaWeight ξ := by
    linarith [(Symbol.actualGammaWeight_bounds ξ).1]
  have hg : |Symbol.gammaWeight ξ+c| ≤ Symbol.gammaWeight ξ+|c| := by
    simpa only [abs_of_nonneg hg0] using abs_add_le (Symbol.gammaWeight ξ) c
  have hsq :
      ‖unitarySourceFourier (actualGammaProfile (correctedGaussian a q)) ξ‖^2 ≤
        2*‖unitarySourceFourier (actualGammaProfile (literalGaussian a)) ξ‖^2+
        2*‖q‖^2*‖unitarySourceFourier (actualGammaProfile (literalGaussian 0)) ξ‖^2 := by
    rw [correctedGaussian_fourier ha q ξ]
    have hh := pow_le_pow_left₀ (norm_nonneg _)
      (norm_sub_le (unitarySourceFourier (actualGammaProfile (literalGaussian a)) ξ)
        (q*unitarySourceFourier (actualGammaProfile (literalGaussian 0)) ξ)) 2
    rw [norm_mul] at hh
    nlinarith only [hh, sq_nonneg
      (‖unitarySourceFourier (actualGammaProfile (literalGaussian a)) ξ‖-
        ‖q‖*‖unitarySourceFourier (actualGammaProfile (literalGaussian 0)) ξ‖)]
  simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply]
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (sq_nonneg
      ‖unitarySourceFourier (actualGammaProfile (correctedGaussian a q)) ξ‖)]
  calc
    _ ≤ (Symbol.gammaWeight ξ+|c|)*
        ‖unitarySourceFourier (actualGammaProfile (correctedGaussian a q)) ξ‖^2 :=
      mul_le_mul_of_nonneg_right hg (sq_nonneg _)
    _ ≤ (Symbol.gammaWeight ξ+|c|)*
        (2*‖unitarySourceFourier (actualGammaProfile (literalGaussian a)) ξ‖^2+
          2*‖q‖^2*‖unitarySourceFourier (actualGammaProfile (literalGaussian 0)) ξ‖^2) :=
      mul_le_mul_of_nonneg_left hsq (add_nonneg hg0 (abs_nonneg c))
    _ = _ := by ring

end D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft

#print axioms D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft.literalGaussian_originalGammaFormDomain
#print axioms D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft.correctedGaussian_originalGammaFormDomain
#print axioms D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft.actual_unshifted_phi_spectrum_zero

namespace D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft

open Real Set MeasureTheory Filter
open scoped Topology ENNReal
open D5.S3.Analytic.Fourier.ThetaDifferentialKernel
open D5.S3.Zeros.Jensen.NormalizedJensenDegreeLowering
open D5.S3.Zeros.Jensen.SourceThetaMomentBounds
open D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail
open D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
open RHFourJetDraft

open private psiSecond_eq from D5.S3.Analytic.Fourier.XiThetaTransform

private def gaussianTailRay (a t : ℝ) : ℝ :=
  (Real.pi ^ (1/4:ℝ)/4)*(psi (a+t/2)-2*psiFirst (a+t/2))

private def gaussianTailSize : ℝ :=
  (Real.pi ^ (1/4:ℝ)/4)*(3*fullConstant 0)

private theorem gaussianTailSize_nonneg : 0 ≤ gaussianTailSize := by
  unfold gaussianTailSize
  exact mul_nonneg (by positivity) (mul_nonneg (by norm_num) (fullConstant_nonneg 0))

private theorem gaussianTailRay_continuous (a : ℝ) : Continuous (gaussianTailRay a) := by
  have hp : Continuous psi := continuous_iff_continuousAt.mpr
    (fun x => (hasDerivAt_psi x).continuousAt)
  have hp' : Continuous psiFirst := continuous_iff_continuousAt.mpr
    (fun x => (hasDerivAt_psiFirst x).continuousAt)
  exact continuous_const.mul
    ((hp.comp (by fun_prop)).sub (continuous_const.mul (hp'.comp (by fun_prop))))

private theorem gaussianTailRay_deriv {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    HasDerivAt (gaussianTailRay a)
      ((5/4:ℝ)*gaussianTailRay a t-gaussianRay a t) t := by
  have hb : HasDerivAt (fun t : ℝ => a+t/2) (1/2:ℝ) t := by
    simpa using ((hasDerivAt_id t).div_const 2).const_add a
  have hphi : sourceThetaKernel (a+t/2) = fullJet 0 (a+t/2) := by
    rw [fullJet_zero_eq_phi (by linarith), romikPhi_eq_source]
  convert ((((hasDerivAt_psi (a+t/2)).comp t hb).sub
    (((hasDerivAt_psiFirst (a+t/2)).comp t hb).const_mul 2)).const_mul
      (Real.pi ^ (1/4:ℝ)/4)) using 1
  · rfl
  · rw [psiSecond_eq, hphi]
    dsimp only [gaussianTailRay, gaussianRay]
    ring

private theorem gaussianTailRay_bound {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    |gaussianTailRay a t| ≤ gaussianTailSize*exp (-t/2) := by
  have hb : 0 ≤ a+t/2 := by linarith
  have hp := psi_bounds hb
  have hphi : sourceThetaKernel (a+t/2) = fullJet 0 (a+t/2) := by
    rw [fullJet_zero_eq_phi hb, romikPhi_eq_source]
  rw [hphi] at hp
  have h0 := halfJet_bound 0 ha ht
  have hp0 : |psi (a+t/2)| ≤ fullConstant 0*exp (-t/2) :=
    hp.1.trans ((le_abs_self _).trans h0)
  have hp1 : |psiFirst (a+t/2)| ≤ fullConstant 0*exp (-t/2) :=
    hp.2.trans ((le_abs_self _).trans h0)
  have hh : |psi (a+t/2)-2*psiFirst (a+t/2)| ≤
      |psi (a+t/2)|+2*|psiFirst (a+t/2)| := by
    simpa [abs_mul] using abs_sub_le (psi (a+t/2)) 0 (2*psiFirst (a+t/2))
  rw [gaussianTailRay, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ Real.pi^(1/4:ℝ)/4)]
  apply (mul_le_mul_of_nonneg_left
    (show |psi (a+t/2)-2*psiFirst (a+t/2)| ≤
      3*fullConstant 0*exp (-t/2) by linarith) (by positivity)).trans_eq
  dsimp only [gaussianTailSize]
  ring

private theorem gaussian_exp_half_integrable :
    IntegrableOn (fun s : ℝ => exp (-s/2)) (Ioi 0) := by
  convert integrableOn_exp_mul_Ioi (show (-1/2:ℝ)<0 by norm_num) 0 using 1
  funext s
  congr 1
  ring

private theorem gaussian_exp_half_tendsto :
    Tendsto (fun s : ℝ => exp (-s/2)) atTop (𝓝 0) := by
  have hh := tendsto_exp_atBot.comp
    (tendsto_id.const_mul_atTop_of_neg (show (-1/2:ℝ)<0 by norm_num))
  convert hh using 1 <;> ext s <;>
    dsimp only [Function.comp_apply, id_eq] <;> congr 1 <;> ring

private theorem gaussian_weighted_translate_integrable {a t : ℝ}
    (ha : 0 ≤ a) (ht : 0 ≤ t) :
    IntegrableOn (fun s : ℝ => (exp (-(5/4:ℝ)*s):ℂ)*
      actualGammaProfile (literalGaussian a) (t+s)) (Ioi 0) := by
  rw [literalGaussian_actualProfile ha]
  have hc : Continuous (fun s : ℝ => (exp (-(5/4:ℝ)*s):ℂ)*
      (gaussianRay a (t+s):ℂ)) := by
    have he : Continuous (fun s : ℝ => (exp (-(5/4:ℝ)*s):ℂ)) := by fun_prop
    exact he.mul
      (Complex.continuous_ofReal.comp ((gaussianRay_continuous a).comp (by fun_prop)))
  apply (gaussian_exp_half_integrable.const_mul gaussianRaySize).mono'
    (hc.aestronglyMeasurable.congr (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs0 : 0 < s := hs
      simp only [if_pos (by linarith : 0 ≤ t+s)]))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs0 : 0 < s := hs
  have hts : 0 ≤ t+s := by linarith
  simp only [if_pos hts, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (exp_pos _)]
  calc
    exp (-(5/4:ℝ)*s)*|gaussianRay a (t+s)| ≤
        1*(gaussianRaySize*exp (-(t+s)/2)) :=
      mul_le_mul (Real.exp_le_one_iff.mpr (by linarith))
        (gaussianRay_bounds ha hts).1 (abs_nonneg _) (by norm_num)
    _ ≤ gaussianRaySize*exp (-s/2) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_left
        (exp_le_exp.mpr (by linarith)) gaussianRaySize_nonneg

/-- The literal right exponential tail is evaluated by a genuine improper
    integral and a decaying primitive; no ODE-uniqueness premise is assumed. -/
theorem literalGaussian_right_tail {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    rightExponentialTail (5/4) (actualGammaProfile (literalGaussian a)) t =
      (gaussianTailRay a t : ℂ) := by
  let V : ℝ → ℂ := fun s => (exp (-(5/4:ℝ)*s):ℂ)*(gaussianTailRay a (t+s):ℂ)
  let U : ℝ → ℂ := fun s => (exp (-(5/4:ℝ)*s):ℂ)*
    actualGammaProfile (literalGaussian a) (t+s)
  have hderiv : ∀ s ∈ Ici (0:ℝ), HasDerivAt V (-U s) s := by
    intro s hs
    have hts : 0 ≤ t+s := by linarith [hs.out]
    have he : HasDerivAt (fun s : ℝ => exp (-(5/4:ℝ)*s))
        (-(5/4:ℝ)*exp (-(5/4:ℝ)*s)) s := by
      convert! (((hasDerivAt_id s).const_mul (-(5/4:ℝ))).exp) using 1 <;>
        dsimp only [Function.comp_apply, id_eq] <;> ring
    have hv := (gaussianTailRay_deriv ha hts).comp s
      ((hasDerivAt_id s).const_add t)
    convert he.ofReal_comp.mul hv.ofReal_comp using 1
    · rfl
    · dsimp only [U]
      simp only [literalGaussian_actualProfile ha, if_pos hts, Function.comp_apply]
      push_cast
      ring
  have htop : Tendsto V atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun s : ℝ => gaussianTailSize*exp (-s/2))
    · filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
      have hts : 0 ≤ t+s := by linarith
      dsimp only [V]
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      calc
        exp (-(5/4:ℝ)*s)*|gaussianTailRay a (t+s)| ≤
            1*(gaussianTailSize*exp (-(t+s)/2)) :=
          mul_le_mul (Real.exp_le_one_iff.mpr (by linarith))
            (gaussianTailRay_bound ha hts) (abs_nonneg _) (by norm_num)
        _ ≤ gaussianTailSize*exp (-s/2) := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_left
            (exp_le_exp.mpr (by linarith)) gaussianTailSize_nonneg
    · simpa only [mul_zero] using gaussian_exp_half_tendsto.const_mul gaussianTailSize
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    (gaussian_weighted_translate_integrable ha ht).neg htop
  change (∫ s : ℝ in Ioi 0, U s) = _
  rw [integral_neg] at hFTC
  simpa only [V, zero_mul, mul_zero, exp_zero, Complex.ofReal_one, one_mul,
    add_zero, zero_sub, neg_inj] using hFTC

/-- The actual Suzuki image is exactly the translated original theta kernel. -/
theorem literalGaussian_actualSuzukiB {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    actualSuzukiBProfile (literalGaussian a) t =
      (Real.pi^(1/4:ℝ)/4:ℝ)*(romikPhi (a+t/2):ℂ) := by
  rw [actualSuzukiBProfile, literalGaussian_right_tail ha ht,
    literalGaussian_actualProfile ha]
  simp only [if_pos ht]
  have hb : 0 ≤ a+t/2 := by linarith
  simp only [gaussianRay, gaussianTailRay, fullJet_zero_eq_phi hb]
  push_cast
  ring

/-- This is the W360 even arithmetic profile, with its exact factor two. -/
theorem literalGaussian_actualSuzukiEvenB {a : ℝ} (ha : 0 ≤ a) (r : ℝ) :
    actualSuzukiEvenBProfile (literalGaussian a) r =
      (Real.pi^(1/4:ℝ)/4:ℝ)*(romikPhi (a+|r|):ℂ) := by
  unfold actualSuzukiEvenBProfile
  rw [literalGaussian_actualSuzukiB ha (by positivity)]
  rw [show a+2*|r|/2=a+|r| by ring]

theorem correctedGaussian_actualSuzukiB {a t : ℝ}
    (ha : 0 ≤ a) (ht : 0 ≤ t) (q : ℂ) :
    actualSuzukiBProfile (correctedGaussian a q) t =
      actualSuzukiBProfile (literalGaussian a) t-
        q*actualSuzukiBProfile (literalGaussian 0) t := by
  have htail : rightExponentialTail (5/4) (actualGammaProfile (correctedGaussian a q)) t =
      rightExponentialTail (5/4) (actualGammaProfile (literalGaussian a)) t-
        q*rightExponentialTail (5/4) (actualGammaProfile (literalGaussian 0)) t := by
    simp only [rightExponentialTail, correctedGaussian_actualProfile]
    simp_rw [mul_sub, show ∀ s : ℝ,
      (exp (-(5/4:ℝ)*s):ℂ)*(q*actualGammaProfile (literalGaussian 0) (t+s)) =
        q*((exp (-(5/4:ℝ)*s):ℂ)*actualGammaProfile (literalGaussian 0) (t+s))
      from fun s => by ring]
    rw [integral_sub (gaussian_weighted_translate_integrable ha ht)
      ((gaussian_weighted_translate_integrable (by norm_num : (0:ℝ)≤0) ht).const_mul q),
      integral_const_mul]
  unfold actualSuzukiBProfile
  rw [htail]
  simp only [correctedGaussian_actualProfile]
  ring

theorem correctedGaussian_actualSuzukiEvenB {a : ℝ} (ha : 0 ≤ a) (q : ℂ) (r : ℝ) :
    actualSuzukiEvenBProfile (correctedGaussian a q) r =
      (Real.pi^(1/4:ℝ)/4:ℝ)*
        ((romikPhi (a+|r|):ℂ)-q*(romikPhi |r|:ℂ)) := by
  unfold actualSuzukiEvenBProfile
  rw [correctedGaussian_actualSuzukiB ha (by positivity),
    literalGaussian_actualSuzukiB ha (by positivity),
    literalGaussian_actualSuzukiB (by norm_num : (0:ℝ)≤0) (by positivity)]
  have harg : a+2*|r|/2 = a+|r| := by ring
  have harg0 : (0:ℝ)+2*|r|/2 = |r| := by ring
  rw [harg, harg0]
  ring

private theorem literalGaussian_zero_charge_ne :
    actualSuzukiMeanCharge (literalGaussian 0) ≠ 0 := by
  have hp (r : ℝ) : romikPhi |r| = sourceThetaKernel r := by
    rw [romikPhi_eq_source]
    by_cases hr : 0 ≤ r
    · rw [abs_of_nonneg hr]
    · rw [abs_of_neg (lt_of_not_ge hr), source_theta_even]
  have hμ : actualSuzukiMeanCharge (literalGaussian 0) =
      (Real.pi^(1/4:ℝ)/4:ℝ)*((∫ r : ℝ, sourceThetaKernel r):ℂ) := by
    unfold actualSuzukiMeanCharge
    simp_rw [literalGaussian_actualSuzukiEvenB (by norm_num : (0:ℝ)≤0),
      zero_add, hp]
    rw [integral_const_mul, integral_complex_ofReal]
  rw [hμ]
  apply mul_ne_zero
  · exact_mod_cast (by positivity : Real.pi^(1/4:ℝ)/4 ≠ 0)
  · exact_mod_cast (show (∫ r : ℝ, sourceThetaKernel r) ≠ 0 from
      (by simpa using (source_theta_raw_moments 0).2.ne'))

private def centeredGaussianCharge (a : ℝ) : ℂ :=
  actualSuzukiMeanCharge (literalGaussian a)/actualSuzukiMeanCharge (literalGaussian 0)

/-- Centering the original physical source leaves its nonzero actual
    spectral coordinate intact. The next fragment pays its physical H6. -/
theorem correctedGaussian_actual_cosine_spectrum_nonzero (q : ℂ) :
    ∃ n : ℕ, (∫ t : ℝ in Ioi 0,
      actualSuzukiEvenBProfile (correctedGaussian (Real.log 2/2) q) t*
        Complex.cos (zetaZeroData.gamma n*(t:ℂ))) ≠ 0 := by
  let a : ℝ := Real.log 2/2
  have ha : 0 ≤ a := (div_pos (Real.log_pos (by norm_num : (1:ℝ)<2))
    (by norm_num : (0:ℝ)<2)).le
  obtain ⟨n, hn⟩ := actual_shifted_phi_spectrum_nonzero
  have hz : |(zetaZeroData.gamma n).im| ≤ 1/2 :=
    RhTransient.ActualZeroCosineNonzero.actual_gamma_half_strip n
  have hL : IntegrableOn (fun t : ℝ => |fullJet 0 (a+t)| *exp (t/2)) (Ioi 0) := by
    apply ((translated_phi_jets 0 ha).1).congr_fun ?_ measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := ht
    dsimp only
    rw [iteratedDeriv_zero, fullJet_zero_eq_phi (x := a+t) (by linarith)]
    ring
  have hI : IntegrableOn (fun t : ℝ => (romikPhi (a+t):ℂ)*
      Complex.cos (zetaZeroData.gamma n*(t:ℂ))) (Ioi 0) := by
    apply (trig_product_integrable (fun t => fullJet 0 (a+t))
      ((fullJet_continuous 0).comp (by fun_prop)) hL _ hz).1.congr_fun ?_
        measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := ht
    dsimp only
    rw [fullJet_zero_eq_phi (x := a+t) (by linarith)]
  have hI0 := (phi_halfline_cosine_eq_xi (zetaZeroData.gamma n)).1
  have heq : (∫ t : ℝ in Ioi 0,
      actualSuzukiEvenBProfile (correctedGaussian a q) t*
        Complex.cos (zetaZeroData.gamma n*(t:ℂ))) =
      (Real.pi^(1/4:ℝ)/4:ℝ)*
        (∫ t : ℝ in Ioi 0, (romikPhi (a+t):ℂ)*
          Complex.cos (zetaZeroData.gamma n*(t:ℂ))) := by
    calc
      _ = ∫ t : ℝ in Ioi 0, (Real.pi^(1/4:ℝ)/4:ℝ)*
          ((romikPhi (a+t):ℂ)*Complex.cos (zetaZeroData.gamma n*(t:ℂ))-
            q*((romikPhi t:ℂ)*Complex.cos (zetaZeroData.gamma n*(t:ℂ)))) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only
        rw [correctedGaussian_actualSuzukiEvenB ha, abs_of_pos ht]
        ring
      _ = _ := by
        rw [integral_const_mul, integral_sub hI (hI0.const_mul q),
          integral_const_mul, actual_unshifted_phi_spectrum_zero, mul_zero, sub_zero]
  refine ⟨n, ?_⟩
  rw [heq]
  exact mul_ne_zero (by exact_mod_cast (by positivity : Real.pi^(1/4:ℝ)/4 ≠ 0)) hn

end D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft

namespace D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft

open Real Set MeasureTheory Filter
open scoped Topology ENNReal
open D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData

private theorem literalGaussian_norm_sq (a x : ℝ) :
    ‖literalGaussian a x‖^2 = exp (9*a)*exp (-(2*exp (2*a))*x) := by
  simp only [literalGaussian, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (exp_pos _)]
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

private theorem literalGaussian_polynomial_sq_integrable (a : ℝ) (k : ℕ) :
    IntegrableOn (fun x : ℝ => x^k*‖literalGaussian a x‖^2) (Ioi Real.pi) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1:ℝ)) (s := (k:ℝ)) (b := 2*exp (2*a))
    (by exact lt_of_lt_of_le (by norm_num : (-1:ℝ)<0) (Nat.cast_nonneg k))
    (by norm_num) (by positivity)
  have h' := (h.mono_set (Ioi_subset_Ioi Real.pi_pos.le)).const_mul (exp (9*a))
  apply IntegrableOn.congr_fun h' ?_ measurableSet_Ioi
  intro x _
  dsimp only
  rw [Real.rpow_one, Real.rpow_natCast, literalGaussian_norm_sq]
  ring

/-- Every member of the literal Gaussian family is in the original physical
    H6 space, with its sixth moment on the original x>pi measure. -/
theorem literalGaussian_original_h6 (a : ℝ) :
    originalPhysicalH6 (literalGaussian a) := by
  have hc : Continuous (literalGaussian a) := by
    unfold literalGaussian
    fun_prop
  have h0 : IntegrableOn (fun x : ℝ => ‖literalGaussian a x‖^2) (Ioi Real.pi) := by
    simpa only [pow_zero, one_mul] using literalGaussian_polynomial_sq_integrable a 0
  refine ⟨(memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2 h0, ?_⟩
  have h6 := (literalGaussian_polynomial_sq_integrable a 6).const_mul ((Real.pi^6)⁻¹)
  apply IntegrableOn.congr_fun h6 ?_ measurableSet_Ioi
  intro x _
  field_simp [Real.pi_ne_zero] <;> ring

private theorem original_h6_sub_const_mul
    (F G : ℝ → ℂ) (hF : originalPhysicalH6 F) (hG : originalPhysicalH6 G) (q : ℂ) :
    originalPhysicalH6 (fun x => F x-q*G x) := by
  have hmem := hF.1.sub (hG.1.const_mul q)
  refine ⟨hmem, ?_⟩
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => (x/Real.pi)^6*‖F x-q*G x‖^2)
        (volume.restrict (Ioi Real.pi)) :=
    ((continuous_id.div_const Real.pi).pow 6).aestronglyMeasurable.mul
      (hmem.aestronglyMeasurable.norm.pow 2)
  apply ((hF.2.const_mul 2).add (hG.2.const_mul (2*‖q‖^2))).mono' hmeas
  filter_upwards with x
  have hweight : 0 ≤ (x/Real.pi)^6 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hweight (sq_nonneg _))]
  have hnorm : ‖F x-q*G x‖^2 ≤ 2*‖F x‖^2+2*‖q‖^2*‖G x‖^2 := by
    have hh := pow_le_pow_left₀ (norm_nonneg (F x-q*G x))
      (norm_sub_le (F x) (q*G x)) 2
    rw [norm_mul] at hh
    nlinarith [sq_nonneg (‖F x‖-‖q‖*‖G x‖)]
  calc
    (x/Real.pi)^6*‖F x-q*G x‖^2 ≤
        (x/Real.pi)^6*(2*‖F x‖^2+2*‖q‖^2*‖G x‖^2) :=
      mul_le_mul_of_nonneg_left hnorm hweight
    _ = _ := by
      simp only [Pi.add_apply]
      ring

theorem correctedGaussian_original_h6 (a : ℝ) (q : ℂ) :
    originalPhysicalH6 (correctedGaussian a q) :=
  original_h6_sub_const_mul _ _ (literalGaussian_original_h6 a)
    (literalGaussian_original_h6 0) q

/-- The centering coefficient is the quotient of the actual even-B charges.
    Its denominator was proved nonzero from the actual original kernel mass. -/
theorem centeredGaussian_actual_mean_zero (a : ℝ) :
    actualSuzukiMeanCharge (correctedGaussian a (centeredGaussianCharge a)) = 0 := by
  let q : ℂ := centeredGaussianCharge a
  have heq : (fun x => (1:ℂ)*literalGaussian a x+(-q)*literalGaussian 0 x) =
      correctedGaussian a q := by
    funext x
    dsimp only [correctedGaussian]
    ring
  have hH : originalPhysicalH6
      (fun x => (1:ℂ)*literalGaussian a x+(-q)*literalGaussian 0 x) := by
    rw [heq]
    exact correctedGaussian_original_h6 a q
  have hlin := actual_h6_suzuki_mean_charge_linear _ _
    (literalGaussian_original_h6 a) (literalGaussian_original_h6 0) 1 (-q) hH
  rw [heq] at hlin
  change actualSuzukiMeanCharge (correctedGaussian a q) = 0
  rw [hlin, one_mul, neg_mul, ← sub_eq_add_neg]
  dsimp only [q, centeredGaussianCharge]
  rw [div_mul_cancel₀ _ literalGaussian_zero_charge_ne, sub_self]

/-- One and the same original physical source has H6, actual even-B mean
    zero, every shifted Gamma form-domain, and a nonzero actual discrete
    even-B cosine coordinate. This is not a claim of Weil-form positivity. -/
theorem actual_centered_gaussian_mean_zero_spectral_witness :
    ∃ F : ℝ → ℂ,
      originalPhysicalH6 F ∧ actualSuzukiMeanCharge F = 0 ∧
      (∀ c : ℝ, originalGammaFormDomain c F) ∧
      ∃ n : ℕ, (∫ t : ℝ in Ioi 0, actualSuzukiEvenBProfile F t*
        Complex.cos (zetaZeroData.gamma n*(t:ℂ))) ≠ 0 := by
  let a : ℝ := Real.log 2/2
  have ha : 0 ≤ a := (div_pos (Real.log_pos (by norm_num : (1:ℝ)<2))
    (by norm_num : (0:ℝ)<2)).le
  refine ⟨correctedGaussian a (centeredGaussianCharge a),
    correctedGaussian_original_h6 a _, centeredGaussian_actual_mean_zero a, ?_, ?_⟩
  · exact fun c => correctedGaussian_originalGammaFormDomain ha _ c
  · exact correctedGaussian_actual_cosine_spectrum_nonzero _

end D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft

#print axioms D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft.actual_centered_gaussian_mean_zero_spectral_witness
#print axioms D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft.literalGaussian_actualSuzukiEvenB

namespace D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft

open Real Set MeasureTheory Filter
open scoped Topology ENNReal
open D5.S3.Analytic.Fourier.ThetaDifferentialKernel
open D5.S3.Zeros.Jensen.NormalizedJensenDegreeLowering
open D5.S3.Zeros.Jensen.SourceThetaMomentBounds
open D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData

private theorem strip_exponential_norm_le (z : ℂ) (hz : |z.im| ≤ 1/2)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖Complex.exp (Complex.I*z*(t:ℂ))‖ ≤ exp (t/2) := by
  have hre : (Complex.I*z*(t:ℂ)).re = -z.im*t := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [Complex.norm_exp, hre]
  apply exp_le_exp.mpr
  have hneg : -z.im ≤ 1/2 := (neg_le_abs z.im).trans hz
  nlinarith [mul_le_mul_of_nonneg_right hneg ht]

private theorem shifted_phi_strip_exponential_integrable {a : ℝ}
    (ha : 0 ≤ a) (z : ℂ) (hz : |z.im| ≤ 1/2) :
    IntegrableOn (fun t : ℝ => (romikPhi (a+t):ℂ)*
      Complex.exp (Complex.I*z*(t:ℂ))) (Ioi 0) := by
  have hL : IntegrableOn
      (fun t : ℝ => |romikPhi (a+t)| *exp (t/2)) (Ioi 0) := by
    apply ((translated_phi_jets 0 ha).1).congr_fun ?_ measurableSet_Ioi
    intro t _
    dsimp only
    rw [iteratedDeriv_zero]
    ring
  have hc : Continuous romikPhi := source_theta_continuous.congr
    (fun x => (romikPhi_eq_source x).symm)
  have hm : Continuous (fun t : ℝ => (romikPhi (a+t):ℂ)*
      Complex.exp (Complex.I*z*(t:ℂ))) :=
    (Complex.continuous_ofReal.comp (hc.comp (by fun_prop))).mul (by fun_prop)
  apply hL.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (strip_exponential_norm_le z hz ht.le) (abs_nonneg _)

private theorem correctedGaussian_evenB_strip_exponential_integrable {a : ℝ}
    (ha : 0 ≤ a) (q z : ℂ) (hz : |z.im| ≤ 1/2) :
    IntegrableOn (fun t : ℝ => actualSuzukiEvenBProfile (correctedGaussian a q) t*
      Complex.exp (Complex.I*z*(t:ℂ))) (Ioi 0) := by
  have hA := shifted_phi_strip_exponential_integrable ha z hz
  have h0 := shifted_phi_strip_exponential_integrable (by norm_num : (0:ℝ)≤0) z hz
  have h := (hA.sub (h0.const_mul q)).const_mul ((Real.pi^(1/4:ℝ)/4:ℝ):ℂ)
  apply IntegrableOn.congr_fun h ?_ measurableSet_Ioi
  intro t ht
  dsimp only [Pi.sub_apply]
  rw [correctedGaussian_actualSuzukiEvenB ha, abs_of_pos ht]
  simp only [zero_add]
  ring

/- A private integral calculation, applied only to the actual source below.
   The two indicators retain the positive and negative exponential tilts;
   their reflected sum is the original full-line integrand almost everywhere.
   The point zero is removed by its actual volume-zero property. -/
private theorem even_profile_full_exponential_fold
    (g : ℝ → ℂ) (heven : ∀ r : ℝ, g (-r) = g r) (z : ℂ)
    (hplus : IntegrableOn (fun t : ℝ => g t*Complex.exp (Complex.I*z*(t:ℂ))) (Ioi 0))
    (hminus : IntegrableOn (fun t : ℝ => g t*Complex.exp (Complex.I*(-z)*(t:ℂ))) (Ioi 0)) :
    Integrable (fun r : ℝ => g r*Complex.exp (Complex.I*z*(r:ℂ))) volume ∧
    (∫ r : ℝ, g r*Complex.exp (Complex.I*z*(r:ℂ))) =
      2*(∫ t : ℝ in Ioi 0, g t*Complex.cos (z*(t:ℂ))) := by
  let P : ℝ → ℂ := (Ioi (0:ℝ)).indicator
    (fun t : ℝ => g t*Complex.exp (Complex.I*z*(t:ℂ)))
  let M : ℝ → ℂ := (Ioi (0:ℝ)).indicator
    (fun t : ℝ => g t*Complex.exp (Complex.I*(-z)*(t:ℂ)))
  have hP : Integrable P volume := (integrable_indicator_iff measurableSet_Ioi).2 hplus
  have hM : Integrable M volume := (integrable_indicator_iff measurableSet_Ioi).2 hminus
  have heq : (fun r : ℝ => P r+M (-r)) =ᵐ[volume]
      (fun r : ℝ => g r*Complex.exp (Complex.I*z*(r:ℂ))) := by
    filter_upwards [volume.ae_ne (0:ℝ)] with r hr
    rcases lt_or_gt_of_ne hr with hneg | hpos
    · have hn : 0 < -r := neg_pos.mpr hneg
      simp only [P, M, Set.indicator_apply, Set.mem_Ioi,
        if_neg hneg.not_gt, if_pos hn, zero_add, heven r]
      push_cast
      congr 2
      ring
    · have hn : ¬ 0 < -r := by linarith
      simp only [P, M, Set.indicator_apply, Set.mem_Ioi,
        if_pos hpos, if_neg hn, add_zero]
  refine ⟨(hP.add hM.comp_neg).congr heq, ?_⟩
  have hpair : Set.EqOn
      (fun t : ℝ => g t*Complex.exp (Complex.I*z*(t:ℂ))+
        g t*Complex.exp (Complex.I*(-z)*(t:ℂ)))
      (fun t : ℝ => (2:ℂ)*(g t*Complex.cos (z*(t:ℂ)))) (Ioi 0) := by
    intro t _
    have h1 : Complex.I*z*(t:ℂ) = (z*(t:ℂ))*Complex.I := by ring
    have h2 : Complex.I*(-z)*(t:ℂ) = -(z*(t:ℂ))*Complex.I := by ring
    dsimp only
    rw [h1, h2]
    calc
      _ = g t*(Complex.exp ((z*(t:ℂ))*Complex.I)+
          Complex.exp (-(z*(t:ℂ))*Complex.I)) := by ring
      _ = g t*(2*Complex.cos (z*(t:ℂ))) := by rw [Complex.two_cos]
      _ = _ := by ring
  calc
    (∫ r : ℝ, g r*Complex.exp (Complex.I*z*(r:ℂ))) =
        ∫ r : ℝ, P r+M (-r) := (integral_congr_ae heq).symm
    _ = (∫ r : ℝ, P r)+(∫ r : ℝ, M (-r)) := integral_add hP hM.comp_neg
    _ = (∫ r : ℝ, P r)+(∫ r : ℝ, M r) := by rw [integral_neg_eq_self]
    _ = (∫ t : ℝ in Ioi 0, g t*Complex.exp (Complex.I*z*(t:ℂ)))+
        (∫ t : ℝ in Ioi 0, g t*Complex.exp (Complex.I*(-z)*(t:ℂ))) := by
      rw [show (∫ r : ℝ, P r) =
          ∫ t : ℝ in Ioi 0, g t*Complex.exp (Complex.I*z*(t:ℂ)) from
            integral_indicator measurableSet_Ioi,
        show (∫ r : ℝ, M r) =
          ∫ t : ℝ in Ioi 0, g t*Complex.exp (Complex.I*(-z)*(t:ℂ)) from
            integral_indicator measurableSet_Ioi]
    _ = ∫ t : ℝ in Ioi 0,
        g t*Complex.exp (Complex.I*z*(t:ℂ))+
          g t*Complex.exp (Complex.I*(-z)*(t:ℂ)) := (integral_add hplus hminus).symm
    _ = ∫ t : ℝ in Ioi 0, (2:ℂ)*(g t*Complex.cos (z*(t:ℂ))) :=
      setIntegral_congr_fun measurableSet_Ioi (fun t ht => hpair ht)
    _ = _ := integral_const_mul _ _

private theorem correctedGaussian_evenB_full_exponential_fold {a : ℝ}
    (ha : 0 ≤ a) (q z : ℂ) (hz : |z.im| ≤ 1/2) :
    Integrable (fun r : ℝ => actualSuzukiEvenBProfile (correctedGaussian a q) r*
      Complex.exp (Complex.I*z*(r:ℂ))) volume ∧
    (∫ r : ℝ, actualSuzukiEvenBProfile (correctedGaussian a q) r*
      Complex.exp (Complex.I*z*(r:ℂ))) =
      2*(∫ t : ℝ in Ioi 0, actualSuzukiEvenBProfile (correctedGaussian a q) t*
        Complex.cos (z*(t:ℂ))) := by
  apply even_profile_full_exponential_fold
  · intro r
    simp only [actualSuzukiEvenBProfile, abs_neg]
  · exact correctedGaussian_evenB_strip_exponential_integrable ha q z hz
  · exact correctedGaussian_evenB_strip_exponential_integrable ha q (-z)
      (by simpa only [Complex.neg_im, abs_neg] using hz)

/-- The SAME original H6 source has zero actual even-B mean, all shifted
    Gamma domains, and a nonzero ordinary full-line exponential transform
    at an actual (possibly nonreal) zeta spectral node. `Integrable` pays the
    absolute integral; the expression is the literal ordinary Fourier
    integral of the actual even-B image, without a normalization surrogate. -/
theorem actual_centered_gaussian_full_spectrum_witness :
    ∃ F : ℝ → ℂ,
      originalPhysicalH6 F ∧ actualSuzukiMeanCharge F = 0 ∧
      (∀ c : ℝ, originalGammaFormDomain c F) ∧
      ∃ n : ℕ,
        Integrable (fun r : ℝ => actualSuzukiEvenBProfile F r*
          Complex.exp (Complex.I*zetaZeroData.gamma n*(r:ℂ))) volume ∧
        (∫ r : ℝ, actualSuzukiEvenBProfile F r*
          Complex.exp (Complex.I*zetaZeroData.gamma n*(r:ℂ))) ≠ 0 := by
  let a : ℝ := Real.log 2/2
  let q : ℂ := centeredGaussianCharge a
  have ha : 0 ≤ a := (div_pos (Real.log_pos (by norm_num : (1:ℝ)<2))
    (by norm_num : (0:ℝ)<2)).le
  obtain ⟨n, hn⟩ := correctedGaussian_actual_cosine_spectrum_nonzero q
  have hz : |(zetaZeroData.gamma n).im| ≤ 1/2 :=
    RhTransient.ActualZeroCosineNonzero.actual_gamma_half_strip n
  obtain ⟨hI, hfold⟩ := correctedGaussian_evenB_full_exponential_fold ha q
    (zetaZeroData.gamma n) hz
  refine ⟨correctedGaussian a q, correctedGaussian_original_h6 a q,
    centeredGaussian_actual_mean_zero a,
    (fun c => correctedGaussian_originalGammaFormDomain ha q c), n, hI, ?_⟩
  rw [hfold]
  exact mul_ne_zero (by norm_num) hn

#print axioms actual_centered_gaussian_full_spectrum_witness

end D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft

/- SOURCE DRAFT, NOT COMPILED (2026-10-27).
   Append in the SAME MODULE after ActualGaussianFullSpectrum.fragment.lean.
   This is an exact small-shift application, with all physical and spectral
   expressions left literal. No new G/Reg wrapper is introduced.
-/

namespace D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft

open Real Set MeasureTheory Filter Polynomial
open scoped Topology ENNReal
open D5.S3.Zeros.Jensen.OriginalPrimalTailProjection
open D5.S3.Analytic.Fourier.ThetaDifferentialKernel
open D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
open RHFourJetDraft
open private tailJet_summable_ray from
  D5.S3.Zeros.Jensen.OriginalPrimalTailProjection
open private jet_one from D5.S3.Zeros.Jensen.OriginalPrimalTailResponse

/- The old threshold six is unnecessary: at y>=4, 8y-30>=2, so
   y(8y-30)+15>0 and -y(8y^2-30y+15)<0. -/
private theorem first_polynomial_negative_four {y : ℝ} (hy : 4 ≤ y) :
    -8*y^3+30*y^2-15*y < 0 := by
  have hypos : 0 < y := by linarith
  have hlin : 0 < 8*y-30 := by linarith
  have hfac : 0 < y*(8*y-30)+15 := by positivity
  have hprod := mul_pos hypos hfac
  nlinarith

private theorem first_jet_negative_of_scale_ge_four {a : ℝ}
    (hscale : 4 ≤ Real.pi*exp (2*a)) (m : ℕ) (hm : 1 ≤ m) :
    primalJet 1 m a < 0 := by
  have hmreal : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hmsq : (1:ℝ) ≤ (m:ℝ)^2 := by nlinarith
  have hmode : Real.pi ≤ modeScale m := by
    dsimp [modeScale]
    simpa using mul_le_mul_of_nonneg_left hmsq Real.pi_pos.le
  have hy : 4 ≤ modeScale m*exp (2*a) := hscale.trans
    (mul_le_mul_of_nonneg_right hmode (exp_pos _).le)
  have hp : (jetPolynomial 1).eval (modeScale m*exp (2*a)) < 0 := by
    rw [jet_one]
    exact first_polynomial_negative_four hy
  exact mul_neg_of_pos_of_neg (mul_pos (exp_pos _) (exp_pos _)) hp

private theorem shift_pos_of_scale_ge_four {a : ℝ}
    (ha : 0 ≤ a) (hscale : 4 ≤ Real.pi*exp (2*a)) : 0 < a := by
  by_contra hn
  have ha0 : a = 0 := le_antisymm (le_of_not_gt hn) ha
  rw [ha0, mul_zero, exp_zero, mul_one] at hscale
  linarith [Real.pi_lt_four]

private theorem phi_derivative_negative_of_scale_ge_four {a : ℝ}
    (ha : 0 ≤ a) (hscale : 4 ≤ Real.pi*exp (2*a)) :
    deriv romikPhi a < 0 := by
  have hap : 0 < a := shift_pos_of_scale_ge_four ha hscale
  have hs := tailJet_summable_ray 1 1 (by omega) ha
  have ht : tailJet 1 1 a ≤ 0 := by
    have hsum := hs.tsum_le_tsum
      (fun j => (first_jet_negative_of_scale_ge_four hscale (1+j+1) (by omega)).le)
      (summable_zero : Summable (fun _ : ℕ => (0:ℝ)))
    simpa only [tailJet, tsum_zero] using hsum
  have hfull : fullJet 1 a < 0 := add_neg_of_neg_of_nonpos
    (first_jet_negative_of_scale_ge_four hscale 1 (by omega)) ht
  rw [fullJet_eq_phi_derivative 1 hap] at hfull
  simpa only [iteratedDeriv_one] using hfull

private theorem shifted_phi_spectrum_nonzero_of_derivative_negative {a : ℝ}
    (ha : 0 < a) (hderiv : deriv romikPhi a < 0) :
    ∃ n : ℕ, (∫ t : ℝ in Ioi 0, (romikPhi (a+t):ℂ)*
      Complex.cos (zetaZeroData.gamma n*(t:ℂ))) ≠ 0 := by
  let f : ℕ → ℝ → ℝ := fun k t => fullJet k (a+t)
  have hC (k : ℕ) : Continuous (f k) :=
    (fullJet_continuous k).comp (continuous_const.add continuous_id)
  have hD (k : ℕ) : ∀ t ∈ Ici (0:ℝ), HasDerivAt (f k) (f (k+1) t) t := by
    intro t ht
    simpa only [f, Function.comp_def, mul_one] using
      (fullJet_deriv k (a+t)).comp t ((hasDerivAt_id t).const_add a)
  have hL (k : ℕ) : IntegrableOn
      (fun t : ℝ => |f k t| * exp (t/2)) (Ioi 0) := by
    apply IntegrableOn.congr_fun ((translated_phi_jets k ha.le).1) ?_ measurableSet_Ioi
    intro t ht
    dsimp only [Pi.sub_apply, Pi.add_apply, f]
    have ht0 : 0 < t := ht
    rw [fullJet_eq_phi_derivative k (by linarith : 0 < a+t)]
    ring
  have hT (k : ℕ) : Tendsto
      (fun t : ℝ => |f k t| * exp (t/2)) atTop (𝓝 0) := by
    apply ((translated_phi_jets k ha.le).2).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    dsimp only [Pi.sub_apply, Pi.add_apply, f]
    rw [fullJet_eq_phi_derivative k (by linarith : 0 < a+t)]
    ring
  have hA : f 1 0 < 0 := by
    change fullJet 1 (a+0) < 0
    rw [add_zero, fullJet_eq_phi_derivative 1 ha]
    simpa only [iteratedDeriv_one] using hderiv
  have hbudget : 0 ≤ jetBudget (f 4) :=
    integral_nonneg (fun t => mul_nonneg (abs_nonneg _) (exp_pos _).le)
  have hnz : ∃ n : ℕ, cosineRay (f 0) (zetaZeroData.gamma n) ≠ 0 := by
    apply RhTransient.ActualZeroCosineNonzero.actual_zero_nonzero_of_fourth_remainder
      (cosineRay (f 0)) (f 1 0) (|f 3 0| + jetBudget (f 4)) hA
      (add_nonneg (abs_nonneg _) hbudget)
    intro z hz
    have hid := cosineRay_fourfold (f 0) (f 1) (f 2) (f 3) (f 4)
      (hC 0) (hC 2) (hC 4) (hD 0) (hD 1) (hD 2) (hD 3)
      (hL 0) (hL 2) (hL 4) (hT 0) (hT 1) (hT 2) (hT 3) z hz
    rw [hid]
    exact (norm_add_le _ _).trans (by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using add_le_add
        (le_refl |f 3 0|) (cosineRay_norm_le (f 4) (hC 4) (hL 4) z hz))
  obtain ⟨n, hn⟩ := hnz
  refine ⟨n, ?_⟩
  have he : cosineRay (f 0) (zetaZeroData.gamma n) =
      ∫ t : ℝ in Ioi 0, (romikPhi (a+t):ℂ)*
        Complex.cos (zetaZeroData.gamma n*(t:ℂ)) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    change (fullJet 0 (a+t):ℂ)*_ = _
    rw [fullJet_zero_eq_phi (add_nonneg ha.le ht0.le)]
  exact he ▸ hn

private theorem small_shift_positive : 0 < Real.log (4/3:ℝ)/2 :=
  div_pos (Real.log_pos (by norm_num : (1:ℝ)<4/3)) (by norm_num)

private theorem small_shift_scale_ge_four :
    4 ≤ Real.pi*exp (2*(Real.log (4/3:ℝ)/2)) := by
  have he : exp (2*(Real.log (4/3:ℝ)/2)) = 4/3 := by
    rw [show 2*(Real.log (4/3:ℝ)/2) = Real.log (4/3:ℝ) by ring,
      Real.exp_log (by norm_num : (0:ℝ)<4/3)]
  rw [he]
  nlinarith [Real.pi_gt_three]

/-- Every actual positive primal mode has negative first jet at this smaller
    shift; summability includes the complete tail, without a truncation. -/
theorem phi_derivative_small_shift_negative :
    deriv romikPhi (Real.log (4/3:ℝ)/2) < 0 :=
  phi_derivative_negative_of_scale_ge_four small_shift_positive.le small_shift_scale_ge_four

/-- The original translated kernel has a nonzero coordinate at an actual
    zeta spectral node at the smaller shift a=log(4/3)/2. -/
theorem actual_small_shift_phi_spectrum_nonzero :
    ∃ n : ℕ, (∫ t : ℝ in Ioi 0, (romikPhi (Real.log (4/3:ℝ)/2+t):ℂ)*
      Complex.cos (zetaZeroData.gamma n*(t:ℂ))) ≠ 0 :=
  shifted_phi_spectrum_nonzero_of_derivative_negative small_shift_positive
    phi_derivative_small_shift_negative

private theorem correctedGaussian_cosine_nonzero_of_scale_ge_four {a : ℝ}
    (ha : 0 ≤ a) (hscale : 4 ≤ Real.pi*exp (2*a)) (q : ℂ) :
    ∃ n : ℕ, (∫ t : ℝ in Ioi 0,
      actualSuzukiEvenBProfile (correctedGaussian a q) t*
        Complex.cos (zetaZeroData.gamma n*(t:ℂ))) ≠ 0 := by
  obtain ⟨n, hn⟩ := shifted_phi_spectrum_nonzero_of_derivative_negative
    (shift_pos_of_scale_ge_four ha hscale)
    (phi_derivative_negative_of_scale_ge_four ha hscale)
  have hz : |(zetaZeroData.gamma n).im| ≤ 1/2 :=
    RhTransient.ActualZeroCosineNonzero.actual_gamma_half_strip n
  have hL : IntegrableOn
      (fun t : ℝ => |fullJet 0 (a+t)| * exp (t/2)) (Ioi 0) := by
    apply IntegrableOn.congr_fun ((translated_phi_jets 0 ha).1) ?_ measurableSet_Ioi
    intro t ht
    dsimp only [Pi.sub_apply, Pi.add_apply]
    have ht0 : 0 < t := ht
    rw [iteratedDeriv_zero, fullJet_zero_eq_phi (by linarith)]
    ring
  have hI : IntegrableOn (fun t : ℝ => (romikPhi (a+t):ℂ)*
      Complex.cos (zetaZeroData.gamma n*(t:ℂ))) (Ioi 0) := by
    have hj : IntegrableOn (fun t : ℝ => (fullJet 0 (a+t):ℂ)*
        Complex.cos (zetaZeroData.gamma n*(t:ℂ))) (Ioi 0) :=
      (trig_product_integrable (fun t => fullJet 0 (a+t))
        ((fullJet_continuous 0).comp (by fun_prop)) hL _ hz).1
    apply IntegrableOn.congr_fun hj ?_ measurableSet_Ioi
    intro t ht
    dsimp only [Pi.sub_apply, Pi.add_apply]
    have ht0 : 0 < t := ht
    rw [fullJet_zero_eq_phi (by linarith)]
  have hI0 := (phi_halfline_cosine_eq_xi (zetaZeroData.gamma n)).1
  have heq : (∫ t : ℝ in Ioi 0,
      actualSuzukiEvenBProfile (correctedGaussian a q) t*
        Complex.cos (zetaZeroData.gamma n*(t:ℂ))) =
      ((Real.pi^(1/4:ℝ)/4:ℝ):ℂ)*
        (∫ t : ℝ in Ioi 0, (romikPhi (a+t):ℂ)*
          Complex.cos (zetaZeroData.gamma n*(t:ℂ))) := by
    calc
      _ = ∫ t : ℝ in Ioi 0, ((Real.pi^(1/4:ℝ)/4:ℝ):ℂ)*
          ((romikPhi (a+t):ℂ)*Complex.cos (zetaZeroData.gamma n*(t:ℂ))-
            q*((romikPhi t:ℂ)*Complex.cos (zetaZeroData.gamma n*(t:ℂ)))) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only [Pi.sub_apply, Pi.add_apply]
        have ht0 : 0 < t := ht
        rw [correctedGaussian_actualSuzukiEvenB ha, abs_of_pos ht0]
        ring
      _ = _ := by
        rw [integral_const_mul, integral_sub hI (hI0.const_mul q),
          integral_const_mul, actual_unshifted_phi_spectrum_zero, mul_zero, sub_zero]
  refine ⟨n, ?_⟩
  rw [heq]
  exact mul_ne_zero (by exact_mod_cast (by positivity : Real.pi^(1/4:ℝ)/4 ≠ 0)) hn

/-- This explicit smaller-shift centered Gaussian simultaneously supplies
    original physical H6, actual zero mean, all shifted Gamma domains, and
    a genuinely integrable nonzero ordinary full-line exponential transform
    of the actual even-B profile at an actual complex spectral node. -/
theorem small_shift_actual_centered_gaussian_full_spectrum_witness :
    let a : ℝ := Real.log (4/3:ℝ)/2
    ∃ F : ℝ → ℂ,
      F = correctedGaussian a (centeredGaussianCharge a) ∧
      originalPhysicalH6 F ∧ actualSuzukiMeanCharge F = 0 ∧
      (∀ c : ℝ, originalGammaFormDomain c F) ∧
      ∃ n : ℕ,
        Integrable (fun r : ℝ => actualSuzukiEvenBProfile F r*
          Complex.exp (Complex.I*zetaZeroData.gamma n*(r:ℂ))) volume ∧
        (∫ r : ℝ, actualSuzukiEvenBProfile F r*
          Complex.exp (Complex.I*zetaZeroData.gamma n*(r:ℂ))) ≠ 0 := by
  dsimp only
  let a : ℝ := Real.log (4/3:ℝ)/2
  let q : ℂ := centeredGaussianCharge a
  have ha : 0 ≤ a := small_shift_positive.le
  obtain ⟨n, hn⟩ := correctedGaussian_cosine_nonzero_of_scale_ge_four ha
    small_shift_scale_ge_four q
  have hz : |(zetaZeroData.gamma n).im| ≤ 1/2 :=
    RhTransient.ActualZeroCosineNonzero.actual_gamma_half_strip n
  obtain ⟨hI, hfold⟩ := correctedGaussian_evenB_full_exponential_fold ha q
    (zetaZeroData.gamma n) hz
  refine ⟨correctedGaussian a q, rfl, correctedGaussian_original_h6 a q,
    centeredGaussian_actual_mean_zero a,
    (fun c => correctedGaussian_originalGammaFormDomain ha q c), n, hI, ?_⟩
  rw [hfold]
  exact mul_ne_zero (by norm_num) hn

#print axioms phi_derivative_small_shift_negative
#print axioms actual_small_shift_phi_spectrum_nonzero
#print axioms small_shift_actual_centered_gaussian_full_spectrum_witness

end D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft
