/- GID: D5/S3/Analytic/XuYangMillsRemainder/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/XuYangMillsRemainder/Result
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.Convolution, mathlib/module/Mathlib.Analysis.Calculus.Taylor]
   utility: none
   digest: Positive Laplace kernels prove complete monotonicity of Mills remainders. -/

/-
admission_basis: open-problem-resolution (#22549; Proved).
Utility none: analytic functions and unbounded-index identities, not finite certificates.
The zero coefficients are normalization steps, not independent numerical results.
Frozen declaration keys (GID; full Lean name; declaration statement_id):
F1 = D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay; D5.S3.FluidDynamics.Fourier.PeriodicAllenCahnDecay.deriv_integral_compact; sha256:b1660874f86eb61eaff50684fa028726415c77303e31d4d36420ca79ab53fd38
F2 = D5/S3/Analytic/ExpRemainderDifferences; D5.S3.Analytic.ExpRemainderDifferences.R; sha256:9bed1ab6867c4a7b1c0405be2310e37e6e4f7aeb4053092151ecce122f494f6b
The same-delivery publicization of TwoScaleEndpointMoments.exponential_moment
preserves its statement and proof; its current declaration statement_id is
sha256:902b92c60a225d79b8da0719443881b1494c8ed89263669f5e2b718195a0393b.
It is expanded to its Mathlib-only proof for the frozen-dependency column below.
Publicized owner judgment: owner module GID | full Lean name | declaration statement_id | proof_shape | frozen deps | escape_witness | consumers.
  D5/S3/Analytic/ExponentialSum/TwoScaleEndpointMoments | TwoScaleEndpointMoments.exponential_moment | sha256:902b92c60a225d79b8da0719443881b1494c8ed89263669f5e2b718195a0393b | bind-only (existing owner publicization; statement and proof unchanged) | none (Mathlib only) | none | JMomentIntegrable,kernelLaplace,remainderKernelMoments,remainderLaplaceRec,remainderRepresentation,result; TwoScaleEndpointMoments.shape_moment; Reg.D5.S3.Analytic.ExponentialSum.TwoScaleEndpointMoments.ExponentialMoment.family,Reg.D5.S3.Analytic.ExponentialSum.TwoScaleEndpointMoments.ExponentialMoment.registration
Per-declaration judgment: name | proof_shape | frozen deps | escape_witness | consumers.
All rows have this module's admission_basis; definitions are bind-only (definition).
  CompletelyMonotoneOn | bind-only | none | none | claim,laplaceCM,result
  millsRatio | bind-only | none | none | Y,millsLaplace,millsSquareConvolution,D_two,remainderRepresentation
  Y | bind-only | none | none | D,D_rec,D_two
  u | bind-only | none | none | D,u_special,u_kernel_coeff,u_kernel_factorial,u_one_zero,u_two_zero,D_rec,D_two,remainderRepresentation
  D | bind-only | none | none | claim,D_rec,D_two,remainderRepresentation,result
  claim | bind-only | none | none | result
  millsLaplace | bind-only | none | none | millsSquareConvolution,remainderRepresentation
  millsLaplaceIntegrable | bind-only | none | none | millsSquareConvolution
  millsSquareConvolution | bind-only | none | none | remainderRepresentation
  convolutionClosed | bind-only | none | none | remainderRepresentation
  moment | bind-only | none | none | momentDeriv,momentIterated,laplaceCM,remainderLaplaceRec,remainderRepresentation,result
  momentDeriv | bind-only | none | none | momentIterated,laplaceCM
  momentIterated | content | none | momentIterated | laplaceCM
  laplaceCM | content | none | momentIterated | result
  coeff | bind-only | none | none | coeff_zero,coeff_rec,coeff_sum,coeff_factorial,u_special,u_kernel_coeff,u_kernel_factorial,u_one_zero,u_two_zero
  intPow | bind-only | none | none | intPow_rec,coeff_sum,intWeight_eq,u_kernel_coeff
  intWeight | bind-only | none | none | intWeight_eq,u_kernel_coeff,u_kernel_factorial,remainderLaplaceRec,remainderRepresentation
  intPow_rec | bind-only | none | none | coeff_sum,intWeight_eq
  coeff_zero | bind-only | none | none | coeff_sum,u_one_zero,u_two_zero
  coeff_rec | bind-only | none | none | coeff_sum,u_one_zero,u_two_zero
  coeff_sum | content | none | coeff_sum | u_kernel_coeff
  intWeight_eq | bind-only | none | none | u_kernel_coeff
  coeff_factorial | bind-only | none | none | u_kernel_factorial
  u_special | bind-only | none | none | u_kernel_coeff,u_one_zero,u_two_zero
  u_kernel_coeff | content | none | coeff_sum | u_kernel_factorial
  u_kernel_factorial | content | none | coeff_sum | remainderRepresentation
  u_one_zero | bind-only | none | none | D_two
  u_two_zero | bind-only | none | none | D_two
  D_rec | bind-only | none | none | remainderRepresentation
  D_two | bind-only | none | none | remainderRepresentation
  J | bind-only | none | none | q0,q1,q2,K,JDeriv,q0Deriv,q1Deriv,kernelIdentity,JBound,JMomentIntegrable,JMomentTendsto,kernelLaplace,remainderRepresentation
  q0 | bind-only | none | none | q0Deriv,kernelIdentity,kernelLaplace,remainderRepresentation
  q1 | bind-only | none | none | q0Deriv,q1Deriv,kernelLaplace
  q2 | bind-only | none | none | q1Deriv,kernelIdentity,kernelLaplace
  K | bind-only | none | none | kernelIdentity,kernelLaplace,remainderRepresentation
  JDeriv | bind-only | F1 | none | q0Deriv,q1Deriv,JMomentIntegrable
  q0Deriv | bind-only | F1 | none | kernelLaplace
  q1Deriv | bind-only | F1 | none | kernelLaplace
  kernelIdentity | bind-only | none | none | kernelLaplace
  JBound | bind-only | none | none | JMomentIntegrable,JMomentTendsto
  JMomentIntegrable | bind-only | F1 | none | kernelLaplace
  JMomentTendsto | bind-only | none | none | kernelLaplace
  laplaceIBP | bind-only | none | none | kernelLaplace
  kernelLaplace | bind-only | F1 | none | remainderRepresentation
  expRemainder | bind-only | F2 | none | expRemainder_eq,expRemainderBounds,expRemainderContinuous,expRemainderRec,remainderKernel,remainderKernelContinuous,remainderKernelBounds,remainderKernelRec,remainderRepresentation
  expRemainder_eq | bind-only | F2 | none | expRemainderBounds,expRemainderRec,remainderRepresentation
  expRemainderBounds | bind-only | F2 | none | remainderKernelBounds
  expRemainderContinuous | bind-only | F2 | none | remainderKernelContinuous,remainderKernelBounds,remainderKernelRec
  expRemainderRec | bind-only | F2 | none | remainderKernelRec
  remainderKernel | bind-only | F2 | none | remainderKernelContinuous,remainderKernelBounds,remainderKernelMoments,remainderKernelRec,remainderLaplaceRec,remainderRepresentation,result
  remainderKernelContinuous | bind-only | F2 | none | remainderKernelMoments,result
  remainderKernelBounds | bind-only | F2 | none | remainderKernelMoments,result
  remainderKernelMoments | bind-only | F2 | none | remainderLaplaceRec,result
  remainderKernelRec | bind-only | F2 | none | remainderLaplaceRec
  remainderLaplaceRec | bind-only | F2 | none | remainderRepresentation
  remainderRepresentation | content | F1,F2 | remainderRepresentation | result
  result | content | F1,F2 | remainderRepresentation | terminal
The source requires C-infinity; ContDiffOn at order omega is stronger.
-/

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.Taylor
import D5.S3.FluidDynamics.Fourier.PeriodicAllenCahnDecay
import D5.S3.Analytic.ExponentialSum.TwoScaleEndpointMoments
import D5.S3.Analytic.ExpRemainderDifferences

/-! Exact positive Laplace kernels for all signed Mills-ratio remainders. -/

open Set Real MeasureTheory Filter
open scoped Topology ContDiff Interval
noncomputable section
namespace D5.S3.Analytic.XuYangMillsRemainder.Result
/-- Complete monotonicity as C-infinity and all signed derivatives nonnegative. -/
def CompletelyMonotoneOn (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ f (Ioi 0) ∧
    ∀ m : ℕ, ∀ x : ℝ, 0 < x → 0 ≤ (-1:ℝ)^m * iteratedDeriv m f x

/-- The Gaussian Mills ratio in the source's normalization. -/
def millsRatio (x : ℝ) : ℝ :=
  exp (x ^ 2 / 2) * ∫ t in Ioi x, exp (-t ^ 2 / 2)

/-- Equation (1.8). -/
def Y (a b x : ℝ) : ℝ := (x ^ 2 + a) * millsRatio x ^ 2 + b * x * millsRatio x

/-- Equation (3.7), with its original Gamma factors. -/
def u (k : ℕ) (a b : ℝ) : ℝ :=
  (b + 1) * 2 ^ k * Gamma (k + 1 / 2) / Gamma (1 / 2) +
    (k - a) * (k - 1).factorial *
      ∑ j ∈ Finset.range k, 2 ^ j * Gamma (j + 1 / 2) / (Gamma (1 / 2) * j.factorial)

/-- The asymptotic remainder of Conjecture 7.1. -/
def D (n : ℕ) (x a : ℝ) : ℝ :=
  Y a (a - 2) x - (a - 1 + ∑ k ∈ Finset.Icc 1 n, (-1 : ℝ) ^ k * u k a (a - 2) / x ^ (2 * k))

/-- Conjecture 7.1 with the necessary lower bound on the truncation index. -/
def claim : Prop :=
  ∀ n : ℕ, 2 ≤ n → CompletelyMonotoneOn (fun x => (-1 : ℝ) ^ n * D n x (-1))


lemma millsLaplace (x : ℝ) :
    millsRatio x = ∫ t in Ioi (0 : ℝ), exp (-x * t - t ^ 2 / 2) := by
  have hs : (∫ t in Ioi (0 : ℝ), exp (-(t + x) ^ 2 / 2)) =
      ∫ t in Ioi x, exp (-t ^ 2 / 2) := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
    convert integral_add_right_eq_self (μ := volume) ((Ioi x).indicator (fun t : ℝ => exp (-t ^ 2 / 2))) x using 1
    congr 1
    ext t
    by_cases ht : 0 < t
    · rw [indicator_of_mem (show t ∈ Ioi 0 from ht), indicator_of_mem (show t + x ∈ Ioi x by simpa only [mem_Ioi, lt_add_iff_pos_left] using ht)]
    · rw [indicator_of_notMem (show t ∉ Ioi 0 from ht), indicator_of_notMem (show t + x ∉ Ioi x by simpa only [mem_Ioi, lt_add_iff_pos_left] using ht)]
  rw [millsRatio, ← hs, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [← exp_add]
  congr 1
  ring

private lemma millsLaplaceIntegrable {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ => exp (-x * t - t ^ 2 / 2)) (Ioi 0) := by
  apply (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)).integrableOn.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_of_nonneg (exp_nonneg _)]
  apply exp_le_exp.mpr
  nlinarith [mul_nonneg hx ht.le]

lemma millsSquareConvolution {x : ℝ} (hx : 0 ≤ x) :
    millsRatio x ^ 2 = ∫ t in Ioi (0 : ℝ), exp (-x * t) *
      ∫ s in 0..t, exp (-s ^ 2 / 2) * exp (-(t-s)^2/2) := by
  rw [millsLaplace, pow_two]
  have hc := integral_posConvolution
    (millsLaplaceIntegrable hx) (millsLaplaceIntegrable hx) (ContinuousLinearMap.mul ℝ ℝ)
  simp only [ContinuousLinearMap.mul_apply'] at hc
  rw [← hc]
  apply integral_congr_ae
  filter_upwards with t
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [ContinuousLinearMap.mul_apply']
  rw [← exp_add, ← mul_assoc, ← exp_add, ← exp_add]
  congr 1
  ring

lemma convolutionClosed (t : ℝ) :
    (∫ s in 0..t, exp (-s ^ 2 / 2) * exp (-(t-s)^2/2)) =
      t * ∫ v in (0:ℝ)..1, exp (-(1+v^2)*t^2/4) := by
  let f := fun v : ℝ => exp (-(1+v^2)*t^2/4)
  have hi : IntervalIntegrable f volume (-1) 0 := by apply Continuous.intervalIntegrable; fun_prop
  have hj : IntervalIntegrable f volume 0 1 := by apply Continuous.intervalIntegrable; fun_prop
  have heven : (∫ v in (-1:ℝ)..0, f v) = ∫ v in (0:ℝ)..1, f v := by
    have hn := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := 1) f
    norm_num only [neg_zero] at hn
    rw [← hn]
    apply intervalIntegral.integral_congr
    intro v _
    dsimp [f]
    rw [neg_sq]
  have hs : (∫ v in (-1:ℝ)..1, f v) = 2 * ∫ v in (0:ℝ)..1, f v := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi hj, heven]
    ring
  by_cases ht : t = 0
  · subst t; simp
  have hc := intervalIntegral.integral_comp_mul_add
    (fun s : ℝ => exp (-s^2/2) * exp (-(t-s)^2/2))
    (a := (-1:ℝ)) (b := 1) (c := t/2) (by exact div_ne_zero ht (by norm_num)) (t/2)
  have hf : (fun v : ℝ => exp (-(t/2*v+t/2)^2/2) * exp (-(t-(t/2*v+t/2))^2/2)) = f := by
    ext v
    dsimp [f]
    rw [← exp_add]
    congr 1
    ring
  rw [hf] at hc
  norm_num at hc
  rw [hs] at hc
  dsimp [f] at hc
  field_simp at hc
  simpa only [neg_div, neg_mul] using hc.symm

def moment (f : ℝ → ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  ∫ t in Ioi (0:ℝ), (-t)^m * exp (-x*t) * f t

private lemma momentDeriv {f : ℝ → ℝ} (hf : Continuous f)
    (hp : ∀ t : ℝ, 0 < t → 0 ≤ f t)
    (hi : ∀ m : ℕ, ∀ x : ℝ, 0 < x →
      IntegrableOn (fun t : ℝ => t^m * exp (-x*t) * f t) (Ioi 0))
    (m : ℕ) {x : ℝ} (hx : 0 < x) : HasDerivAt (moment f m) (moment f (m+1) x) x := by
  have hint (m : ℕ) (x : ℝ) (hx : 0 < x) :
      IntegrableOn (fun t : ℝ => (-t)^m * exp (-x*t) * f t) (Ioi 0) := by
    apply ((hi m x hx).const_mul ((-1:ℝ)^m)).congr
    filter_upwards with t
    rw [neg_eq_neg_one_mul, mul_pow]
    ring
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0:ℝ))) (F := fun x t : ℝ => (-t)^m * exp (-x*t) * f t)
    (F' := fun x t : ℝ => (-t)^(m+1) * exp (-x*t) * f t)
    (s := Ioi (x/2)) (bound := fun t : ℝ => t^(m+1)*exp (-(x/2)*t)*f t)
    (Ioi_mem_nhds (by linarith : x/2 < x))
    (Eventually.of_forall (fun _ => by fun_prop)) (hint m x hx) (by fun_prop)
    ?_ (hi (m+1) (x/2) (half_pos hx)) ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro y hy
    simp only [norm_mul, norm_pow, norm_neg, Real.norm_of_nonneg ht.le,
      Real.norm_of_nonneg (exp_nonneg _), Real.norm_of_nonneg (hp t ht)]
    apply mul_le_mul_of_nonneg_right _ (hp t ht)
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg ht.le _)
    apply exp_le_exp.mpr
    change x/2 < y at hy
    change 0 < t at ht
    nlinarith
  · filter_upwards with t
    intro y _
    convert ((((hasDerivAt_id y).neg.mul_const t).exp).const_mul ((-t)^m)).mul_const (f t) using 1 <;>
      simp only [Pi.neg_apply, id_eq, pow_succ] <;> ring

private lemma momentIterated {f : ℝ → ℝ} (hf : Continuous f)
    (hp : ∀ t : ℝ, 0 < t → 0 ≤ f t)
    (hi : ∀ m : ℕ, ∀ x : ℝ, 0 < x →
      IntegrableOn (fun t : ℝ => t^m * exp (-x*t) * f t) (Ioi 0))
    (m : ℕ) : EqOn (iteratedDeriv m (moment f 0)) (moment f m) (Ioi 0) := by
  induction m with
  | zero => intro x _; rfl
  | succ m ih =>
    intro x hx
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv m (moment f 0) =ᶠ[𝓝 x] moment f m :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨Ioi 0, Ioi_mem_nhds hx, fun t ht => ih ht⟩
    rw [he.deriv_eq, (momentDeriv hf hp hi m hx).deriv]

private lemma laplaceCM {f : ℝ → ℝ} (hf : Continuous f)
    (hp : ∀ t : ℝ, 0 < t → 0 ≤ f t)
    (hi : ∀ m : ℕ, ∀ x : ℝ, 0 < x →
      IntegrableOn (fun t : ℝ => t^m * exp (-x*t) * f t) (Ioi 0)) :
    CompletelyMonotoneOn (moment f 0) := by
  constructor
  · apply contDiffOn_of_differentiableOn_deriv (n := ⊤)
    intro m _ x hx
    apply DifferentiableAt.differentiableWithinAt
    have he : iteratedDerivWithin m (moment f 0) (Ioi 0) =ᶠ[𝓝 x] moment f m := by
      filter_upwards [Ioi_mem_nhds hx] with t ht
      rw [iteratedDerivWithin_of_isOpen isOpen_Ioi ht]
      exact momentIterated hf hp hi m ht
    exact (momentDeriv hf hp hi m hx).differentiableAt.congr_of_eventuallyEq he
  · intro m x hx
    rw [momentIterated hf hp hi m hx, moment, ← integral_const_mul]
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have he : (-1:ℝ)^m * (-t)^m = t^m := by
      rw [← mul_pow]; congr 1; ring
    rw [← mul_assoc, ← mul_assoc, he]
    exact mul_nonneg (mul_nonneg (pow_nonneg ht.le _) (exp_nonneg _)) (hp t ht)

def coeff (k : ℕ) : ℝ := 2 ^ k * Gamma (k + 1/2) / Gamma (1/2)
def intPow (m : ℕ) : ℝ := ∫ v in (0:ℝ)..1, (1+v^2)^m
private def intWeight (m : ℕ) : ℝ := ∫ v in (0:ℝ)..1, v^2*(1-v^2)*(1+v^2)^m
lemma intPow_rec (m : ℕ) :
    (2*(m:ℝ)+3)*intPow (m+1) - 2*(m+1)*intPow m = 2^(m+1) := by
  have hd (v : ℝ) : HasDerivAt (fun v : ℝ => v*(1+v^2)^(m+1))
      ((2*(m:ℝ)+3)*(1+v^2)^(m+1)-2*(m+1)*(1+v^2)^m) v := by
    convert (hasDerivAt_id v).mul (((hasDerivAt_id v).pow 2).const_add 1 |>.pow (m+1)) using 1
    · rfl
    · simp only [Pi.pow_apply, id_eq, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.add_sub_cancel, pow_succ]
      ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v)
    (show IntervalIntegrable (fun v : ℝ => (2*(m:ℝ)+3)*(1+v^2)^(m+1)-2*(m+1)*(1+v^2)^m) volume 0 1 by
      apply Continuous.intervalIntegrable; fun_prop)
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at h
  simpa [intPow, show (1:ℝ)+1 = 2 by norm_num] using h
private lemma coeff_zero : coeff 0 = 1 := by
  simp only [coeff, Nat.cast_zero, zero_add, pow_zero, one_mul]
  exact div_self (ne_of_gt (Gamma_pos_of_pos (by norm_num)))
private lemma coeff_rec (m : ℕ) : coeff (m+1) = (2*(m:ℝ)+1)*coeff m := by
  unfold coeff
  rw [show (↑(m+1):ℝ)+1/2 = ((m:ℝ)+1/2)+1 by push_cast; ring,
    Gamma_add_one (by positivity), pow_succ]
  ring
lemma coeff_sum (m : ℕ) :
    (∑ j ∈ Finset.range (m+1), coeff j / j.factorial) =
      coeff (m+1) / (2^m * m.factorial) * intPow m := by
  induction m with
  | zero => simp [coeff_zero, coeff_rec, intPow]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, coeff_rec (m+1), Nat.factorial_succ, pow_succ]
    have hm : (m+1:ℝ) ≠ 0 := by positivity
    have hf : (m.factorial:ℝ) ≠ 0 := by positivity
    have hp : (2:ℝ)^m ≠ 0 := by positivity
    have hr := intPow_rec m
    push_cast at *
    field_simp
    simp only [pow_succ] at hr
    linear_combination -coeff (m+1) * hr
private lemma intWeight_eq (m : ℕ) :
    2*((m:ℝ)+1)*(m+2)*intWeight m =
      2^(m+3) - (m+4)*intPow (m+2) := by
  have hw : intWeight m = -intPow (m+2)+3*intPow (m+1)-2*intPow m := by
    unfold intWeight intPow
    rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop),
      ← intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop)]
    apply intervalIntegral.integral_congr
    intro v _
    simp only [pow_succ]
    ring
  have h0 := intPow_rec m
  have h1 := intPow_rec (m+1)
  rw [hw]
  push_cast at h1
  simp only [pow_succ] at h0 h1 ⊢
  nlinarith [h0, h1]
lemma coeff_factorial (m : ℕ) :
    coeff (m+1)*(2^m*m.factorial) = (2*m+1).factorial := by
  have hfac := Nat.factorial_eq_mul_doubleFactorial (2*m)
  rw [Nat.doubleFactorial_two_mul] at hfac
  have hfacR : ((2*m+1).factorial:ℝ) =
      ((2*m+1).doubleFactorial:ℝ)*(2^m*m.factorial) := by exact_mod_cast hfac
  unfold coeff
  push_cast
  rw [Gamma_nat_add_one_add_half, Gamma_one_half_eq, hfacR]
  have hs : Real.sqrt Real.pi ≠ 0 := Real.sqrt_ne_zero'.mpr Real.pi_pos
  field_simp
private lemma u_special (m : ℕ) :
    u (m+1) (-1) (-3) = -2*coeff (m+1)+(m+2)*m.factorial *
      (∑ j ∈ Finset.range (m+1), coeff j / j.factorial) := by
  simp only [u, coeff, Nat.add_sub_cancel]
  push_cast
  congr 1
  · ring
  · congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro j _
      ring
private lemma u_kernel_coeff (m : ℕ) :
    u (m+3) (-1) (-3) =
      -(coeff (m+3)*((m:ℝ)+1)*(m+2)/2^(m+1))*intWeight m := by
  have hs := coeff_sum (m+2)
  have hw := intWeight_eq m
  have hu := u_special (m+2)
  rw [hu, hs]
  push_cast
  have hf : ((m+2).factorial:ℝ) ≠ 0 := by positivity
  have hp : (2:ℝ)^(m+1) ≠ 0 := by positivity
  have hq : (2:ℝ)^(m+2) ≠ 0 := by positivity
  field_simp
  simp only [pow_succ] at hw ⊢
  linear_combination coeff (m+3) * 2^m * 2 * hw
private lemma u_kernel_factorial (m : ℕ) :
    u (m+3) (-1) (-3) =
      -((2*m+5).factorial:ℝ)/(8*4^m*m.factorial)*intWeight m := by
  rw [u_kernel_coeff]
  have hc := coeff_factorial (m+2)
  rw [show m+2+1 = m+3 by omega, show 2*(m+2)+1 = 2*m+5 by omega] at hc
  rw [Nat.factorial_succ, Nat.factorial_succ] at hc
  push_cast at hc
  have hp : (2:ℝ)^(m+1) ≠ 0 := by positivity
  have hq : (4:ℝ)^m ≠ 0 := by positivity
  have hf : (m.factorial:ℝ) ≠ 0 := by positivity
  have he : (4:ℝ)^m = (2^m)^2 := by
    calc (4:ℝ)^m = (2^2)^m := by norm_num
         _ = (2^m)^2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [he]
  field_simp
  simp only [pow_succ] at hc ⊢
  linear_combination -(2^m)*2*intWeight m * hc
private lemma u_one_zero : u 1 (-1) (-3) = 0 := by
  have h := u_special 0
  norm_num [coeff_rec, coeff_zero, Finset.sum_range_succ] at h
  exact h
private lemma u_two_zero : u 2 (-1) (-3) = 0 := by
  have h := u_special 1
  norm_num [coeff_rec, coeff_zero, Finset.sum_range_succ] at h
  exact h
private lemma D_rec (r : ℕ) (x : ℝ) :
    D (r+3) x (-1) = D (r+2) x (-1) -
      (-1:ℝ)^(r+3)*u (r+3) (-1) (-3)/x^(2*(r+3)) := by
  simp only [D, show (-1:ℝ)-2 = -3 by norm_num]
  rw [Finset.sum_Icc_succ_top (a := 1) (b := r+2) (by omega)]
  ring
private lemma D_two (x : ℝ) :
    D 2 x (-1) = (x^2-1)*millsRatio x^2-3*x*millsRatio x+2 := by
  norm_num [D, Y, show Finset.Icc 1 2 = {1,2} by decide, u_one_zero, u_two_zero]
  ring

def J (p : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ v in (0:ℝ)..1, p v * exp (-(1+v^2)*t^2/4)
def q0 (t : ℝ) : ℝ := t * J (fun _ => 1) t
private def q1 (t : ℝ) : ℝ := J (fun _ => 1) t - t^2/2 * J (fun v => 1+v^2) t
private def q2 (t : ℝ) : ℝ := t^3/4 * J (fun v => (1+v^2)^2) t - 3*t/2 * J (fun v => 1+v^2) t
def K (t : ℝ) : ℝ := t^5/8 * J (fun v => v^2*(1-v^2)) t

private lemma JDeriv (p : ℝ → ℝ) (hp : Continuous p) (t : ℝ) :
    HasDerivAt (J p) (-(t/2) * J (fun v => p v*(1+v^2)) t) t := by
  have hd (y v : ℝ) : HasDerivAt (fun y => p v * exp (-(1+v^2)*y^2/4))
      (-(y/2) * (p v*(1+v^2)) * exp (-(1+v^2)*y^2/4)) y := by
    convert (((hasDerivAt_id y).pow 2 |>.const_mul (-(1+v^2)) |>.div_const 4).exp).const_mul (p v) using 1 <;> (try ext z) <;> dsimp <;> ring
  have h := D5.S3.FluidDynamics.Fourier.PeriodicAllenCahnDecay.deriv_integral_compact
    (F := fun y v => p v*exp (-(1+v^2)*y^2/4))
    (H := fun y v => -(y/2)*(p v*(1+v^2))*exp (-(1+v^2)*y^2/4))
    (a := 0) (b := 1) (t := t) (δ := 1) zero_le_one zero_lt_one
    (by fun_prop) (by fun_prop) (fun y _ v _ => hd y v)
  change HasDerivAt (J p) _ t at h
  rw [show (∫ v in (0:ℝ)..1, -(t/2)*(p v*(1+v^2))*exp (-(1+v^2)*t^2/4)) =
      -(t/2)*J (fun v => p v*(1+v^2)) t by
    rw [J, ← intervalIntegral.integral_const_mul]
    congr 1; ext v; ring] at h
  exact h

private lemma q0Deriv (t : ℝ) : HasDerivAt q0 (q1 t) t := by
  have h := (hasDerivAt_id t).mul (JDeriv (fun _ => 1) continuous_const t)
  convert h using 1 <;> (try ext z) <;> dsimp [q0,q1] <;> simp only [one_mul] <;> ring

private lemma q1Deriv (t : ℝ) : HasDerivAt q1 (q2 t) t := by
  have h := (JDeriv (fun _ => 1) continuous_const t).sub
    (((hasDerivAt_id t).pow 2 |>.div_const 2).mul (JDeriv (fun v => 1+v^2) (by fun_prop) t))
  convert h using 1 <;> (try ext z) <;> dsimp [q1,q2] <;> simp only [one_mul, ← pow_two] <;> ring

private lemma kernelIdentity (t : ℝ) :
    q2 t - q0 t + 3*t*exp (-t^2/2) = K t := by
  let e := fun v : ℝ => exp (-(1+v^2)*t^2/4)
  have hd0 (v : ℝ) : HasDerivAt (fun v : ℝ => v*e v) ((1-v^2*t^2/2)*e v) v := by
    dsimp [e]
    convert (hasDerivAt_id v).mul ((((hasDerivAt_id v).pow 2).const_add 1 |>.neg |>.mul_const (t^2) |>.div_const 4).exp) using 1 <;> (try ext z) <;> dsimp <;> ring
  have hd1 (v : ℝ) : HasDerivAt (fun v : ℝ => v*(1-v^2)*e v)
      ((1-3*v^2-t^2/2*(v^2-v^4))*e v) v := by
    dsimp [e]
    convert ((hasDerivAt_id v).mul ((hasDerivAt_const v 1).sub ((hasDerivAt_id v).pow 2))).mul
      ((((hasDerivAt_id v).pow 2).const_add 1 |>.neg |>.mul_const (t^2) |>.div_const 4).exp) using 1 <;> (try ext z) <;> dsimp <;> ring
  have h0 := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd0 v)
    (show IntervalIntegrable (fun v => (1-v^2*t^2/2)*e v) volume 0 1 by apply Continuous.intervalIntegrable; dsimp [e]; fun_prop)
  have h1 := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd1 v)
    (show IntervalIntegrable (fun v => (1-3*v^2-t^2/2*(v^2-v^4))*e v) volume 0 1 by apply Continuous.intervalIntegrable; dsimp [e]; fun_prop)
  dsimp [e] at h0 h1
  simp only [one_pow, zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 4 ≠ 0),
    mul_zero, zero_mul, one_mul, sub_self, zero_sub, sub_zero] at h0 h1
  have hj : J (fun v => 1-3*v^2-t^2/2*(v^2-v^4)) t = 0 := by simpa only [J] using h1
  have he : J (fun v => 1-v^2*t^2/2) t = exp (-t^2/2) := by
    change (∫ v in (0:ℝ)..1, (1-v^2*t^2/2)*exp (-(1+v^2)*t^2/4)) = _
    convert h0 using 1 <;> congr 1 <;> ring
  unfold q2 q0 K
  rw [← he]
  have hh : J (fun v => 1-3*v^2) t = t^2/2 * J (fun v => v^2*(1-v^2)) t := by
    have h := hj
    unfold J at h ⊢
    rw [← intervalIntegral.integral_const_mul, ← sub_eq_zero]
    rw [← intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    convert h using 1
    congr 1
    ext v
    ring
  have hx : t^3/4 * J (fun v => (1+v^2)^2) t - 3*t/2*J (fun v => 1+v^2) t -
      t*J (fun _ => 1) t + 3*t*J (fun v => 1-v^2*t^2/2) t =
      t^3/4*J (fun v => 1-3*v^2) t + t/2*J (fun v => 1-3*v^2-t^2/2*(v^2-v^4)) t := by
    unfold J
    repeat rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    rw [← intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    rw [← intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    rw [← intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    apply intervalIntegral.integral_congr
    intro v _
    ring
  rw [hx,hj,hh]
  ring
private lemma JBound (p : ℝ → ℝ) (hp : Continuous p) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, ‖J p t‖ ≤ C := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0:ℝ) 1) hp.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (C := max C 0)
    (a := (0:ℝ)) (b := 1) (f := fun v => p v*exp (-(1+v^2)*t^2/4)) (fun v hv => by
      have hv' : v ∈ Icc (0:ℝ) 1 := Ioc_subset_Icc_self (by simpa only [uIoc_of_le zero_le_one] using hv)
      rw [norm_mul, Real.norm_of_nonneg (exp_nonneg _)]
      have he : exp (-(1+v^2)*t^2/4) ≤ 1 := exp_le_one_iff.mpr (by
        have h : 0 ≤ (1+v^2)*t^2 := by positivity
        nlinarith [h])
      exact (mul_le_mul_of_nonneg_left he (norm_nonneg _)).trans (by simpa only [mul_one] using (hC v hv').trans (le_max_left C (0:ℝ))))
  simpa only [J, sub_zero, abs_one, mul_one] using h

lemma JMomentIntegrable (p : ℝ → ℝ) (hp : Continuous p) (m : ℕ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => t^m*exp (-x*t)*J p t) (Ioi 0) := by
  obtain ⟨C,hC,hbound⟩ := JBound p hp
  have hcont : Continuous (J p) := continuous_iff_continuousAt.mpr (fun t => (JDeriv p hp t).continuousAt)
  have he := (TwoScaleEndpointMoments.exponential_moment x hx m).1
  simp only [← neg_mul] at he
  apply (he.mul_const C).mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, Real.norm_of_nonneg (mul_nonneg (pow_nonneg ht.le _) (exp_nonneg _))]
  exact mul_le_mul_of_nonneg_left (hbound t) (mul_nonneg (pow_nonneg ht.le _) (exp_nonneg _))

private lemma JMomentTendsto (p : ℝ → ℝ) (hp : Continuous p) (m : ℕ) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun t : ℝ => t^m*exp (-x*t)*J p t) atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := JBound p hp
  have hlim : Tendsto (fun t : ℝ => t^m*exp (-x*t)*C) atTop (𝓝 0) := by
    simpa only [rpow_natCast, zero_mul] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (m:ℝ) x hx).mul_const C
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  rw [norm_mul, Real.norm_of_nonneg (mul_nonneg (pow_nonneg ht _) (exp_nonneg _))]
  exact mul_le_mul_of_nonneg_left (hbound t) (mul_nonneg (pow_nonneg ht _) (exp_nonneg _))

lemma laplaceIBP {f g : ℝ → ℝ} {x : ℝ}
    (hd : ∀ t, HasDerivAt f (g t) t)
    (hf : IntegrableOn (fun t => exp (-x*t)*f t) (Ioi 0))
    (hg : IntegrableOn (fun t => exp (-x*t)*g t) (Ioi 0))
    (hl : Tendsto (fun t => exp (-x*t)*f t) atTop (𝓝 0)) :
    (∫ t in Ioi (0:ℝ), exp (-x*t)*g t) = x*(∫ t in Ioi (0:ℝ), exp (-x*t)*f t)-f 0 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := (0:ℝ)) (f := fun t => exp (-x*t)*f t)
    (f' := fun t => exp (-x*t)*g t-x*(exp (-x*t)*f t))
    (fun t _ => by convert (((hasDerivAt_id t).const_mul (-x)).exp).mul (hd t) using 1 <;> (try ext z) <;> dsimp <;> ring)
    (hg.sub (hf.const_mul x)) hl
  rw [integral_sub hg (hf.const_mul x), integral_const_mul] at h
  simp only [mul_zero, exp_zero, one_mul, zero_sub] at h
  linarith
lemma kernelLaplace {x : ℝ} (hx : 0 < x) (r : ℝ)
    (hr : r = ∫ t in Ioi (0:ℝ), exp (-x*t)*exp (-t^2/2))
    (hr2 : r^2 = ∫ t in Ioi (0:ℝ), exp (-x*t)*q0 t) :
    (x^2-1)*r^2-3*x*r+2 = ∫ t in Ioi (0:ℝ), exp (-x*t)*K t := by
  have h0 : IntegrableOn (fun t => exp (-x*t)*q0 t) (Ioi 0) := by
    convert JMomentIntegrable (fun _ => 1) continuous_const 1 hx using 1
    ext t; dsimp [q0]; ring
  have h1 : IntegrableOn (fun t => exp (-x*t)*q1 t) (Ioi 0) := by
    convert (JMomentIntegrable (fun _ => 1) continuous_const 0 hx).sub
      ((JMomentIntegrable (fun v => 1+v^2) (by fun_prop) 2 hx).div_const 2) using 1
    ext t; dsimp [q1]; ring
  have h2 : IntegrableOn (fun t => exp (-x*t)*q2 t) (Ioi 0) := by
    apply (((JMomentIntegrable (fun v => (1+v^2)^2) (by fun_prop) 3 hx).div_const 4).sub
      ((JMomentIntegrable (fun v => 1+v^2) (by fun_prop) 1 hx).const_mul (3/2))).congr
    filter_upwards with t
    dsimp [q2]; ring
  have l0 : Tendsto (fun t => exp (-x*t)*q0 t) atTop (𝓝 0) := by
    convert JMomentTendsto (fun _ => 1) continuous_const 1 hx using 1
    ext t; dsimp [q0]; ring
  have l1 : Tendsto (fun t => exp (-x*t)*q1 t) atTop (𝓝 0) := by
    have h := (JMomentTendsto (fun _ => 1) continuous_const 0 hx).sub
      ((JMomentTendsto (fun v => 1+v^2) (by fun_prop) 2 hx).div_const 2)
    convert h using 1
    · ext t; simp only [q1,pow_zero,one_mul]; ring
    · norm_num
  have ib0 := laplaceIBP q0Deriv h0 h1 l0
  have ib1 := laplaceIBP q1Deriv h1 h2 l1
  have z0 : q0 0 = 0 := by simp [q0]
  have z1 : q1 0 = 1 := by norm_num [q1,J]
  rw [z0, sub_zero] at ib0
  rw [z1] at ib1
  have hh : IntegrableOn (fun t : ℝ => exp (-x*t)*exp (-t^2/2)) (Ioi 0) := by
    have he := (TwoScaleEndpointMoments.exponential_moment x hx 0).1
    simp only [← neg_mul] at he
    apply he.mono' (by fun_prop)
    filter_upwards with t
    simp only [pow_zero,one_mul,Real.norm_of_nonneg (mul_nonneg (exp_nonneg _) (exp_nonneg _))]
    exact mul_le_of_le_one_right (exp_nonneg _) (exp_le_one_iff.mpr (by nlinarith [sq_nonneg t]))
  have hth : IntegrableOn (fun t : ℝ => exp (-x*t)*(-t*exp (-t^2/2))) (Ioi 0) := by
    have he := (TwoScaleEndpointMoments.exponential_moment x hx 1).1
    simp only [← neg_mul] at he
    apply he.mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul,norm_mul,Real.norm_of_nonneg (exp_nonneg _),norm_neg,
      Real.norm_of_nonneg ht.le, Real.norm_of_nonneg (exp_nonneg _)]
    simp only [pow_one]
    nlinarith [mul_le_of_le_one_right (mul_nonneg (exp_nonneg (-x*t)) ht.le)
      (exp_le_one_iff.mpr (by nlinarith [sq_nonneg t]) : exp (-t^2/2) ≤ 1)]
  have lh : Tendsto (fun t : ℝ => exp (-x*t)*exp (-t^2/2)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun t : ℝ => exp (-x*t)) (fun t => ?_)
      (by simpa only [rpow_zero, one_mul] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 x hx)
    simp only [norm_mul,Real.norm_of_nonneg (exp_nonneg _)]
    exact mul_le_of_le_one_right (exp_nonneg _) (exp_le_one_iff.mpr (by nlinarith [sq_nonneg t]))
  have ibh := laplaceIBP (f := fun t : ℝ => exp (-t^2/2)) (g := fun t : ℝ => -t*exp (-t^2/2))
    (fun t => by convert (((hasDerivAt_id t).pow 2).neg.div_const 2).exp using 1 <;> (try ext z) <;> dsimp <;> ring) hh hth lh
  simp only [zero_pow (by decide : 2 ≠ 0), neg_zero, zero_div, exp_zero] at ibh
  have hk : (∫ t in Ioi (0:ℝ), exp (-x*t)*K t) =
      (∫ t in Ioi (0:ℝ), exp (-x*t)*q2 t) -
      (∫ t in Ioi (0:ℝ), exp (-x*t)*q0 t) -
      3*(∫ t in Ioi (0:ℝ), exp (-x*t)*(-t*exp (-t^2/2))) := by
    rw [← integral_sub h2 h0, ← integral_const_mul]
    change (∫ t in Ioi (0:ℝ), exp (-x*t)*K t) =
      (∫ t in Ioi (0:ℝ), ((fun t => exp (-x*t)*q2 t) - (fun t => exp (-x*t)*q0 t)) t) -
      ∫ t in Ioi (0:ℝ), 3*(exp (-x*t)*(-t*exp (-t^2/2)))
    rw [← integral_sub (h2.sub h0) (hth.const_mul 3)]
    apply integral_congr_ae
    filter_upwards with t
    rw [← kernelIdentity t]
    dsimp
    ring
  rw [hk, ib1, ib0, ← hr2, ibh, ← hr]
  ring

def expRemainder (r : ℕ) (v : ℝ) : ℝ :=
  (-1:ℝ)^r * (D5.S3.Analytic.ExpRemainderDifferences.R r (-v) + (-v)^r/r.factorial)
lemma expRemainder_eq (r : ℕ) (v : ℝ) :
    expRemainder r v = (-1:ℝ)^r * (exp (-v) - ∑ j ∈ Finset.range r, (-v)^j / j.factorial) := by
  simp only [expRemainder, D5.S3.Analytic.ExpRemainderDifferences.R, Finset.sum_range_succ]
  ring
lemma expRemainderBounds (r : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ expRemainder r v ∧ expRemainder r v ≤ v^r / r.factorial := by
  cases r with
  | zero => simpa [expRemainder_eq] using And.intro (exp_nonneg (-v)) (exp_le_one_iff.mpr (neg_nonpos.mpr hv))
  | succ r =>
    by_cases h0 : v = 0
    · subst v
      simp [expRemainder_eq, Finset.sum_range_succ']
    have hv' : 0 < v := lt_of_le_of_ne hv (Ne.symm h0)
    let f : ℝ → ℝ := fun s => exp ((-1:ℝ)*s)
    have hc : ContDiff ℝ ⊤ f := by dsimp [f]; fun_prop
    obtain ⟨w, hw, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
      (ne_of_lt hv') (hc.of_le (by exact_mod_cast le_top)).contDiffOn
    have hs : taylorWithinEval f r (uIcc 0 v) 0 v =
        ∑ j ∈ Finset.range (r+1), (-v)^j / j.factorial := by
      rw [taylor_within_apply]
      apply Finset.sum_congr rfl
      intro j _
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (ne_of_lt hv'))
        (hc.of_le (by exact_mod_cast le_top)).contDiffAt (left_mem_uIcc),
        iteratedDeriv_exp_const_mul]
      simp only [f, mul_zero, exp_zero, mul_one, sub_zero, smul_eq_mul, neg_mul, one_mul,
        div_eq_mul_inv]
      rw [neg_pow]
      ring
    rw [hs, iteratedDeriv_exp_const_mul] at he
    have hw' : 0 < w ∧ w < v := by simpa [uIoo_of_lt hv'] using hw
    have hexp : exp (-w) ≤ 1 := exp_le_one_iff.mpr (by linarith)
    have hid : expRemainder (r+1) v = exp (-w) * v^(r+1) / (r+1).factorial := by
      rw [expRemainder_eq]
      dsimp [f] at he
      simp only [neg_one_mul, sub_zero] at he
      rw [he]
      have hsgn : (-1:ℝ)^(r+1) * (-1:ℝ)^(r+1) = 1 := by
        rw [← mul_pow]; norm_num
      calc
        _ = ((-1:ℝ)^(r+1)*(-1:ℝ)^(r+1)) * exp (-w) * v^(r+1) / (r+1).factorial := by ring
        _ = _ := by rw [hsgn]; ring
    rw [hid]
    constructor
    · positivity
    · exact div_le_div_of_nonneg_right (mul_le_of_le_one_left (by positivity) hexp) (by positivity)
lemma expRemainderContinuous (r : ℕ) : Continuous (expRemainder r) := by
  unfold expRemainder D5.S3.Analytic.ExpRemainderDifferences.R
  fun_prop
lemma expRemainderRec (r : ℕ) (v : ℝ) :
    expRemainder (r+1) v = v^r / r.factorial - expRemainder r v := by
  have hs : (-1:ℝ)^r * (-v)^r = v^r := by rw [← mul_pow]; congr 1; ring
  simp only [expRemainder_eq, Finset.sum_range_succ, pow_succ]
  linear_combination hs / (r.factorial:ℝ)
private def remainderKernel (r : ℕ) (t : ℝ) : ℝ :=
  t^5/8 * ∫ v in (0:ℝ)..1, v^2*(1-v^2)*expRemainder r ((1+v^2)*t^2/4)
private lemma remainderKernelContinuous (r : ℕ) : Continuous (remainderKernel r) := by
  have hc : Continuous (fun p : ℝ × ℝ =>
      p.2^2*(1-p.2^2)*expRemainder r ((1+p.2^2)*p.1^2/4)) := by
    apply Continuous.mul (by fun_prop)
    exact (expRemainderContinuous r).comp (by fun_prop)
  have hi := continuous_parametric_integral_of_continuous (μ := volume) (f := fun t v : ℝ => v^2*(1-v^2)*expRemainder r ((1+v^2)*t^2/4)) hc (s := Icc (0:ℝ) 1) isCompact_Icc
  simp_rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)] at hi
  exact (by fun_prop : Continuous (fun t : ℝ => t^5/8)).mul hi
private lemma remainderKernelBounds (r : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ remainderKernel r t ∧ remainderKernel r t ≤ t^(2*r+5) := by
  have hc : Continuous (fun v : ℝ => v^2*(1-v^2)*expRemainder r ((1+v^2)*t^2/4)) := by
    exact (by fun_prop : Continuous (fun v : ℝ => v^2*(1-v^2))).mul
      ((expRemainderContinuous r).comp (by fun_prop))
  have hbound (v : ℝ) (hv : v ∈ Icc (0:ℝ) 1) :
      0 ≤ v^2*(1-v^2)*expRemainder r ((1+v^2)*t^2/4) ∧
      v^2*(1-v^2)*expRemainder r ((1+v^2)*t^2/4) ≤ t^(2*r) := by
    have hv2 : v^2 ≤ 1 := by nlinarith [hv.1, hv.2]
    have hw : 0 ≤ v^2*(1-v^2) := mul_nonneg (sq_nonneg _) (by linarith)
    have hw1 : v^2*(1-v^2) ≤ 1 := by nlinarith [sq_nonneg (v^2)]
    have ha : 0 ≤ (1+v^2)*t^2/4 := by positivity
    have ha' : (1+v^2)*t^2/4 ≤ t^2 := by nlinarith [sq_nonneg t]
    have he := expRemainderBounds r ha
    constructor
    · exact mul_nonneg hw he.1
    · calc
        _ ≤ expRemainder r ((1+v^2)*t^2/4) := mul_le_of_le_one_left he.1 hw1
        _ ≤ ((1+v^2)*t^2/4)^r / r.factorial := he.2
        _ ≤ (t^2)^r := (div_le_self (by positivity) (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos r))).trans
          (pow_le_pow_left₀ ha ha' r)
        _ = _ := by rw [← pow_mul]
  have hnon := intervalIntegral.integral_nonneg (μ := volume) (by norm_num : (0:ℝ) ≤ 1) (fun v hv => (hbound v hv).1)
  have hle := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
    (hc.intervalIntegrable _ _) (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => t^(2*r)) volume 0 1)
    (fun v hv => (hbound v hv).2)
  simp only [intervalIntegral.integral_const, sub_zero, one_smul] at hle
  unfold remainderKernel
  constructor
  · positivity
  · calc
      _ ≤ t^5/8*t^(2*r) := mul_le_mul_of_nonneg_left hle (by positivity)
      _ ≤ t^(2*r+5) := by rw [pow_add]; nlinarith [mul_nonneg (pow_nonneg ht 5) (pow_nonneg ht (2*r))]
private lemma remainderKernelMoments (r m : ℕ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => t^m*exp (-x*t)*remainderKernel r t) (Ioi 0) := by
  have he := (TwoScaleEndpointMoments.exponential_moment x hx (m+2*r+5)).1
  simp only [← neg_mul] at he
  apply he.mono'
    (((by fun_prop : Continuous (fun t : ℝ => t^m*exp (-x*t))).mul
      (remainderKernelContinuous r)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change ‖t^m*exp (-x*t)*remainderKernel r t‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ht.le _) (exp_nonneg _))
    (remainderKernelBounds r ht.le).1)]
  calc
    _ ≤ t^m*exp (-x*t)*t^(2*r+5) := mul_le_mul_of_nonneg_left
      (remainderKernelBounds r ht.le).2 (mul_nonneg (pow_nonneg ht.le _) (exp_nonneg _))
    _ = _ := by rw [show m+2*r+5 = m+(2*r+5) by omega, pow_add]; ring
private lemma remainderKernelRec (r : ℕ) (t : ℝ) :
    remainderKernel (r+1) t =
      t^(2*r+5)/(8*4^r*r.factorial) *
        (∫ v in (0:ℝ)..1, v^2*(1-v^2)*(1+v^2)^r) - remainderKernel r t := by
  unfold remainderKernel
  simp_rw [expRemainderRec]
  have hid (v : ℝ) : v^2*(1-v^2)*(((1+v^2)*t^2/4)^r/r.factorial - expRemainder r ((1+v^2)*t^2/4)) =
      (t^(2*r)/(4^r*r.factorial))*(v^2*(1-v^2)*(1+v^2)^r) -
        v^2*(1-v^2)*expRemainder r ((1+v^2)*t^2/4) := by
    rw [div_pow, mul_pow, ← pow_mul]
    ring
  simp_rw [hid]
  have hc : Continuous (fun v : ℝ => v^2*(1-v^2)*expRemainder r ((1+v^2)*t^2/4)) := by
    exact (by fun_prop : Continuous (fun v : ℝ => v^2*(1-v^2))).mul
      ((expRemainderContinuous r).comp (by fun_prop))
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (hc.intervalIntegrable _ _), intervalIntegral.integral_const_mul]
  rw [pow_add]
  ring

private lemma remainderLaplaceRec (r : ℕ) {x : ℝ} (hx : 0 < x) :
    moment (remainderKernel (r+1)) 0 x =
      ((2*r+5).factorial:ℝ)/(8*4^r*r.factorial)*intWeight r/x^(2*r+6) -
        moment (remainderKernel r) 0 x := by
  have hk : IntegrableOn (fun t : ℝ => exp (-x*t)*remainderKernel r t) (Ioi 0) := by
    simpa only [pow_zero, one_mul] using remainderKernelMoments r 0 hx
  have hm := TwoScaleEndpointMoments.exponential_moment x hx (2*r+5)
  simp only [← neg_mul] at hm
  calc
    _ = ∫ t in Ioi (0:ℝ), (t^(2*r+5)*exp (-x*t))*(intWeight r/(8*4^r*r.factorial)) -
        exp (-x*t)*remainderKernel r t := by
      apply integral_congr_ae
      filter_upwards with t
      rw [remainderKernelRec]
      simp only [pow_zero, one_mul, intWeight]
      ring
    _ = (∫ t in Ioi (0:ℝ), t^(2*r+5)*exp (-x*t)) *
        (intWeight r/(8*4^r*r.factorial)) - moment (remainderKernel r) 0 x := by
      rw [integral_sub (hm.1.mul_const _) hk, integral_mul_const]
      simp only [moment, pow_zero, one_mul]
    _ = _ := by
      rw [hm.2]
      simp only [show 2*r+5+1 = 2*r+6 by omega]
      ring
private lemma remainderRepresentation (r : ℕ) {x : ℝ} (hx : 0 < x) :
    (-1:ℝ)^r * D (r+2) x (-1) = moment (remainderKernel r) 0 x := by
  induction r with
  | zero =>
    have hr : millsRatio x = ∫ t in Ioi (0:ℝ), exp (-x*t)*exp (-t^2/2) := by
      rw [millsLaplace]
      apply integral_congr_ae
      filter_upwards with t
      rw [← exp_add]
      congr 1
      ring
    have hr2 : millsRatio x^2 = ∫ t in Ioi (0:ℝ), exp (-x*t)*q0 t := by
      rw [millsSquareConvolution hx.le]
      apply integral_congr_ae
      filter_upwards with t
      rw [convolutionClosed]
      simp only [q0, J, one_mul]
    simpa only [Nat.zero_add, D_two, moment, remainderKernel, expRemainder_eq, K, J, pow_zero,
      Finset.range_zero, Finset.sum_empty, sub_zero, one_mul, neg_mul, neg_div]
      using kernelLaplace hx (millsRatio x) hr hr2
  | succ r ih =>
    rw [show r+1+2 = r+3 by omega, D_rec, u_kernel_factorial, remainderLaplaceRec r hx, ← ih]
    have hs : (-1:ℝ)^r * (-1:ℝ)^r = 1 := by rw [← mul_pow]; norm_num
    simp only [pow_succ, show 2*(r+3) = 2*r+6 by omega]
    linear_combination (((2*r+5).factorial:ℝ)/(8*4^r*r.factorial)*intWeight r/x^(2*r+6)) * hs

theorem result : claim := by
  intro n hn
  obtain ⟨r, hr⟩ : ∃ r, n = r+2 := ⟨n-2, by omega⟩
  subst n
  have hc := laplaceCM (remainderKernelContinuous r)
    (fun t ht => (remainderKernelBounds r ht.le).1)
    (fun m x hx => remainderKernelMoments r m hx)
  have he : EqOn (fun x => (-1:ℝ)^(r+2)*D (r+2) x (-1)) (moment (remainderKernel r) 0) (Ioi 0) := by
    intro x hx
    simpa [pow_add] using remainderRepresentation r hx
  refine ⟨hc.1.congr (fun x hx => he hx), ?_⟩
  intro m x hx
  rw [he.iteratedDeriv_of_isOpen isOpen_Ioi m hx]
  exact hc.2 m x hx

end D5.S3.Analytic.XuYangMillsRemainder.Result
