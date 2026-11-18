/- GID: D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite positive source modes and the complete square-resolvent candidate. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalSourceJet
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
Finite-mode construction; its original/candidate identification is not claimed.
Project APIs were read at 2fd4380ac552c5cc9d30968cdebb0e5ece3a3496;
Mathlib APIs were read at 56a005855ea17e0b0958f73ec801ae140b0a1679.

Concrete finite positive source modes and the ++ square-resolvent candidate.
Every parameter derivative of a mode below is a derivative of a finite sum.
The period is the actual original period. No original/candidate identification,
mode recurrence, or differentiation of a parameter-dependent tsum is assumed.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Topology

namespace D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes

open OriginalGaussianMatrix OriginalGaussianAllIndexResolvent
open OriginalGaussianSourceEvaluation
open D5.S3.Analytic.OriginalHalfBinomialPeriod

/-- The literal finite positive source polynomial. -/
def a (p : ℕ) (r : ℂ) : ℂ :=
  ∑ n ∈ Finset.range (p + 1),
    (centralWeight n : ℂ) * (-1 : ℂ) ^ n * (p.choose n : ℂ) * r ^ n

/-- Exact support reduction of the ACTUAL source, for every complex parameter. -/
theorem sourceAmplitude_true_finite (p : ℕ) (r : ℂ) :
    sourceAmplitude true p r = a p r := by
  have harg : ((p : ℂ) + 1 / 2) - 1 / 2 = (p : ℂ) := by ring
  simp only [sourceAmplitude, ite_true, harg, Ring.choose_natCast]
  unfold a
  apply tsum_eq_sum
  intro n hn
  have hpn : p < n := by
    have h := (Finset.mem_range.not.mp hn)
    omega
  simp [Nat.choose_eq_zero_of_lt hpn]

/-- The formal derivative is finite, including its harmless zero-index term. -/
def aPrime (p : ℕ) (r : ℂ) : ℂ :=
  ∑ n ∈ Finset.range (p + 1),
    ((centralWeight n : ℂ) * (-1 : ℂ) ^ n * (p.choose n : ℂ)) *
      ((n : ℂ) * r ^ (n - 1))

theorem hasDerivAt_a (p : ℕ) (r : ℂ) : HasDerivAt (a p) (aPrime p r) r := by
  unfold a aPrime
  exact HasDerivAt.fun_sum fun n _ =>
    (hasDerivAt_pow n r).const_mul
      ((centralWeight n : ℂ) * (-1 : ℂ) ^ n * (p.choose n : ℂ))

theorem deriv_a (p : ℕ) (r : ℂ) : deriv (a p) r = aPrime p r :=
  (hasDerivAt_a p r).deriv

theorem hasDerivAt_a_real (p : ℕ) (r : ℝ) :
    HasDerivAt (fun u : ℝ => a p (u : ℂ)) (aPrime p r) r :=
  (hasDerivAt_a p (r : ℂ)).comp_ofReal

theorem hasDerivAt_sourceAmplitude_true (p : ℕ) (r : ℂ) :
    HasDerivAt (sourceAmplitude true p) (aPrime p r) r := by
  rw [show sourceAmplitude true p = a p from funext (sourceAmplitude_true_finite p)]
  exact hasDerivAt_a p r

theorem deriv_sourceAmplitude_true_real (p : ℕ) (r : ℝ) :
    deriv (fun u : ℝ => sourceAmplitude true p (u : ℂ)) r = aPrime p r := by
  simpa only [sourceAmplitude_true_finite] using (hasDerivAt_a_real p r).deriv


/-- An exact finite source-mode recurrence.  The factor is the polynomial
mode p+1, not the signed half-frequency from the original external column. -/
theorem a_euler_mode_step (p : ℕ) (r : ℂ) :
    r * aPrime (p + 1) r = (p + 1 : ℂ) * (a (p + 1) r - a p r) := by
  have hpad : a p r = ∑ n ∈ Finset.range (p + 2),
      (centralWeight n : ℂ) * (-1 : ℂ) ^ n * (p.choose n : ℂ) * r ^ n := by
    rw [show p + 2 = (p + 1) + 1 by omega, Finset.sum_range_succ]
    simp [a]
  rw [hpad]
  unfold a aPrime
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  cases n with
  | zero => simp
  | succ n =>
    have hc : (n + 1 : ℂ) * ((p + 1).choose (n + 1) : ℂ) =
        (p + 1 : ℂ) * (((p + 1).choose (n + 1) : ℂ) - (p.choose (n + 1) : ℂ)) := by
      have hh : (p + 1 : ℂ) * (p.choose n : ℂ) =
          ((p + 1).choose (n + 1) : ℂ) * (n + 1 : ℂ) := by
        exact_mod_cast Nat.add_one_mul_choose_eq p n
      simp only [Nat.choose_succ_succ, Nat.cast_add] at hh ⊢
      linear_combination -hh
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    linear_combination (centralWeight (n + 1) : ℂ) * (-1 : ℂ) ^ (n + 1) *
      r ^ (n + 1) * hc

private lemma aPrime_shifted (p : ℕ) (r : ℂ) :
    aPrime p r = ∑ n ∈ Finset.range (p + 1),
      (centralWeight (n + 1) : ℂ) * (-1 : ℂ) ^ (n + 1) *
        (p.choose (n + 1) : ℂ) * (n + 1 : ℂ) * r ^ n := by
  unfold aPrime
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.choose_succ_self,
    Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- The second exact source recurrence, obtained from the actual central-binomial
ratio. It is polynomial and is valid even at r=0. -/
theorem a_derivative_mode_step (p : ℕ) (r : ℂ) :
    2 * (aPrime (p + 1) r - (1 - r) * aPrime p r) = -a p r := by
  have hdiff : aPrime (p + 1) r - aPrime p r =
      ∑ n ∈ Finset.range (p + 1),
        (centralWeight (n + 1) : ℂ) * (-1 : ℂ) ^ (n + 1) *
          (p.choose n : ℂ) * (n + 1 : ℂ) * r ^ n := by
    rw [aPrime_shifted (p + 1), Finset.sum_range_succ, aPrime_shifted p]
    simp only [Nat.choose_succ_self, Nat.cast_zero, mul_zero, zero_mul, add_zero]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [Nat.choose_succ_succ, Nat.cast_add]
    ring
  have heuler : r * aPrime p r = ∑ n ∈ Finset.range (p + 1),
      (centralWeight n : ℂ) * (-1 : ℂ) ^ n * (p.choose n : ℂ) *
        (n : ℂ) * r ^ n := by
    unfold aPrime
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    cases n with
    | zero => simp
    | succ n => simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]; ring
  have hzero : 2 * (aPrime (p + 1) r - aPrime p r) +
      2 * (r * aPrime p r) + a p r = 0 := by
    rw [hdiff, heuler]
    unfold a
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro n hn
    have hc : 2 * (n + 1 : ℂ) * (centralWeight (n + 1) : ℂ) =
        (2 * n + 1 : ℂ) * (centralWeight n : ℂ) := by
      exact_mod_cast centralWeight_step n
    simp only [pow_succ]
    linear_combination -(p.choose n : ℂ) * (-1 : ℂ) ^ n * r ^ n * hc
  linear_combination hzero

theorem analyticAt_a (p : ℕ) (r : ℂ) : AnalyticAt ℂ (a p) r := by
  unfold a
  apply Finset.analyticAt_fun_sum
  intro n hn
  fun_prop

theorem analyticAt_aPrime (p : ℕ) (r : ℂ) : AnalyticAt ℂ (aPrime p) r := by
  unfold aPrime
  apply Finset.analyticAt_fun_sum
  intro n hn
  fun_prop

/-- Coefficients of the positive-sector inverse denominator. -/
def h (p q : ℕ) (r : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (min p q + 1),
    (p.choose j : ℂ) * (q.choose j : ℂ) * r ^ j

/-- Coefficients of its square, given by an actual finite polynomial. -/
def h2 (p q : ℕ) (r : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (min p q + 1),
    (j + 1 : ℂ) * ((p + 1).choose (j + 1) : ℂ) *
      ((q + 1).choose (j + 1) : ℂ) * r ^ j

def hPrime (p q : ℕ) (r : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (min p q + 1),
    ((p.choose j : ℂ) * (q.choose j : ℂ)) * ((j : ℂ) * r ^ (j - 1))

def h2Prime (p q : ℕ) (r : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (min p q + 1),
    ((j + 1 : ℂ) * ((p + 1).choose (j + 1) : ℂ) *
      ((q + 1).choose (j + 1) : ℂ)) * ((j : ℂ) * r ^ (j - 1))

theorem hasDerivAt_h (p q : ℕ) (r : ℂ) : HasDerivAt (h p q) (hPrime p q r) r := by
  unfold h hPrime
  exact HasDerivAt.fun_sum fun j _ =>
    (hasDerivAt_pow j r).const_mul ((p.choose j : ℂ) * (q.choose j : ℂ))

theorem hasDerivAt_h2 (p q : ℕ) (r : ℂ) : HasDerivAt (h2 p q) (h2Prime p q r) r := by
  unfold h2 h2Prime
  exact HasDerivAt.fun_sum fun j _ =>
    (hasDerivAt_pow j r).const_mul
      ((j + 1 : ℂ) * ((p + 1).choose (j + 1) : ℂ) *
        ((q + 1).choose (j + 1) : ℂ))

theorem analyticAt_h (p q : ℕ) (r : ℂ) : AnalyticAt ℂ (h p q) r := by
  unfold h
  apply Finset.analyticAt_fun_sum
  intro j hj
  fun_prop

theorem analyticAt_h2 (p q : ℕ) (r : ℂ) : AnalyticAt ℂ (h2 p q) r := by
  unfold h2
  apply Finset.analyticAt_fun_sum
  intro j hj
  fun_prop

private lemma h_sum_pad (p q N : ℕ) (r : ℂ) (hN : min p q < N) :
    h p q r = ∑ j ∈ Finset.range N,
      (p.choose j : ℂ) * (q.choose j : ℂ) * r ^ j := by
  unfold h
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro j hj hj'
  have hjm : min p q < j := by
    have := Finset.mem_range.not.mp hj'
    omega
  have hcases : p < j ∨ q < j := by omega
  rcases hcases with hp | hq
  · simp [Nat.choose_eq_zero_of_lt hp]
  · simp [Nat.choose_eq_zero_of_lt hq]

private lemma hPrime_sum_pad (p q N : ℕ) (r : ℂ) (hN : min p q < N) :
    hPrime p q r = ∑ j ∈ Finset.range N,
      ((p.choose j : ℂ) * (q.choose j : ℂ)) * ((j : ℂ) * r ^ (j - 1)) := by
  unfold hPrime
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro j hj hj'
  have hjm : min p q < j := by
    have := Finset.mem_range.not.mp hj'
    omega
  have hcases : p < j ∨ q < j := by omega
  rcases hcases with hp | hq
  · simp [Nat.choose_eq_zero_of_lt hp]
  · simp [Nat.choose_eq_zero_of_lt hq]

private lemma h_zero_left (q : ℕ) (r : ℂ) : h 0 q r = 1 := by
  simp [h]

private lemma h_zero_right (p : ℕ) (r : ℂ) : h p 0 r = 1 := by
  simp [h]

/-- The two Pascal differences of the literal denominator coefficients.
The axes are handled separately by the guarded version below. -/
theorem h_pascal (p q : ℕ) (r : ℂ) :
    h (p + 1) (q + 1) r - h p (q + 1) r - h (p + 1) q r + h p q r =
      r * h p q r := by
  let N := p + q + 2
  conv_rhs => rw [h_sum_pad p q N r (by dsimp [N]; omega)]
  rw [h_sum_pad (p + 1) (q + 1) (N + 1) r (by dsimp [N]; omega),
    h_sum_pad p (q + 1) (N + 1) r (by dsimp [N]; omega),
    h_sum_pad (p + 1) q (N + 1) r (by dsimp [N]; omega),
    h_sum_pad p q (N + 1) r (by dsimp [N]; omega)]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, sub_self,
    zero_sub, neg_add_cancel, add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Nat.choose_succ_succ, Nat.cast_add, pow_succ]
  ring

/-- The finite Euler identity, with no division by the parameter. -/
theorem h_euler_mode_step (p q : ℕ) (r : ℂ) :
    r * hPrime (p + 1) q r = (p + 1 : ℂ) * (h (p + 1) q r - h p q r) := by
  rw [hPrime_sum_pad (p + 1) q (p + 2) r (by omega),
    h_sum_pad (p + 1) q (p + 2) r (by omega),
    h_sum_pad p q (p + 2) r (by omega)]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  cases j with
  | zero => simp
  | succ j =>
    have hc : (j + 1 : ℂ) * ((p + 1).choose (j + 1) : ℂ) =
        (p + 1 : ℂ) * (((p + 1).choose (j + 1) : ℂ) - (p.choose (j + 1) : ℂ)) := by
      have hh : (p + 1 : ℂ) * (p.choose j : ℂ) =
          ((p + 1).choose (j + 1) : ℂ) * (j + 1 : ℂ) := by
        exact_mod_cast Nat.add_one_mul_choose_eq p j
      simp only [Nat.choose_succ_succ, Nat.cast_add] at hh ⊢
      linear_combination -hh
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    linear_combination (q.choose (j + 1) : ℂ) * r ^ (j + 1) * hc

/-- Differentiating the actual finite coefficient sum shifts both indices.
The zero row and column of the derivative are not omitted. -/
theorem hPrime_succ_succ (p q : ℕ) (r : ℂ) :
    hPrime (p + 1) (q + 1) r = h2 p q r := by
  unfold hPrime h2
  rw [show min (p + 1) (q + 1) + 1 = (min p q + 1) + 1 by omega,
    Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.add_sub_cancel,
    Nat.cast_add, Nat.cast_one]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Finite source convolution with one of the two denominator tables. -/
def L (H : ℕ → ℕ → ℂ → ℂ) (p q : ℕ) (r : ℂ) : ℂ :=
  ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 1),
    a i r * a j r * H (p - i) (q - j) r

def LPrime (H HPrime : ℕ → ℕ → ℂ → ℂ) (p q : ℕ) (r : ℂ) : ℂ :=
  ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 1),
    ((aPrime i r * a j r + a i r * aPrime j r) * H (p - i) (q - j) r +
      (a i r * a j r) * HPrime (p - i) (q - j) r)

def L_h := L h
def L_h2 := L h2
def L_hPrime := LPrime h hPrime
def L_h2Prime := LPrime h2 h2Prime

/-- This is only the finite product rule; its hypotheses are scalar derivatives. -/
theorem hasDerivAt_L (H HPrime : ℕ → ℕ → ℂ → ℂ) (p q : ℕ) (r : ℂ)
    (hH : ∀ i j, HasDerivAt (H i j) (HPrime i j r) r) :
    HasDerivAt (L H p q) (LPrime H HPrime p q r) r := by
  unfold L LPrime
  apply HasDerivAt.fun_sum
  intro i hi
  apply HasDerivAt.fun_sum
  intro j hj
  exact ((hasDerivAt_a i r).mul (hasDerivAt_a j r)).mul (hH (p - i) (q - j))

theorem hasDerivAt_L_h (p q : ℕ) (r : ℂ) :
    HasDerivAt (L_h p q) (L_hPrime p q r) r :=
  hasDerivAt_L h hPrime p q r (fun i j => hasDerivAt_h i j r)

theorem hasDerivAt_L_h2 (p q : ℕ) (r : ℂ) :
    HasDerivAt (L_h2 p q) (L_h2Prime p q r) r :=
  hasDerivAt_L h2 h2Prime p q r (fun i j => hasDerivAt_h2 i j r)

theorem analyticAt_L (H : ℕ → ℕ → ℂ → ℂ) (p q : ℕ) (r : ℂ)
    (hH : ∀ i j, AnalyticAt ℂ (H i j) r) : AnalyticAt ℂ (L H p q) r := by
  unfold L
  apply Finset.analyticAt_fun_sum
  intro i hi
  apply Finset.analyticAt_fun_sum
  intro j hj
  exact ((analyticAt_a i r).mul (analyticAt_a j r)).mul (hH (p - i) (q - j))

theorem analyticAt_L_h (p q : ℕ) (r : ℂ) : AnalyticAt ℂ (L_h p q) r :=
  analyticAt_L h p q r (fun i j => analyticAt_h i j r)

theorem analyticAt_L_h2 (p q : ℕ) (r : ℂ) : AnalyticAt ℂ (L_h2 p q) r :=
  analyticAt_L h2 p q r (fun i j => analyticAt_h2 i j r)

/-- A Taylor shift, with BOTH zero indices guarded before Nat subtraction.
It is unrelated to the signed source predecessor, whose false-zero row is real data. -/
def shift11 (F : ℕ → ℕ → ℂ → ℂ) (p q : ℕ) (r : ℂ) : ℂ :=
  if p = 0 ∨ q = 0 then 0 else F (p - 1) (q - 1) r

@[simp] theorem shift11_zero_left (F : ℕ → ℕ → ℂ → ℂ) (q : ℕ) (r : ℂ) :
    shift11 F 0 q r = 0 := by simp [shift11]

@[simp] theorem shift11_zero_right (F : ℕ → ℕ → ℂ → ℂ) (p : ℕ) (r : ℂ) :
    shift11 F p 0 r = 0 := by simp [shift11]

@[simp] theorem shift11_succ_succ (F : ℕ → ℕ → ℂ → ℂ) (p q : ℕ) (r : ℂ) :
    shift11 F (p + 1) (q + 1) r = F p q r := by simp [shift11]

/-- One backward Taylor shift, guarded before natural subtraction.
This is not the signed-frequency predecessor of the original external mode. -/
def shiftX (F : ℕ → ℕ → ℂ → ℂ) (p q : ℕ) (r : ℂ) : ℂ :=
  if p = 0 then 0 else F (p - 1) q r

def shiftY (F : ℕ → ℕ → ℂ → ℂ) (p q : ℕ) (r : ℂ) : ℂ :=
  if q = 0 then 0 else F p (q - 1) r

/-- Multiplication by the literal inverse-denominator stencil. -/
def denominatorStencil (F : ℕ → ℕ → ℂ → ℂ) (p q : ℕ) (r : ℂ) : ℂ :=
  F p q r - shiftX F p q r - shiftY F p q r + (1 - r) * shift11 F p q r

/-- The finite h table is the inverse of 1-X-Y+(1-r)XY, including both axes. -/
theorem h_inverse_stencil (p q : ℕ) (r : ℂ) :
    denominatorStencil h p q r = if p = 0 ∧ q = 0 then 1 else 0 := by
  cases p with
  | zero =>
    cases q with
    | zero => simp [denominatorStencil, shiftX, shiftY, h_zero_left]
    | succ q => simp [denominatorStencil, shiftX, shiftY, h_zero_left]
  | succ p =>
    cases q with
    | zero => simp [denominatorStencil, shiftX, shiftY, h_zero_right]
    | succ q =>
      simp only [denominatorStencil, shiftX, shiftY, Nat.succ_ne_zero, ite_false,
        Nat.add_sub_cancel, shift11_succ_succ, false_and]
      linear_combination h_pascal p q r

/-- The finite derivative is the guarded XY shift of the actual h2 table. -/
theorem hPrime_eq_shift11 (p q : ℕ) (r : ℂ) :
    hPrime p q r = shift11 h2 p q r := by
  cases p with
  | zero => simp [hPrime]
  | succ p =>
    cases q with
    | zero => simp [hPrime]
    | succ q => simpa only [shift11_succ_succ] using hPrime_succ_succ p q r

/-- The literal finite square-denominator coefficients satisfy E h2=h.
Differentiation is only of finite polynomials. -/
theorem h2_inverse_stencil (p q : ℕ) (r : ℂ) :
    denominatorStencil h2 p q r = h p q r := by
  cases p with
  | zero =>
    cases q with
    | zero => simp [denominatorStencil, shiftX, shiftY, h2, h]
    | succ q =>
      simp [denominatorStencil, shiftX, shiftY, h2, h]
  | succ p =>
    cases q with
    | zero =>
      simp [denominatorStencil, shiftX, shiftY, h2, h]
    | succ q =>
      have hd := (((hasDerivAt_h (p + 2) (q + 2) r).sub
        (hasDerivAt_h (p + 1) (q + 2) r)).sub
        (hasDerivAt_h (p + 2) (q + 1) r)).add
        (hasDerivAt_h (p + 1) (q + 1) r)
      have heq : (fun u : ℂ => h (p + 2) (q + 2) u - h (p + 1) (q + 2) u -
          h (p + 2) (q + 1) u + h (p + 1) (q + 1) u) =
          (fun u : ℂ => u * h (p + 1) (q + 1) u) :=
        funext (h_pascal (p + 1) (q + 1))
      change HasDerivAt (fun u : ℂ => h (p + 2) (q + 2) u - h (p + 1) (q + 2) u -
        h (p + 2) (q + 1) u + h (p + 1) (q + 1) u) _ r at hd
      rw [heq] at hd
      have hh := hd.unique ((hasDerivAt_id r).mul
        (hasDerivAt_h (p + 1) (q + 1) r))
      simp only [show p + 2 = (p + 1) + 1 by omega,
        show q + 2 = (q + 1) + 1 by omega, hPrime_succ_succ, id_eq] at hh
      simp only [denominatorStencil, shiftX, shiftY, Nat.succ_ne_zero, ite_false,
        Nat.add_sub_cancel, shift11_succ_succ]
      linear_combination hh

private lemma L_shiftX (H : ℕ → ℕ → ℂ → ℂ) (p q : ℕ) (r : ℂ) :
    L (shiftX H) p q r = shiftX (L H) p q r := by
  cases p with
  | zero => simp [L, shiftX]
  | succ p =>
    simp only [shiftX, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
    unfold L
    rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, shiftX, ite_true, mul_zero, Finset.sum_const_zero, add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    have hi' := Finset.mem_range.mp hi
    simp only [ite_eq_right (show p + 1 - i ≠ 0 by omega)]
    rw [show p + 1 - i - 1 = p - i by omega]

private lemma L_shiftY (H : ℕ → ℕ → ℂ → ℂ) (p q : ℕ) (r : ℂ) :
    L (shiftY H) p q r = shiftY (L H) p q r := by
  cases q with
  | zero => simp [L, shiftY]
  | succ q =>
    simp only [shiftY, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
    unfold L
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, shiftY, ite_true, mul_zero, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    simp only [ite_eq_right (show q + 1 - j ≠ 0 by omega)]
    rw [show q + 1 - j - 1 = q - j by omega]

private lemma shiftX_shiftY (H : ℕ → ℕ → ℂ → ℂ) : shiftX (shiftY H) = shift11 H := by
  funext p q r
  cases p <;> cases q <;> simp [shiftX, shiftY, shift11]

private lemma L_shift11 (H : ℕ → ℕ → ℂ → ℂ) (p q : ℕ) (r : ℂ) :
    L (shift11 H) p q r = shift11 (L H) p q r := by
  rw [← shiftX_shiftY, L_shiftX]
  cases p with
  | zero => simp [shiftX]
  | succ p =>
    simp only [shiftX, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
    rw [L_shiftY]
    cases q <;> simp [shiftY, shift11]

/-- The actual finite convolution with the second source differentiated by Euler.
No parameter derivative of an infinite external-mode sum occurs here. -/
def sourceDerivativeConvolution (H : ℕ → ℕ → ℂ → ℂ) (p q : ℕ) (r : ℂ) : ℂ :=
  ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 1),
    a i r * (r * aPrime j r) * H (p - i) (q - j) r

/-- The source derivative recurrence survives the actual finite rectangular
convolution, including the q=0 boundary. This is the H_y cancellation needed
by the asymmetric polynomial stencil. -/
theorem sourceDerivativeConvolution_step (H : ℕ → ℕ → ℂ → ℂ)
    (p q : ℕ) (r : ℂ) :
    2 * (sourceDerivativeConvolution H p q r -
      (1 - r) * shiftY (sourceDerivativeConvolution H) p q r) =
      -r * shiftY (L H) p q r := by
  cases q with
  | zero => simp [sourceDerivativeConvolution, aPrime, shiftY]
  | succ q =>
    simp only [shiftY, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
    unfold sourceDerivativeConvolution L
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_range_succ']
    have hz : aPrime 0 r = 0 := by simp [aPrime]
    simp only [hz, mul_zero, zero_mul, add_zero]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [show q + 1 - (j + 1) = q - j by omega]
    linear_combination a i r * r * H (p - i) (q - j) r *
      a_derivative_mode_step j r

private lemma L_denominatorStencil (H : ℕ → ℕ → ℂ → ℂ) (p q : ℕ) (r : ℂ) :
    denominatorStencil (L H) p q r = L (denominatorStencil H) p q r := by
  unfold denominatorStencil
  rw [← L_shiftX, ← L_shiftY, ← L_shift11]
  unfold L
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The actual finite source convolution obeys E G=A at every index. -/
theorem L_h_inverse_stencil (p q : ℕ) (r : ℂ) :
    denominatorStencil L_h p q r = a p r * a q r := by
  rw [L_h, L_denominatorStencil]
  unfold L
  simp only [h_inverse_stencil]
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single q]
    · simp
    · intro j hj hjq
      have hj' := Finset.mem_range.mp hj
      simp [show q - j ≠ 0 by omega]
    · simp
  · intro i hi hip
    have hi' := Finset.mem_range.mp hi
    apply Finset.sum_eq_zero
    intro j hj
    simp [show p - i ≠ 0 by omega]
  · simp

/-- The square-denominator finite convolution obeys E J=G on both axes too. -/
theorem L_h2_inverse_stencil (p q : ℕ) (r : ℂ) :
    denominatorStencil L_h2 p q r = L_h p q r := by
  rw [L_h2, L_denominatorStencil]
  have heq : denominatorStencil h2 = h := funext fun p => funext fun q =>
    funext fun r => h2_inverse_stencil p q r
  rw [heq]
  rfl

/-- The square-denominator Euler recurrence is derived from the finite h
recurrence. It uses no formal interchange with an infinite mode sum. -/
theorem h2_euler_mode_step (p q : ℕ) (r : ℂ) :
    r * h2Prime (p + 1) q r =
      (p + 1 : ℂ) * h2 (p + 1) q r - (p + 2 : ℂ) * h2 p q r := by
  have heq : (fun u : ℂ => u * h2 (p + 1) q u) =
      (fun u : ℂ => (p + 2 : ℂ) * (h (p + 2) (q + 1) u - h (p + 1) (q + 1) u)) := by
    funext u
    have hh := h_euler_mode_step (p + 1) (q + 1) u
    rw [hPrime_eq_shift11] at hh
    simp only [show p + 2 = (p + 1) + 1 by omega, shift11_succ_succ] at hh
    convert hh using 1 <;> push_cast <;> ring
  have hd := (hasDerivAt_id r).mul (hasDerivAt_h2 (p + 1) q r)
  change HasDerivAt (fun u : ℂ => u * h2 (p + 1) q u) _ r at hd
  rw [heq] at hd
  have hh := hd.unique (((hasDerivAt_h (p + 2) (q + 1) r).sub
    (hasDerivAt_h (p + 1) (q + 1) r)).const_mul (p + 2 : ℂ))
  simp only [show p + 2 = (p + 1) + 1 by omega, hPrime_succ_succ, id_eq] at hh
  push_cast at hh ⊢
  linear_combination hh

lemma denominatorStencil_linear (F G : ℕ → ℕ → ℂ → ℂ) (b c : ℂ → ℂ)
    (p q : ℕ) (r : ℂ) :
    denominatorStencil (fun i j u => b u * F i j u + c u * G i j u) p q r =
      b r * denominatorStencil F p q r + c r * denominatorStencil G p q r := by
  cases p <;> cases q <;> simp [denominatorStencil, shiftX, shiftY, shift11] <;> ring

lemma denominatorStencil_shift11 (F : ℕ → ℕ → ℂ → ℂ) (p q : ℕ) (r : ℂ) :
    denominatorStencil (shift11 F) p q r = shift11 (denominatorStencil F) p q r := by
  cases p with
  | zero => simp [denominatorStencil, shiftX, shiftY, shift11]
  | succ p =>
    cases q with
    | zero => simp [denominatorStencil, shiftX, shiftY, shift11]
    | succ q =>
      cases p <;> cases q <;> simp [denominatorStencil, shiftX, shiftY, shift11]

theorem hasDerivAt_shift11 (F FPrime : ℕ → ℕ → ℂ → ℂ) (p q : ℕ) (r : ℂ)
    (hF : ∀ i j, HasDerivAt (F i j) (FPrime i j r) r) :
    HasDerivAt (shift11 F p q) (shift11 FPrime p q r) r := by
  unfold shift11
  by_cases hpq : p = 0 ∨ q = 0
  · simpa only [ite_eq_left hpq] using hasDerivAt_const r (0 : ℂ)
  · simpa only [ite_eq_right hpq] using hF (p - 1) (q - 1)

theorem analyticAt_shift11 (F : ℕ → ℕ → ℂ → ℂ) (p q : ℕ) (r : ℂ)
    (hF : ∀ i j, AnalyticAt ℂ (F i j) r) :
    AnalyticAt ℂ (shift11 F p q) r := by
  unfold shift11
  by_cases hpq : p = 0 ∨ q = 0
  · simpa only [ite_eq_left hpq] using
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) r)
  · simpa only [ite_eq_right hpq] using hF (p - 1) (q - 1)

/-- The complete finite polynomial part, retaining the direct square contribution. -/
def P (p q : ℕ) (r : ℂ) : ℂ :=
  r / 2 * (L_h p q r + (1 - r) * shift11 L_h p q r) +
    r ^ 2 * shift11 L_h2 p q r

def PPrime (p q : ℕ) (r : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (L_h p q r + (1 - r) * shift11 L_h p q r) +
    r / 2 * (L_hPrime p q r - shift11 L_h p q r +
      (1 - r) * shift11 L_hPrime p q r) +
    2 * r * shift11 L_h2 p q r + r ^ 2 * shift11 L_h2Prime p q r

/-- The complete polynomial candidate satisfies its finite denominator equation.
The direct inverse-square term contributes r squared times XY G. -/
theorem P_inverse_stencil (p q : ℕ) (r : ℂ) :
    denominatorStencil P p q r =
      r / 2 * (a p r * a q r + (1 - r) *
        shift11 (fun i j u => a i u * a j u) p q r) + r ^ 2 * shift11 L_h p q r := by
  unfold P
  rw [denominatorStencil_linear]
  have hlin := denominatorStencil_linear L_h (shift11 L_h) (fun _ => 1)
    (fun u => 1 - u) p q r
  simp only [one_mul] at hlin
  rw [hlin,
    L_h_inverse_stencil, denominatorStencil_shift11, denominatorStencil_shift11]
  have hg : denominatorStencil L_h = fun i j u => a i u * a j u :=
    funext fun i => funext fun j => funext fun u => L_h_inverse_stencil i j u
  have hj : denominatorStencil L_h2 = L_h :=
    funext fun i => funext fun j => funext fun u => L_h2_inverse_stencil i j u
  rw [hg, hj]

theorem hasDerivAt_P (p q : ℕ) (r : ℂ) : HasDerivAt (P p q) (PPrime p q r) r := by
  have hs := hasDerivAt_shift11 L_h L_hPrime p q r (fun i j => hasDerivAt_L_h i j r)
  have hs2 := hasDerivAt_shift11 L_h2 L_h2Prime p q r (fun i j => hasDerivAt_L_h2 i j r)
  have hd := (((hasDerivAt_id r).div_const 2).mul
    ((hasDerivAt_L_h p q r).add
      (((hasDerivAt_const r (1 : ℂ)).sub (hasDerivAt_id r)).mul hs))).add
    ((hasDerivAt_pow 2 r).mul hs2)
  convert! hd using 1
  dsimp [P, PPrime]
  ring

theorem analyticAt_P (p q : ℕ) (r : ℂ) : AnalyticAt ℂ (P p q) r := by
  have hL := analyticAt_L_h p q r
  have hS := analyticAt_shift11 L_h p q r (fun i j => analyticAt_L_h i j r)
  have hS2 := analyticAt_shift11 L_h2 p q r (fun i j => analyticAt_L_h2 i j r)
  unfold P
  fun_prop

/-- Logarithmic derivative of the actual period, not a new scalar solution. -/
def ell (r : ℂ) : ℂ := deriv period r / period r

def k (r : ℂ) : ℂ := r * (1 - r) * ell r

theorem hasDerivAt_period {r : ℂ} (hr : ‖r‖ < 1) :
    HasDerivAt period (shiftedCentralDerivative r 0) r := by
  simpa only [← period_eq_central] using central_hasDerivAt hr 0

theorem shiftedCentralDerivative_eq_deriv_period {r : ℂ} (hr : ‖r‖ < 1) :
    shiftedCentralDerivative r 0 = deriv period r :=
  (hasDerivAt_period hr).deriv.symm

theorem ell_eq_shifted {r : ℂ} (hr : ‖r‖ < 1) :
    ell r = shiftedCentralDerivative r 0 / period r := by
  rw [ell, shiftedCentralDerivative_eq_deriv_period hr]

theorem period_analyticOnNhd : AnalyticOnNhd ℂ period (Metric.ball 0 1) := by
  apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
  intro r hr
  exact (hasDerivAt_period (by simpa using hr)).differentiableAt.differentiableWithinAt

theorem analyticAt_ell {r : ℂ} (hr : ‖r‖ < 1) : AnalyticAt ℂ ell r := by
  have hF := period_analyticOnNhd r (by simpa using hr)
  exact hF.deriv.div hF (OriginalGaussianPeriodIdentity.period_ne_zero hr)

theorem analyticAt_k {r : ℂ} (hr : ‖r‖ < 1) : AnalyticAt ℂ k r := by
  exact (analyticAt_id.mul (analyticAt_const.sub analyticAt_id)).mul (analyticAt_ell hr)

/-- Quotient differentiation only; the second derivative is the actual one. -/
def ellPrime (r : ℂ) : ℂ :=
  (deriv (deriv period) r * period r - deriv period r * deriv period r) / period r ^ 2

theorem hasDerivAt_ell {r : ℂ} (hr : ‖r‖ < 1) : HasDerivAt ell (ellPrime r) r := by
  have hpf := picard_fuchs hr
  exact hpf.2.1.hasDerivAt.div hpf.1.hasDerivAt
    (OriginalGaussianPeriodIdentity.period_ne_zero hr)

/-- Picard--Fuchs in logarithmic form, with no division by r or 1-r. -/
theorem ell_picard_fuchs {r : ℂ} (hr : ‖r‖ < 1) :
    r * (1 - r) * (ellPrime r + ell r ^ 2) + (1 - 2 * r) * ell r - 1 / 4 = 0 := by
  have hF := OriginalGaussianPeriodIdentity.period_ne_zero hr
  have hpf := (picard_fuchs hr).2.2
  dsimp only [ellPrime, ell]
  field_simp [hF]
  linear_combination 4 * period r * hpf

/-- The exact derivative needed in the finite candidate radial equation. -/
theorem hasDerivAt_k {r : ℂ} (hr : ‖r‖ < 1) :
    HasDerivAt k (1 / 4 - r * (1 - r) * ell r ^ 2) r := by
  have hd := ((hasDerivAt_id r).mul
    ((hasDerivAt_const r (1 : ℂ)).sub (hasDerivAt_id r))).mul (hasDerivAt_ell hr)
  have he : ((1 * (1 - r) + r * (0 - 1)) * ell r +
      (r * (1 - r)) * ellPrime r) = 1 / 4 - r * (1 - r) * ell r ^ 2 := by
    linear_combination ell_picard_fuchs hr
  change HasDerivAt k _ r at hd
  exact hd.congr_deriv (by simpa using he)

def t (p q : ℕ) (r : ℂ) : ℂ := P p q r - k r * a p r * a q r

def tPrime (p q : ℕ) (r : ℂ) : ℂ :=
  PPrime p q r -
    (((1 / 4 - r * (1 - r) * ell r ^ 2) * a p r + k r * aPrime p r) * a q r +
      (k r * a p r) * aPrime q r)

def candidateT (p q : ℕ) (z : ℂ) : ℂ := t p q (z ^ 2)

theorem hasDerivAt_t (p q : ℕ) {r : ℂ} (hr : ‖r‖ < 1) :
    HasDerivAt (t p q) (tPrime p q r) r :=
  (hasDerivAt_P p q r).sub (((hasDerivAt_k hr).mul (hasDerivAt_a p r)).mul
    (hasDerivAt_a q r))

theorem hasDerivAt_t_real (p q : ℕ) {r : ℝ} (hr : ‖(r : ℂ)‖ < 1) :
    HasDerivAt (fun u : ℝ => t p q (u : ℂ)) (tPrime p q r) r :=
  (hasDerivAt_t p q hr).comp_ofReal

theorem analyticAt_t (p q : ℕ) {r : ℂ} (hr : ‖r‖ < 1) : AnalyticAt ℂ (t p q) r :=
  (analyticAt_P p q r).sub (((analyticAt_k hr).mul (analyticAt_a p r)).mul (analyticAt_a q r))

theorem candidateT_analyticOnNhd (p q : ℕ) :
    AnalyticOnNhd ℂ (candidateT p q) (Metric.ball 0 1) := by
  intro z hz
  have hz1 : ‖z‖ < 1 := by simpa using hz
  have hz2 : ‖z ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg z) hz1 (by norm_num)
  exact (analyticAt_t p q hz2).comp (f := fun w : ℂ => w ^ 2) (by fun_prop)

theorem hasDerivAt_candidateT (p q : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (candidateT p q) (tPrime p q (z ^ 2) * (2 * z)) z := by
  have hz2 : ‖z ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg z) hz (by norm_num)
  convert! (hasDerivAt_t p q hz2).comp z (hasDerivAt_pow 2 z) using 1
  norm_num

@[simp] theorem candidateT_even (p q : ℕ) (z : ℂ) :
    candidateT p q (-z) = candidateT p q z := by simp [candidateT]

/-- The genuine negative-zero T row against a positive mode, expressed using
finite source data and the actual period. It is not the Taylor shift11. -/
def negativeZeroT : ℕ → ℝ → ℂ
  | 0, r => -(Real.sqrt (1 - r) : ℂ) * (r : ℂ) * ell r
  | p + 1, r => (Real.sqrt (1 - r) : ℂ) *
      ((p + 1 : ℂ) * (a (p + 1) r - a p r) - (r : ℂ) * ell r * a (p + 1) r)

/-- Identification of the actual signed predecessor boundary with finite data.
The frequency contribution cancels only after adding the actual moment and jet;
it is never set to zero by an absent-mode convention. -/
theorem externalT_negative_zero_positive_finite (p : ℕ)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    OriginalGaussianExternalResolvent.externalT false 0 true p (Real.sqrt r : ℂ) =
      negativeZeroT p r := by
  have hx : ‖(r : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using hr1
  rw [(OriginalGaussianExternalEvolution.external_negative_zero_boundary true p hr hr1).2,
    OriginalGaussianExternalSourceJet.sourceJetMoment_eq_derivative true p hr hr1,
    OriginalGaussianExternalMoments.sourceMoment_eq_modeFrequency true p hx,
    deriv_sourceAmplitude_true_real, sourceAmplitude_true_finite]
  cases p with
  | zero =>
    dsimp only [negativeZeroT]
    rw [ell_eq_shifted hx]
    norm_num [a, aPrime, centralWeight]
    ring
  | succ p =>
    dsimp only [negativeZeroT]
    rw [ell_eq_shifted hx]
    have hs := a_euler_mode_step p (r : ℂ)
    linear_combination (Real.sqrt (1 - r) : ℂ) * hs

/- Remaining work is recorded only in comments outside theorem bodies:
finite inverse coefficient identification; candidate PDEs and their transport;
all signed source and J candidates; original/candidate germ and global equality.
The true negative-zero row is identified above from the literal original boundary.
-/

end D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes
