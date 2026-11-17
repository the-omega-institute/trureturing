/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteCandidateModes
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteCandidateModes
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

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFiniteCandidateModes

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
  convert! (hasDerivAt_t p q hz2).comp z (hasDerivAt_pow 2 z) using 1 <;>
    simp [candidateT, Function.comp_def]

@[simp] theorem candidateT_even (p q : ℕ) (z : ℂ) :
    candidateT p q (-z) = candidateT p q z := by simp [candidateT]

/- Remaining work is recorded only in comments outside theorem bodies:
finite inverse coefficient identification; candidate PDEs and their transport;
all signed source and J candidates; original/candidate germ and global equality.
The companion normalization file supplies real finite values and actual boundary data.
-/

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFiniteCandidateModes
