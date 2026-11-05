/- GID: D5/S3/Analytic/Fourier/ThetaRadialCurvature
   generality: I
   mirror-B: D5/B/S3/Analytic/Fourier/ThetaRadialCurvature
   mirror-E: none(waiver:universal-infinite-analytic-estimate)
   anchors: []
   utility: none
   digest: Strict radial curvature and square-variable logarithmic concavity for the complete theta kernel. -/
import D5.S3.Zeros.Jensen.OriginalPrimalTailProjection
import D5.S3.Analytic.Fourier.ThetaDifferentialKernel
import D5.S3.Zeros.Jensen.SourceThetaMomentBounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic
/-!
# Radial curvature and square-variable strict concavity of the theta kernel
For the literal complete theta kernel, a rational certificate for the first
two modes and a bound on every remaining mode give a strictly negative
fourth-logarithmic-derivative numerator. Evenness and the resulting
logarithmic jet chain imply the radial curvature inequality and strict
concavity of `r ↦ log (romikPhi (sqrt r))` on the positive ray.
The square-variable conclusion is the classical Csordas–Varga property;
this proof verifies the complete kernel through an explicit full-tail estimate.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Analytic.Fourier.ThetaRadialCurvature
open Real Set Polynomial
open D5.S3.Zeros.Jensen.OriginalPrimalTailProjection
open D5.S3.Analytic.Fourier.ThetaDifferentialKernel
open D5.S3.Zeros.Jensen.SourceThetaMomentBounds
open private primalJet_deriv tailJet_deriv tailJet_summable_ray from
  D5.S3.Zeros.Jensen.OriginalPrimalTailProjection
private def fullJet (r : ℕ) (x : ℝ) : ℝ :=
  primalJet r 1 x + tailJet r 1 x
private theorem fullJet_deriv (r : ℕ) (x : ℝ) :
    HasDerivAt (fullJet r) (fullJet (r + 1) x) x :=
  (primalJet_deriv r 1 x).add (tailJet_deriv r 1 (by omega) x)
private theorem fullJet_eq_iterated (r : ℕ) :
    fullJet r = iteratedDeriv r (fullJet 0) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [iteratedDeriv_succ, ← ih]
    exact funext (fun x => (fullJet_deriv r x).deriv.symm)
/-- The five actual primal derivative polynomials. -/
private def P : ℕ → ℝ → ℝ
  | 0, u => 4*u^2 - 6*u
  | 1, u => -8*u^3 + 30*u^2 - 15*u
  | 2, u => 16*u^4 - 112*u^3 + 165*u^2 - (75/2)*u
  | 3, u => -32*u^5 + 360*u^4 - 1058*u^3 + (1635/2)*u^2 - (375/4)*u
  | 4, u => 64*u^6 - 1056*u^5 + 5176*u^4 - 8512*u^3 +
      (15465/4)*u^2 - (1875/8)*u
  | _, _ => 0
private theorem P_eq_jetPolynomial (k : ℕ) (hk : k ≤ 4) (u : ℝ) :
    P k u = (jetPolynomial k).eval u := by
  interval_cases k <;>
    norm_num [P, jetPolynomial, derivative_sub, derivative_add,
      derivative_mul, derivative_pow] <;> ring
/-- The numerator of the fourth derivative of the logarithm. The five
    arguments are the zeroth through fourth derivatives in x. -/
private def fourthNumerator (a b c d e : ℝ) : ℝ :=
  a^3*e - 4*a^2*b*d - 3*a^2*c^2 + 12*a*b^2*c - 6*b^4
/-- Its coefficientwise absolute polynomial, used only for tail perturbations. -/
private def absoluteFourth (a b c d e : ℝ) : ℝ :=
  a^3*e + 4*a^2*b*d + 3*a^2*c^2 + 12*a*b^2*c + 6*b^4
/-- Remove the common exp(x/2-y), where y = pi*exp(2*x). The second
    argument is t = exp(-3*y), so these are exactly the first two modes. -/
private def twoModeJet (k : ℕ) (y t : ℝ) : ℝ := P k y + t*P k (4*y)
private def twoModeNumerator (y t : ℝ) : ℝ :=
  fourthNumerator (twoModeJet 0 y t) (twoModeJet 1 y t)
    (twoModeJet 2 y t) (twoModeJet 3 y t) (twoModeJet 4 y t)
private def Q0 (y : ℝ) : ℝ := 16*y^4 - 96*y^3 + 240*y^2 - 72*y + 135
private def Q1 (y : ℝ) : ℝ := 5184*y^7 - 35640*y^6 + 106092*y^5 -
  165418*y^4 + 145257*y^3 - 64680*y^2 + 13113*y - 945
private def Q2 (y : ℝ) : ℝ := 27648*y^7 - 103680*y^6 + 159024*y^5 -
  94480*y^4 - 444*y^3 + 24780*y^2 - 9054*y + 675
private def Q3 (y : ℝ) : ℝ := 82944*y^7 - 51840*y^6 - 71568*y^5 +
  79298*y^4 - 5043*y^3 - 25260*y^2 + 15273*y - 1755
private def Q4 (y : ℝ) : ℝ := 4096*y^4 - 6144*y^3 + 3840*y^2 - 288*y + 135
private def cubicExpLower (z : ℝ) : ℝ := 1 + 3*z + (9/2)*z^2 + (9/2)*z^3
private def firstModeReserve (y : ℝ) : ℝ := 256*y^5*Q0 y
private def frontBudget (k : ℕ) : ℝ := (2:ℝ)^(k+2)*(1+(4:ℝ)^(k+2)/8000)
private def tailBudget (k : ℕ) : ℝ := (2:ℝ)^(k+3)*(3:ℝ)^(2*k+4)
private def tailExponentialDenominator : ℝ := 20^8
/-- The full normalized tail that the analytic supplier must bound. -/
private def normalizedTail (k : ℕ) (y : ℝ) : ℝ :=
  ∑' j : ℕ, P k (((j+3:ℕ):ℝ)^2*y) *
    exp (-((((j+3:ℕ):ℝ)^2-1)*y))
private theorem twoModeNumerator_expand (y t : ℝ) :
    twoModeNumerator y t = 256*y^5*
      (-Q0 y + 4*t*Q1 y - 48*t^2*Q2 y + 64*t^3*Q3 y - 1024*t^4*Q4 y) := by
  norm_num [twoModeNumerator, fourthNumerator, twoModeJet, P, Q0, Q1, Q2, Q3, Q4]
  <;> ring
/-- Each of the five complete derivative polynomials has its leading-power
    envelope on the whole ray u >= 3. -/
private theorem P_abs_le (k : ℕ) (hk : k ≤ 4) {u : ℝ} (hu : 3 ≤ u) :
    |P k u| ≤ (2:ℝ)^(k+2)*u^(k+2) := by
  let z := u-3
  have hz : 0 ≤ z := sub_nonneg.mpr hu
  have huz : u = z+3 := by dsimp [z]; ring
  rw [huz]
  apply abs_le.mpr
  constructor <;> interval_cases k <;> dsimp [P]
  all_goals norm_num
  all_goals
    first
    | positivity
    | (apply sub_nonneg.mp; ring_nf; positivity)
private theorem Q0_ge {y : ℝ} (hy : 3 ≤ y) : y^4 ≤ Q0 y := by
  let z := y-3
  have hz : 0 ≤ z := sub_nonneg.mpr hy
  have hyz : y = z+3 := by dsimp [z]; ring
  rw [hyz]
  apply sub_nonneg.mp
  dsimp [Q0]
  ring_nf
  positivity
private theorem Q2_nonneg {y : ℝ} (hy : 3 ≤ y) : 0 ≤ Q2 y := by
  let z := y-3
  have hz : 0 ≤ z := sub_nonneg.mpr hy
  have hyz : y = z+3 := by dsimp [z]; ring
  rw [hyz]
  dsimp [Q2]
  ring_nf
  positivity
private theorem Q4_nonneg {y : ℝ} (hy : 3 ≤ y) : 0 ≤ Q4 y := by
  let z := y-3
  have hz : 0 ≤ z := sub_nonneg.mpr hy
  have hyz : y = z+3 := by dsimp [z]; ring
  rw [hyz]
  dsimp [Q4]
  ring_nf
  positivity
private theorem Q1_certificate {z : ℝ} (hz : 0 ≤ z) :
    4*Q1 (z+3) ≤ 6000*Q0 (z+3)*cubicExpLower z := by
  apply sub_nonneg.mp
  dsimp [Q1, Q0, cubicExpLower]
  ring_nf
  positivity
private theorem Q3_certificate {z : ℝ} (hz : 0 ≤ z) :
    64*Q3 (z+3) ≤ 16000000*Q0 (z+3)*(cubicExpLower z)^3 := by
  apply sub_nonneg.mp
  dsimp [Q3, Q0, cubicExpLower]
  ring_nf
  positivity
private theorem cubicExpLower_nonneg {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ cubicExpLower z := by dsimp [cubicExpLower]; positivity
private theorem cubicExpLower_le_exp {z : ℝ} (hz : 0 ≤ z) :
    cubicExpLower z ≤ exp (3*z) := by
  have h := sum_le_exp_of_nonneg (by positivity : 0 ≤ 3*z) 4
  norm_num [Finset.sum_range_succ] at h
  convert h using 1 <;> dsimp [cubicExpLower] <;> ring
private theorem exp_three_gt_twenty : (20:ℝ) < exp 3 := by
  have h := sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 3) 9
  norm_num [Finset.sum_range_succ] at h
  linarith
private theorem exp_neg_nine_le : exp (-9:ℝ) ≤ 1/8000 := by
  have h3 := exp_three_gt_twenty
  have hc : (8000:ℝ) < (exp 3)^3 := by
    nlinarith [mul_pos (sub_pos.mpr h3)
      (show 0 < (exp 3)^2+20*exp 3+400 by positivity)]
  have heq : exp (9:ℝ) = (exp 3)^3 := by
    rw [← exp_nat_mul]
    norm_num
  rw [← heq] at hc
  rw [exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 8000) hc.le
/-- A pure algebraic estimate; the actual t below pays this explicit premise. -/
private theorem twoModeNumerator_bound {y t : ℝ} (hy : 3 ≤ y) (ht : 0 ≤ t)
    (hcap : t*cubicExpLower (y-3) ≤ 1/8000) :
    twoModeNumerator y t ≤ -(7999/32000:ℝ)*firstModeReserve y := by
  have hy0 : 0 ≤ y := by linarith
  have hz : 0 ≤ y-3 := sub_nonneg.mpr hy
  have hS := cubicExpLower_nonneg hz
  have h0 : 0 ≤ Q0 y := (pow_nonneg hy0 4).trans (Q0_ge hy)
  have h1c := Q1_certificate hz
  have h3c := Q3_certificate hz
  rw [show y-3+3=y by ring] at h1c h3c
  have h1 : 4*t*Q1 y ≤ (3/4:ℝ)*Q0 y := by
    calc
      _ = t*(4*Q1 y) := by ring
      _ ≤ t*(6000*Q0 y*cubicExpLower (y-3)) :=
        mul_le_mul_of_nonneg_left h1c ht
      _ = (6000*Q0 y)*(t*cubicExpLower (y-3)) := by ring
      _ ≤ (6000*Q0 y)*(1/8000) :=
        mul_le_mul_of_nonneg_left hcap (by positivity)
      _ = _ := by ring
  have ht3 : t^3*(cubicExpLower (y-3))^3 ≤ (1/8000:ℝ)^3 := by
    simpa only [mul_pow] using
      pow_le_pow_left₀ (mul_nonneg ht hS) hcap 3
  have h3 : 64*t^3*Q3 y ≤ (1/32000:ℝ)*Q0 y := by
    calc
      _ = t^3*(64*Q3 y) := by ring
      _ ≤ t^3*(16000000*Q0 y*(cubicExpLower (y-3))^3) :=
        mul_le_mul_of_nonneg_left h3c (pow_nonneg ht 3)
      _ = (16000000*Q0 y)*(t^3*(cubicExpLower (y-3))^3) := by ring
      _ ≤ (16000000*Q0 y)*(1/8000:ℝ)^3 :=
        mul_le_mul_of_nonneg_left ht3 (by positivity)
      _ = _ := by ring
  have h2 : 0 ≤ 48*t^2*Q2 y := by
    exact mul_nonneg (by positivity) (Q2_nonneg hy)
  have h4 : 0 ≤ 1024*t^4*Q4 y := by
    exact mul_nonneg (by positivity) (Q4_nonneg hy)
  have hinner :
      -Q0 y+4*t*Q1 y-48*t^2*Q2 y+64*t^3*Q3 y-1024*t^4*Q4 y ≤
        -(7999/32000:ℝ)*Q0 y := by linarith
  rw [twoModeNumerator_expand]
  calc
    _ ≤ 256*y^5*(-(7999/32000:ℝ)*Q0 y) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = _ := by dsimp [firstModeReserve]; ring
private theorem twoMode_actual_bound {y : ℝ} (hy : 3 ≤ y) :
    twoModeNumerator y (exp (-3*y)) ≤
      -(7999/32000:ℝ)*firstModeReserve y := by
  apply twoModeNumerator_bound hy (exp_nonneg _)
  calc
    _ ≤ exp (-3*y)*exp (3*(y-3)) :=
      mul_le_mul_of_nonneg_left (cubicExpLower_le_exp (sub_nonneg.mpr hy))
        (exp_nonneg _)
    _ = exp (-9:ℝ) := by rw [← exp_add]; congr 1; ring
    _ ≤ 1/8000 := exp_neg_nine_le
/-- The exact five front budgets are [501,1008,2064,4512,12096]/125;
    the exact five tail budgets are
    [648,11664,209952,3779136,68024448]. -/
private theorem rational_perturbation_certificate :
    absoluteFourth
      (frontBudget 0 + tailBudget 0/tailExponentialDenominator)
      (frontBudget 1 + tailBudget 1/tailExponentialDenominator)
      (frontBudget 2 + tailBudget 2/tailExponentialDenominator)
      (frontBudget 3 + tailBudget 3/tailExponentialDenominator)
      (frontBudget 4 + tailBudget 4/tailExponentialDenominator) -
    absoluteFourth (frontBudget 0) (frontBudget 1) (frontBudget 2)
      (frontBudget 3) (frontBudget 4) < 1/2 := by
  norm_num [absoluteFourth, frontBudget, tailBudget, tailExponentialDenominator]
/-- A complete quadratic-exponential mode tail, with the same constant for
    every y >= 3. This is the analytic supplier behind the five tail budgets. -/
private theorem quadratic_exponential_tail_bound {P : ℝ → ℝ} {C y : ℝ} {m : ℕ}
    (hC : 0 ≤ C) (hm : m ≤ 6) (hy : 3 ≤ y)
    (hP : ∀ u : ℝ, 3 ≤ u → |P u| ≤ C * u ^ m) :
    Summable (fun j : ℕ => P (((j + 3 : ℕ) : ℝ) ^ 2 * y) *
      exp (-((((j + 3 : ℕ) : ℝ) ^ 2 - 1) * y))) ∧
    |∑' j : ℕ, P (((j + 3 : ℕ) : ℝ) ^ 2 * y) *
      exp (-((((j + 3 : ℕ) : ℝ) ^ 2 - 1) * y))| ≤
      2 * C * (3 : ℝ) ^ (2 * m) * y ^ m * exp (-8 * y) := by
  let term (j : ℕ) : ℝ := P (((j + 3 : ℕ) : ℝ) ^ 2 * y) *
    exp (-((((j + 3 : ℕ) : ℝ) ^ 2 - 1) * y))
  let D : ℝ := C * (3 : ℝ) ^ (2 * m) * y ^ m * exp (-8 * y)
  have hy0 : 0 ≤ y := by linarith
  have hd : ((2 * m : ℕ) : ℝ) ≤ 12 := by exact_mod_cast (show 2 * m ≤ 12 by omega)
  have hhalf : exp (-9 : ℝ) ≤ 1 / 2 := by
    rw [Real.exp_neg, ← one_div]
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
    linarith [Real.add_one_le_exp (9 : ℝ)]
  have hterm (j : ℕ) : |term j| ≤ D * (1 / 2 : ℝ) ^ j := by
    let n : ℝ := ((j + 3 : ℕ) : ℝ)
    have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
    have hn : n = (j : ℝ) + 3 := by simp [n]
    have hn0 : 0 ≤ n := by rw [hn]; positivity
    have hn2 : 9 ≤ n ^ 2 := by rw [hn]; nlinarith
    have hnu : 3 ≤ n ^ 2 * y := by
      calc
        (3 : ℝ) ≤ 9 * 3 := by norm_num
        _ ≤ n ^ 2 * y := by nlinarith [mul_le_mul hn2 hy (by norm_num) (by positivity)]
    have hj2 : (j : ℝ) ≤ (j : ℝ) ^ 2 := by
      exact_mod_cast (show j ≤ j ^ 2 by simpa [pow_two] using Nat.le_mul_self j)
    have hgap : 7 * (j : ℝ) ≤ n ^ 2 - 9 := by rw [hn]; nlinarith
    have hgap0 : 0 ≤ n ^ 2 - 9 := by linarith
    have hgapY : 21 * (j : ℝ) ≤ (n ^ 2 - 9) * y := by
      have := mul_le_mul hgap hy (by norm_num : (0 : ℝ) ≤ 3) hgap0
      nlinarith
    have hpoly : n ^ (2 * m) ≤ (3 : ℝ) ^ (2 * m) * exp (12 * (j : ℝ)) := by
      have hnle : n ≤ 3 * ((j : ℝ) + 1) := by rw [hn]; linarith
      have hp : ((j : ℝ) + 1) ^ (2 * m) ≤ exp (12 * (j : ℝ)) := by
        calc
          _ ≤ (exp (j : ℝ)) ^ (2 * m) :=
            pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp _) _
          _ = exp (((2 * m : ℕ) : ℝ) * (j : ℝ)) := by rw [Real.exp_nat_mul]
          _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hd hj0)
      calc
        _ ≤ (3 * ((j : ℝ) + 1)) ^ (2 * m) := pow_le_pow_left₀ hn0 hnle _
        _ = (3 : ℝ) ^ (2 * m) * ((j : ℝ) + 1) ^ (2 * m) := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)
    have hdec : exp (-((n ^ 2 - 9) * y)) ≤ exp (-21 * (j : ℝ)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hgeom : exp (-9 * (j : ℝ)) ≤ (1 / 2 : ℝ) ^ j := by
      rw [mul_comm (-9 : ℝ) (j : ℝ), Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_nonneg _) hhalf _
    have hmode : n ^ (2 * m) * exp (-((n ^ 2 - 9) * y)) ≤
        (3 : ℝ) ^ (2 * m) * (1 / 2 : ℝ) ^ j := by
      calc
        _ ≤ ((3 : ℝ) ^ (2 * m) * exp (12 * (j : ℝ))) *
            exp (-21 * (j : ℝ)) :=
          mul_le_mul hpoly hdec (Real.exp_nonneg _) (by positivity)
        _ = (3 : ℝ) ^ (2 * m) * exp (-9 * (j : ℝ)) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hgeom (by positivity)
    have hexpsplit : exp (-((n ^ 2 - 1) * y)) =
        exp (-8 * y) * exp (-((n ^ 2 - 9) * y)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    change |P (n ^ 2 * y) * exp (-((n ^ 2 - 1) * y))| ≤ _
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (C * (n ^ 2 * y) ^ m) * exp (-((n ^ 2 - 1) * y)) :=
        mul_le_mul_of_nonneg_right (hP _ hnu) (Real.exp_nonneg _)
      _ = (C * y ^ m * exp (-8 * y)) *
          (n ^ (2 * m) * exp (-((n ^ 2 - 9) * y))) := by
        rw [mul_pow, ← pow_mul, hexpsplit]
        ring
      _ ≤ (C * y ^ m * exp (-8 * y)) *
          ((3 : ℝ) ^ (2 * m) * (1 / 2 : ℝ) ^ j) :=
        mul_le_mul_of_nonneg_left hmode (by positivity)
      _ = _ := by dsimp [D]; ring
  have hgs : Summable (fun j : ℕ => D * (1 / 2 : ℝ) ^ j) :=
    (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_left D
  have hs : Summable term := hgs.of_norm_bounded fun j => by
    simpa only [Real.norm_eq_abs] using hterm j
  refine ⟨hs, ?_⟩
  change |∑' j : ℕ, term j| ≤ _
  calc
    _ ≤ ∑' j : ℕ, |term j| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' j : ℕ, D * (1 / 2 : ℝ) ^ j := hs.abs.tsum_le_tsum hterm hgs
    _ = D * 2 := by
      rw [tsum_mul_left, tsum_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)]
      norm_num
    _ = _ := by dsimp [D]; ring
/-- Consume the sharp polynomial envelopes for the actual five derivatives.
    All omitted modes remain present in normalizedTail. -/
private theorem normalizedTail_bound (k : ℕ) (hk : k ≤ 4) {y : ℝ} (hy : 3 ≤ y) :
    Summable (fun j : ℕ => P k (((j + 3 : ℕ) : ℝ) ^ 2 * y) *
      exp (-((((j + 3 : ℕ) : ℝ) ^ 2 - 1) * y))) ∧
    |normalizedTail k y| ≤ tailBudget k * y ^ (k + 2) * exp (-8 * y) := by
  have h := quadratic_exponential_tail_bound
    (P := P k) (C := (2 : ℝ) ^ (k + 2)) (m := k + 2)
    (by positivity) (by omega) hy (fun u hu => P_abs_le k hk hu)
  refine ⟨h.1, ?_⟩
  have hpow : (2 : ℝ) ^ (k + 3) = 2 * (2 : ℝ) ^ (k + 2) := by
    rw [show k + 3 = (k + 2) + 1 by omega, pow_succ]
    ring
  simpa only [normalizedTail, tailBudget, hpow,
    show 2 * (k + 2) = 2 * k + 4 by omega, mul_assoc] using h.2
/-- Exact normalization of the accepted original complete tail. This is a
    consumed algebraic bridge, not an additional content claim. -/
private theorem actual_tailJet_normalized (k : ℕ) (hk : k ≤ 4) (x : ℝ) :
    let y : ℝ := Real.pi * exp (2 * x)
    D5.S3.Zeros.Jensen.OriginalPrimalTailProjection.tailJet k 2 x =
      exp (x / 2 - y) * normalizedTail k y := by
  dsimp only
  let y : ℝ := Real.pi * exp (2 * x)
  change D5.S3.Zeros.Jensen.OriginalPrimalTailProjection.tailJet k 2 x =
    exp (x / 2 - y) * normalizedTail k y
  unfold D5.S3.Zeros.Jensen.OriginalPrimalTailProjection.tailJet normalizedTail
  rw [← tsum_mul_left]
  apply tsum_congr
  intro j
  rw [show 2 + j + 1 = j + 3 by omega]
  let u : ℝ := (((j + 3 : ℕ) : ℝ) ^ 2 * y)
  have ha :
      D5.S3.Zeros.Jensen.OriginalPrimalTailProjection.modeScale (j + 3) * exp (2 * x) = u := by
    dsimp [D5.S3.Zeros.Jensen.OriginalPrimalTailProjection.modeScale, u, y]
    ring
  have hb :
      -D5.S3.Zeros.Jensen.OriginalPrimalTailProjection.modeScale (j + 3) * exp (2 * x) = -u := by
    calc
      _ = -(D5.S3.Zeros.Jensen.OriginalPrimalTailProjection.modeScale (j + 3) *
          exp (2 * x)) := by ring
      _ = _ := by rw [ha]
  dsimp only [D5.S3.Zeros.Jensen.OriginalPrimalTailProjection.primalJet]
  rw [ha, hb, ← P_eq_jetPolynomial k hk u]
  change exp (x / 2) * exp (-u) * P k u =
    exp (x / 2 - y) * (P k u * exp (-((((j + 3 : ℕ) : ℝ) ^ 2 - 1) * y)))
  have he : exp (x / 2) * exp (-u) = exp (x / 2 - y) *
      exp (-((((j + 3 : ℕ) : ℝ) ^ 2 - 1) * y)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [u]
    ring
  rw [he]
  ring
private theorem abs_mul_perturbation
    {a b r s A B R S : ℝ}
    (ha : |a| ≤ A) (hb : |b| ≤ B) (hr : |r| ≤ R) (hs : |s| ≤ S) :
    |(a+r)*(b+s)-a*b| ≤ (A+R)*(B+S)-A*B := by
  have hA := (abs_nonneg a).trans ha
  have hB := (abs_nonneg b).trans hb
  have hR := (abs_nonneg r).trans hr
  have hS := (abs_nonneg s).trans hs
  have h1 : |a*s| ≤ A*S := by
    rw [abs_mul]
    exact mul_le_mul ha hs (abs_nonneg _) hA
  have h2 : |r*b| ≤ R*B := by
    rw [abs_mul]
    exact mul_le_mul hr hb (abs_nonneg _) hR
  have h3 : |r*s| ≤ R*S := by
    rw [abs_mul]
    exact mul_le_mul hr hs (abs_nonneg _) hR
  calc
    _ = |a*s+r*b+r*s| := by congr 1; ring
    _ ≤ |a*s+r*b|+|r*s| := abs_add_le _ _
    _ ≤ |a*s|+|r*b|+|r*s| := by linarith [abs_add_le (a*s) (r*b)]
    _ ≤ A*S+R*B+R*S := by linarith
    _ = _ := by ring
private theorem abs_four_mul_perturbation
    {a b c d r s t u A B C D R S T U : ℝ}
    (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C) (hd : |d| ≤ D)
    (hr : |r| ≤ R) (hs : |s| ≤ S) (ht : |t| ≤ T) (hu : |u| ≤ U) :
    |(a+r)*(b+s)*(c+t)*(d+u)-a*b*c*d| ≤
      (A+R)*(B+S)*(C+T)*(D+U)-A*B*C*D := by
  have hA := (abs_nonneg a).trans ha
  have hC := (abs_nonneg c).trans hc
  have hab : |a*b| ≤ A*B := by
    rw [abs_mul]
    exact mul_le_mul ha hb (abs_nonneg _) hA
  have hcd : |c*d| ≤ C*D := by
    rw [abs_mul]
    exact mul_le_mul hc hd (abs_nonneg _) hC
  have hrs := abs_mul_perturbation ha hb hr hs
  have htu := abs_mul_perturbation hc hd ht hu
  have h := abs_mul_perturbation hab hcd hrs htu
  convert h using 1 <;> (try congr 1) <;> ring
private theorem abs_add_five (a b c d e : ℝ) :
    |a+b+c+d+e| ≤ |a|+|b|+|c|+|d|+|e| := by
  calc
    _ ≤ |a+b+c+d|+|e| := abs_add_le _ _
    _ ≤ |a+b+c|+|d|+|e| := by linarith [abs_add_le (a+b+c) d]
    _ ≤ |a+b|+|c|+|d|+|e| := by linarith [abs_add_le (a+b) c]
    _ ≤ _ := by linarith [abs_add_le a b]
/-- The full quartic perturbation is bounded by the increment of its
    coefficientwise absolute polynomial, with no sign premise on the jets. -/
private theorem fourthNumerator_perturbation
    {a b c d e r s t u v A B C D E R S T U V : ℝ}
    (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C)
    (hd : |d| ≤ D) (he : |e| ≤ E)
    (hr : |r| ≤ R) (hs : |s| ≤ S) (ht : |t| ≤ T)
    (hu : |u| ≤ U) (hv : |v| ≤ V) :
    |fourthNumerator (a+r) (b+s) (c+t) (d+u) (e+v)-
      fourthNumerator a b c d e| ≤
      absoluteFourth (A+R) (B+S) (C+T) (D+U) (E+V)-absoluteFourth A B C D E := by
  have h1 := abs_four_mul_perturbation ha ha ha he hr hr hr hv
  have h2 := abs_four_mul_perturbation ha ha hb hd hr hr hs hu
  have h3 := abs_four_mul_perturbation ha ha hc hc hr hr ht ht
  have h4 := abs_four_mul_perturbation ha hb hb hc hr hs hs ht
  have h5 := abs_four_mul_perturbation hb hb hb hb hs hs hs hs
  let d1 := (a+r)^3*(e+v)-a^3*e
  let d2 := (a+r)^2*(b+s)*(d+u)-a^2*b*d
  let d3 := (a+r)^2*(c+t)^2-a^2*c^2
  let d4 := (a+r)*(b+s)^2*(c+t)-a*b^2*c
  let d5 := (b+s)^4-b^4
  have hsum := abs_add_five d1 (-4*d2) (-3*d3) (12*d4) (-6*d5)
  norm_num only [abs_mul] at hsum
  have hnormalized :
      |fourthNumerator (a+r) (b+s) (c+t) (d+u) (e+v)-
        fourthNumerator a b c d e| ≤ |d1|+4*|d2|+3*|d3|+12*|d4|+6*|d5| := by
    convert hsum using 1 <;> dsimp [d1,d2,d3,d4,d5,fourthNumerator] <;>
      (try congr 1) <;> ring
  have h1' : |d1| ≤ (A+R)^3*(E+V)-A^3*E := by
    convert h1 using 1 <;> (try dsimp [d1]) <;> (try congr 1) <;> ring
  have h2' : |d2| ≤ (A+R)^2*(B+S)*(D+U)-A^2*B*D := by
    convert h2 using 1 <;> (try dsimp [d2]) <;> (try congr 1) <;> ring
  have h3' : |d3| ≤ (A+R)^2*(C+T)^2-A^2*C^2 := by
    convert h3 using 1 <;> (try dsimp [d3]) <;> (try congr 1) <;> ring
  have h4' : |d4| ≤ (A+R)*(B+S)^2*(C+T)-A*B^2*C := by
    convert h4 using 1 <;> (try dsimp [d4]) <;> (try congr 1) <;> ring
  have h5' : |d5| ≤ (B+S)^4-B^4 := by
    convert h5 using 1 <;> (try dsimp [d5]) <;> (try congr 1) <;> ring
  dsimp [absoluteFourth]
  linarith
/-- The whole positive-coefficient perturbation polynomial, at every
    0 <= s <= 1, stays below s/2. This retains all degrees up to four. -/
private theorem scaled_rational_perturbation {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    absoluteFourth
      (frontBudget 0 + tailBudget 0/tailExponentialDenominator*s)
      (frontBudget 1 + tailBudget 1/tailExponentialDenominator*s)
      (frontBudget 2 + tailBudget 2/tailExponentialDenominator*s)
      (frontBudget 3 + tailBudget 3/tailExponentialDenominator*s)
      (frontBudget 4 + tailBudget 4/tailExponentialDenominator*s) -
    absoluteFourth (frontBudget 0) (frontBudget 1) (frontBudget 2)
      (frontBudget 3) (frontBudget 4) ≤ s/2 := by
  let deltaOne : ℝ :=
    absoluteFourth
      (frontBudget 0 + tailBudget 0/tailExponentialDenominator)
      (frontBudget 1 + tailBudget 1/tailExponentialDenominator)
      (frontBudget 2 + tailBudget 2/tailExponentialDenominator)
      (frontBudget 3 + tailBudget 3/tailExponentialDenominator)
      (frontBudget 4 + tailBudget 4/tailExponentialDenominator) -
    absoluteFourth (frontBudget 0) (frontBudget 1) (frontBudget 2)
      (frontBudget 3) (frontBudget 4)
  have hdeltaOne : deltaOne < 1/2 := rational_perturbation_certificate
  have hs2 : s^2 ≤ s := by nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs1)]
  have hs3 : s^3 ≤ s := by
    calc s^3 = s^2*s := by ring
         _ ≤ s*s := mul_le_mul_of_nonneg_right hs2 hs0
         _ ≤ s := by nlinarith
  have hs4 : s^4 ≤ s := by
    calc s^4 = s^3*s := by ring
         _ ≤ s*s := mul_le_mul_of_nonneg_right hs3 hs0
         _ ≤ s := by nlinarith
  have hscale :
      absoluteFourth
        (frontBudget 0 + tailBudget 0/tailExponentialDenominator*s)
        (frontBudget 1 + tailBudget 1/tailExponentialDenominator*s)
        (frontBudget 2 + tailBudget 2/tailExponentialDenominator*s)
        (frontBudget 3 + tailBudget 3/tailExponentialDenominator*s)
        (frontBudget 4 + tailBudget 4/tailExponentialDenominator*s) -
      absoluteFourth (frontBudget 0) (frontBudget 1) (frontBudget 2)
        (frontBudget 3) (frontBudget 4) ≤ s*deltaOne := by
    norm_num [deltaOne,absoluteFourth,frontBudget,tailBudget,tailExponentialDenominator]
    nlinarith
  exact hscale.trans (by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hdeltaOne.le hs0)
private def fullNormalizedJet (k : ℕ) (y : ℝ) : ℝ :=
  twoModeJet k y (exp (-3*y)) + normalizedTail k y
private def fullNormalizedNumerator (y : ℝ) : ℝ :=
  fourthNumerator (fullNormalizedJet 0 y) (fullNormalizedJet 1 y)
    (fullNormalizedJet 2 y) (fullNormalizedJet 3 y) (fullNormalizedJet 4 y)
private theorem twoModeJet_abs_le (k : ℕ) (hk : k ≤ 4) {y : ℝ} (hy : 3 ≤ y) :
    |twoModeJet k y (exp (-3*y))| ≤ frontBudget k*y^(k+2) := by
  have hy0 : 0 ≤ y := by linarith
  have h4y : 3 ≤ 4*y := by linarith
  have ht : exp (-3*y) ≤ 1/8000 :=
    (exp_le_exp.mpr (by linarith : -3*y ≤ (-9:ℝ))).trans exp_neg_nine_le
  calc
    _ ≤ |P k y|+|exp (-3*y)*P k (4*y)| := abs_add_le _ _
    _ = |P k y|+exp (-3*y)*|P k (4*y)| := by
      rw [abs_mul, abs_of_pos (exp_pos _)]
    _ ≤ (2:ℝ)^(k+2)*y^(k+2)+(1/8000)*((2:ℝ)^(k+2)*(4*y)^(k+2)) := by
      apply add_le_add (P_abs_le k hk hy)
      exact mul_le_mul ht (P_abs_le k hk h4y) (abs_nonneg _) (by norm_num)
    _ = _ := by dsimp [frontBudget]; rw [mul_pow]; ring
private theorem tail_exp_le {y : ℝ} (hy : 3 ≤ y) :
    exp (-8*y) ≤ 1/tailExponentialDenominator := by
  have h3 : exp (-3:ℝ) ≤ 1/20 := by
    rw [exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 20)
      exp_three_gt_twenty.le
  calc
    _ ≤ exp (-24:ℝ) := exp_le_exp.mpr (by linarith)
    _ = (exp (-3:ℝ))^8 := by rw [← exp_nat_mul]; norm_num
    _ ≤ (1/20:ℝ)^8 := pow_le_pow_left₀ (exp_nonneg _) h3 8
    _ = _ := by norm_num [tailExponentialDenominator]
private theorem weighted_tail_exp_le {y : ℝ} (hy : 3 ≤ y) :
    y^3*exp (-8*y) ≤ 27/tailExponentialDenominator := by
  let z := y-3
  have hz : 0 ≤ z := sub_nonneg.mpr hy
  have hy0 : 0 ≤ y := by linarith
  have hyb : y ≤ 3*exp (z/3) := by
    have h := add_one_le_exp (z/3)
    dsimp [z] at h ⊢
    linarith
  have hy3 : y^3 ≤ 27*exp z := by
    calc
      _ ≤ (3*exp (z/3))^3 := pow_le_pow_left₀ hy0 hyb 3
      _ = _ := by
        have he : (exp (z/3))^3 = exp z := by
          rw [← exp_nat_mul]
          congr 1
          ring
        rw [mul_pow, he]
        norm_num
  have hdec : exp (z-8*y) ≤ exp (-24:ℝ) := by
    apply exp_le_exp.mpr
    dsimp [z]
    linarith
  calc
    _ ≤ (27*exp z)*exp (-8*y) :=
      mul_le_mul_of_nonneg_right hy3 (exp_nonneg _)
    _ = 27*exp (z-8*y) := by rw [mul_assoc, ← exp_add]; congr 1; ring
    _ ≤ 27*exp (-24:ℝ) := mul_le_mul_of_nonneg_left hdec (by norm_num)
    _ ≤ 27*(1/tailExponentialDenominator) :=
      mul_le_mul_of_nonneg_left (by convert tail_exp_le (y := 3) (by norm_num) using 1 <;> norm_num)
        (by norm_num)
    _ = _ := by ring
private theorem firstModeReserve_ge {y : ℝ} (hy : 3 ≤ y) :
    256*y^9 ≤ firstModeReserve y := by
  have hy0 : 0 ≤ y := by linarith
  calc
    _ = 256*y^5*y^4 := by ring
    _ ≤ 256*y^5*Q0 y := mul_le_mul_of_nonneg_left (Q0_ge hy) (by positivity)
    _ = _ := rfl
/-- The complete infinite theta tail preserves strict negativity, uniformly
    throughout y >= 3. No frequency or mode is truncated in this statement. -/
private theorem fullNormalizedNumerator_negative {y : ℝ} (hy : 3 ≤ y) :
    fullNormalizedNumerator y < 0 := by
  have hy0 : 0 ≤ y := by linarith
  have hypos : 0 < y := by linarith
  let q := exp (-8*y)
  let C := tailExponentialDenominator
  have hC : 0 < C := by norm_num [C,tailExponentialDenominator]
  have hq : 0 ≤ q := exp_nonneg _
  have hqcap : q ≤ 1/C := tail_exp_le hy
  have hCs0 : 0 ≤ C*q := mul_nonneg hC.le hq
  have hCs1 : C*q ≤ 1 := by
    have hCn : C ≠ 0 := ne_of_gt hC
    calc
      _ ≤ C*(1/C) := mul_le_mul_of_nonneg_left hqcap hC.le
      _ = 1 := by field_simp [hCn]
  have ha (k : ℕ) (hk : k ≤ 4) := twoModeJet_abs_le k hk hy
  have hr (k : ℕ) (hk : k ≤ 4) := (normalizedTail_bound k hk hy).2
  have hp := fourthNumerator_perturbation
    (ha 0 (by omega)) (ha 1 (by omega)) (ha 2 (by omega))
    (ha 3 (by omega)) (ha 4 (by omega))
    (hr 0 (by omega)) (hr 1 (by omega)) (hr 2 (by omega))
    (hr 3 (by omega)) (hr 4 (by omega))
  let delta : ℝ :=
    absoluteFourth (frontBudget 0+tailBudget 0*q) (frontBudget 1+tailBudget 1*q)
      (frontBudget 2+tailBudget 2*q) (frontBudget 3+tailBudget 3*q)
      (frontBudget 4+tailBudget 4*q) -
    absoluteFourth (frontBudget 0) (frontBudget 1) (frontBudget 2)
      (frontBudget 3) (frontBudget 4)
  have hp' : |fullNormalizedNumerator y-twoModeNumerator y (exp (-3*y))| ≤
      y^12*delta := by
    calc
      _ ≤ _ := hp
      _ = _ := by
        dsimp [delta,q,absoluteFourth]
        ring
  have hdelta : delta ≤ C*q/2 := by
    have h := scaled_rational_perturbation hCs0 hCs1
    convert h using 1 <;>
      dsimp [delta,C,tailExponentialDenominator] <;> norm_num <;> ring
  have hweighted : y^3*q ≤ 27/C := weighted_tail_exp_le hy
  have herror : y^12*delta ≤ (27/512:ℝ)*firstModeReserve y := by
    calc
      _ ≤ y^12*(C*q/2) := mul_le_mul_of_nonneg_left hdelta (by positivity)
      _ = (y^9*C/2)*(y^3*q) := by ring
      _ ≤ (y^9*C/2)*(27/C) :=
        mul_le_mul_of_nonneg_left hweighted (by positivity)
      _ = (27/512:ℝ)*(256*y^9) := by
        dsimp [C,tailExponentialDenominator]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (firstModeReserve_ge hy) (by norm_num)
  have hreserve : 0 < firstModeReserve y :=
    (show 0 < 256*y^9 by positivity).trans_le (firstModeReserve_ge hy)
  have hfront := twoMode_actual_bound hy
  have hdiff := (le_abs_self
    (fullNormalizedNumerator y-twoModeNumerator y (exp (-3*y)))).trans hp'
  have hfull : fullNormalizedNumerator y ≤
      -(12623/64000:ℝ)*firstModeReserve y := by
    linarith
  exact hfull.trans_lt (mul_neg_of_neg_of_pos (by norm_num) hreserve)
/-- Exact normalization of an individual physical primal jet. -/
private theorem actual_primalJet_normalized (k : ℕ) (hk : k ≤ 4) (n : ℕ) (x : ℝ) :
    let y : ℝ := Real.pi*exp (2*x)
    primalJet k n x = exp (x/2-y)*
      (P k ((n:ℝ)^2*y)*exp (-(((n:ℝ)^2-1)*y))) := by
  dsimp only
  rw [primalJet, ← P_eq_jetPolynomial k hk]
  dsimp [modeScale]
  have he : exp (x/2)*exp (-(Real.pi*(n:ℝ)^2)*exp (2*x)) =
      exp (x/2-Real.pi*exp (2*x))*
        exp (-(((n:ℝ)^2-1)*(Real.pi*exp (2*x)))) := by
    rw [← exp_add, ← exp_add]
    congr 1
    ring
  have harg : Real.pi*(n:ℝ)^2*exp (2*x) =
      (n:ℝ)^2*(Real.pi*exp (2*x)) := by ring
  rw [he,harg]
  ring
private theorem actual_fullJet_normalized (k : ℕ) (hk : k ≤ 4) {x : ℝ} (hx : 0 ≤ x) :
    let y : ℝ := Real.pi*exp (2*x)
    fullJet k x = exp (x/2-y)*fullNormalizedJet k y := by
  dsimp only
  have hs := tailJet_summable_ray k 1 (by omega) hx
  have hsplit : tailJet k 1 x = primalJet k 2 x+tailJet k 2 x := by
    calc
      _ = primalJet k (1+0+1) x+
          ∑' j : ℕ, primalJet k (1+(j+1)+1) x := hs.tsum_eq_zero_add
      _ = _ := by
        congr 1
        apply tsum_congr
        intro j
        congr 1
        omega
  rw [fullJet,hsplit,actual_tailJet_normalized k hk,
    actual_primalJet_normalized k hk 1,actual_primalJet_normalized k hk 2]
  norm_num only [Nat.cast_one,one_pow,one_mul,sub_self,zero_mul,neg_zero,
    exp_zero,mul_one,Nat.cast_ofNat,show (2:ℝ)^2=4 by norm_num]
  dsimp [fullNormalizedJet,twoModeJet]
  ring
/-- Strict negativity of the literal full-theta fourth-log numerator.
    These are actual jets, including every positive integer mode. -/
private theorem actual_fullJet_fourthNumerator_negative {x : ℝ} (hx : 0 ≤ x) :
    fourthNumerator (fullJet 0 x) (fullJet 1 x) (fullJet 2 x)
      (fullJet 3 x) (fullJet 4 x) < 0 := by
  let y := Real.pi*exp (2*x)
  have hy : 3 ≤ y := by
    have he : 1 ≤ exp (2*x) := one_le_exp (by linarith)
    dsimp [y]
    nlinarith [Real.pi_gt_three]
  rw [actual_fullJet_normalized 0 (by omega) hx,
    actual_fullJet_normalized 1 (by omega) hx,
    actual_fullJet_normalized 2 (by omega) hx,
    actual_fullJet_normalized 3 (by omega) hx,
    actual_fullJet_normalized 4 (by omega) hx]
  have heq :
      fourthNumerator (exp (x/2-y)*fullNormalizedJet 0 y)
        (exp (x/2-y)*fullNormalizedJet 1 y)
        (exp (x/2-y)*fullNormalizedJet 2 y)
        (exp (x/2-y)*fullNormalizedJet 3 y)
        (exp (x/2-y)*fullNormalizedJet 4 y) =
      (exp (x/2-y))^4*fullNormalizedNumerator y := by
    dsimp [fourthNumerator,fullNormalizedNumerator]
    ring
  change fourthNumerator _ _ _ _ _ < 0
  rw [heq]
  exact mul_neg_of_pos_of_neg (pow_pos (exp_pos _) 4)
    (fullNormalizedNumerator_negative hy)
private theorem actual_phi_has_full_mode_sum (x : ℝ) :
    Summable (fun j : ℕ => primalJet 0 (j+1) x) ∧
    romikPhi x = ∑' j : ℕ, primalJet 0 (j+1) x := by
  have ht : 0 < exp (2*x) := exp_pos _
  have hs := (((thetaSeries_summable 4 ht).mul_left
      (2*Real.pi^2*(exp (2*x))^2)).sub
      ((thetaSeries_summable 2 ht).mul_left (3*Real.pi*exp (2*x)))).mul_left
        (2*exp (x/2))
  have hterm (j : ℕ) :
      2*exp (x/2)*
        (2*Real.pi^2*(exp (2*x))^2*
            (((j:ℝ)+1)^4*exp (-Real.pi*((j:ℝ)+1)^2*exp (2*x)))-
          (3*Real.pi*exp (2*x))*
            (((j:ℝ)+1)^2*exp (-Real.pi*((j:ℝ)+1)^2*exp (2*x)))) =
      primalJet 0 (j+1) x := by
    dsimp [primalJet,jetPolynomial,modeScale]
    simp only [Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_pow,Polynomial.eval_X]
    push_cast
    ring
  have hsum : Summable (fun j : ℕ => primalJet 0 (j+1) x) := by
    convert hs using 1
    funext j
    exact (hterm j).symm
  refine ⟨hsum,?_⟩
  rw [romikPhi,omega,← tsum_mul_left]
  apply tsum_congr
  intro j
  dsimp [primalJet,jetPolynomial,modeScale]
  simp only [Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_pow,Polynomial.eval_X]
  push_cast
  ring
private theorem actual_fullJet_zero_eq_phi_all (x : ℝ) : fullJet 0 x = romikPhi x := by
  obtain ⟨hs,hphi⟩ := actual_phi_has_full_mode_sum x
  have hsplit : (∑' j : ℕ, primalJet 0 (j+1) x) = fullJet 0 x := by
    calc
      _ = primalJet 0 (0+1) x+∑' j : ℕ, primalJet 0 ((j+1)+1) x :=
        hs.tsum_eq_zero_add
      _ = _ := by
        dsimp only [fullJet,tailJet]
        congr 1
        apply tsum_congr
        intro j
        congr 1
        omega
  exact (hphi.trans hsplit).symm
private theorem actual_fullJet_eq_phi_iterated_all (k : ℕ) (x : ℝ) :
    fullJet k x = iteratedDeriv k romikPhi x := by
  have heq : fullJet 0 = romikPhi := funext actual_fullJet_zero_eq_phi_all
  rw [fullJet_eq_iterated,heq]
private theorem actual_fullJet_one_odd (x : ℝ) : fullJet 1 (-x) = -fullJet 1 x := by
  have h0 : (fun t : ℝ => fullJet 0 (-t)) = fullJet 0 := by
    funext t
    rw [actual_fullJet_zero_eq_phi_all,actual_fullJet_zero_eq_phi_all,romikPhi_even]
  have hl := (fullJet_deriv 0 (-x)).comp x (hasDerivAt_neg x)
  change HasDerivAt (fun t : ℝ => fullJet 0 (-t)) _ x at hl
  rw [h0] at hl
  have heq := hl.unique (fullJet_deriv 0 x)
  norm_num at heq ⊢
  linarith
private theorem actual_fullJet_two_even (x : ℝ) : fullJet 2 (-x) = fullJet 2 x := by
  have h1 : (fun t : ℝ => fullJet 1 (-t)) = fun t => -fullJet 1 t :=
    funext actual_fullJet_one_odd
  have hl := (fullJet_deriv 1 (-x)).comp x (hasDerivAt_neg x)
  change HasDerivAt (fun t : ℝ => fullJet 1 (-t)) _ x at hl
  rw [h1] at hl
  have heq := hl.unique (fullJet_deriv 1 x).neg
  norm_num at heq ⊢
  linarith
private theorem actual_fullJet_three_odd (x : ℝ) : fullJet 3 (-x) = -fullJet 3 x := by
  have h2 : (fun t : ℝ => fullJet 2 (-t)) = fullJet 2 :=
    funext actual_fullJet_two_even
  have hl := (fullJet_deriv 2 (-x)).comp x (hasDerivAt_neg x)
  change HasDerivAt (fun t : ℝ => fullJet 2 (-t)) _ x at hl
  rw [h2] at hl
  have heq := hl.unique (fullJet_deriv 2 x)
  norm_num at heq ⊢
  linarith
private theorem actual_fullJet_odd_origin : fullJet 1 0 = 0 ∧ fullJet 3 0 = 0 := by
  have h1 := actual_fullJet_one_odd 0
  have h3 := actual_fullJet_three_odd 0
  norm_num at h1 h3
  exact ⟨by linarith,by linarith⟩
private def logJet1 (F0 F1 : ℝ → ℝ) (x : ℝ) : ℝ := F1 x / F0 x
private def logJet2 (F0 F1 F2 : ℝ → ℝ) (x : ℝ) : ℝ :=
  F2 x / F0 x - (F1 x) ^ 2 / (F0 x) ^ 2
private def logJet3 (F0 F1 F2 F3 : ℝ → ℝ) (x : ℝ) : ℝ :=
  F3 x / F0 x - 3 * ((F1 x * F2 x) / (F0 x) ^ 2) +
    2 * ((F1 x) ^ 3 / (F0 x) ^ 3)
/-- Exactly the actual fourth-log numerator N divided by F0^4. -/
private def logJet4 (F0 F1 F2 F3 F4 : ℝ → ℝ) (x : ℝ) : ℝ :=
  ((F0 x) ^ 3 * F4 x - 4 * (F0 x) ^ 2 * F1 x * F3 x -
      3 * (F0 x) ^ 2 * (F2 x) ^ 2 + 12 * F0 x * (F1 x) ^ 2 * F2 x -
      6 * (F1 x) ^ 4) / (F0 x) ^ 4
/-- The complete local logarithmic jet chain. A positive actual kernel
    supplies hne, while its original smooth jets supply h0 through h3. -/
private theorem hasDerivAt_log_four_jets (F0 F1 F2 F3 F4 : ℝ → ℝ) {x : ℝ}
    (h0 : HasDerivAt F0 (F1 x) x) (h1 : HasDerivAt F1 (F2 x) x)
    (h2 : HasDerivAt F2 (F3 x) x) (h3 : HasDerivAt F3 (F4 x) x)
    (hne : F0 x ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log (F0 t)) (logJet1 F0 F1 x) x ∧
      HasDerivAt (logJet1 F0 F1) (logJet2 F0 F1 F2 x) x ∧
      HasDerivAt (logJet2 F0 F1 F2) (logJet3 F0 F1 F2 F3 x) x ∧
      HasDerivAt (logJet3 F0 F1 F2 F3) (logJet4 F0 F1 F2 F3 F4 x) x := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [logJet1] using! h0.log hne
  · convert! h1.div h0 hne using 1 <;>
      dsimp only [logJet1, logJet2] <;> field_simp [hne] <;> ring
  · convert! (h2.div h0 hne).sub
      ((h1.pow 2).div (h0.pow 2) (pow_ne_zero _ hne)) using 1 <;>
      simp only [logJet2, logJet3, Pi.pow_apply, Pi.mul_apply] <;>
      field_simp [hne] <;> ring
  · convert! ((h3.div h0 hne).sub
      (((h1.mul h2).div (h0.pow 2) (pow_ne_zero _ hne)).const_mul (3 : ℝ))).add
      (((h1.pow 3).div (h0.pow 3) (pow_ne_zero _ hne)).const_mul (2 : ℝ)) using 1 <;>
      simp only [logJet3, logJet4, Pi.pow_apply, Pi.mul_apply] <;>
      field_simp [hne] <;> ring
/-- Negative fourth derivative and vanishing odd origin jets imply a
    positive radial curvature gap and strict concavity in the square variable.
    Explicit jet assumptions keep this reusable independently of the actual
    theta-kernel logarithmic-derivative computation. -/
private theorem squareVariable_strictConcavity_of_fourthJet_neg
    (f0 f1 f2 f3 f4 : ℝ → ℝ)
    (h01 : ∀ x : ℝ, 0 ≤ x → HasDerivAt f0 (f1 x) x)
    (h12 : ∀ x : ℝ, 0 ≤ x → HasDerivAt f1 (f2 x) x)
    (h23 : ∀ x : ℝ, 0 ≤ x → HasDerivAt f2 (f3 x) x)
    (h34 : ∀ x : ℝ, 0 ≤ x → HasDerivAt f3 (f4 x) x)
    (h10 : f1 0 = 0) (h30 : f3 0 = 0)
    (h4neg : ∀ x : ℝ, 0 < x → f4 x < 0) :
    (∀ x : ℝ, 0 < x → 0 < f1 x - x * f2 x) ∧
      StrictConcaveOn ℝ (Ioi (0 : ℝ)) (fun r : ℝ => f0 (Real.sqrt r)) := by
  have hanti3 : StrictAntiOn f3 (Ici (0 : ℝ)) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici (0 : ℝ))
      (fun x hx => (h34 x hx).continuousAt.continuousWithinAt)
    intro x hx
    have hx0 : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
    rw [(h34 x hx0.le).deriv]
    exact h4neg x hx0
  have h3neg (x : ℝ) (hx : 0 < x) : f3 x < 0 := by
    simpa only [h30] using hanti3 (show (0 : ℝ) ∈ Ici 0 by simp) hx.le hx
  let K : ℝ → ℝ := fun x => f1 x - x * f2 x
  have hK (x : ℝ) (hx : 0 ≤ x) : HasDerivAt K (-x * f3 x) x := by
    convert! (h12 x hx).sub ((hasDerivAt_id x).mul (h23 x hx)) using 1 <;>
      simp only [K, id_eq, one_mul] <;> ring
  have hmonoK : StrictMonoOn K (Ici (0 : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ))
      (fun x hx => (hK x hx).continuousAt.continuousWithinAt)
    intro x hx
    have hx0 : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
    rw [(hK x hx0.le).deriv]
    simpa only [neg_mul] using neg_pos.mpr (mul_neg_of_pos_of_neg hx0 (h3neg x hx0))
  have hgap (x : ℝ) (hx : 0 < x) : 0 < f1 x - x * f2 x := by
    simpa only [K, zero_mul, sub_zero, h10] using
      hmonoK (show (0 : ℝ) ∈ Ici 0 by simp) hx.le hx
  refine ⟨hgap, ?_⟩
  let G : ℝ → ℝ := fun r => f0 (Real.sqrt r)
  let H : ℝ → ℝ := fun r => f1 (Real.sqrt r) / (2 * Real.sqrt r)
  have hG (r : ℝ) (hr : 0 < r) : HasDerivAt G (H r) r := by
    convert! (h01 (Real.sqrt r) (Real.sqrt_nonneg r)).comp r
      (Real.hasDerivAt_sqrt hr.ne') using 1 <;> dsimp only [G, H] <;> ring
  have hH (r : ℝ) (hr : 0 < r) :
      HasDerivAt H
        ((Real.sqrt r * f2 (Real.sqrt r) - f1 (Real.sqrt r)) /
          (4 * (Real.sqrt r) ^ 3)) r := by
    have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
    have hsder := Real.hasDerivAt_sqrt hr.ne'
    have hnum := (h12 (Real.sqrt r) hs.le).comp r hsder
    have hden := hsder.const_mul (2 : ℝ)
    convert! hnum.div hden (by positivity : (2 : ℝ) * Real.sqrt r ≠ 0) using 1 <;>
      simp only [H, Function.comp_def] <;> field_simp [hs.ne'] <;> ring
  have hHneg (r : ℝ) (hr : 0 < r) : deriv H r < 0 := by
    rw [(hH r hr).deriv]
    apply div_neg_of_neg_of_pos
    · linarith [hgap (Real.sqrt r) (Real.sqrt_pos.mpr hr)]
    · positivity
  have hantiH : StrictAntiOn H (Ioi (0 : ℝ)) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioi (0 : ℝ))
      (fun r hr => (hH r hr).continuousAt.continuousWithinAt)
    intro r hr
    apply hHneg
    simpa only [interior_Ioi, mem_Ioi] using hr
  change StrictConcaveOn ℝ (Ioi (0 : ℝ)) G
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioi (0 : ℝ))
    (fun r hr => (hG r hr).continuousAt.continuousWithinAt)
  intro a ha b hb hab
  have ha0 : 0 < a := by simpa only [interior_Ioi, mem_Ioi] using ha
  have hb0 : 0 < b := by simpa only [interior_Ioi, mem_Ioi] using hb
  rw [(hG b hb0).deriv, (hG a ha0).deriv]
  exact hantiH ha0 hb0 hab
/-- The exact Csordas radial curvature target and square-variable strict
    concavity for the original theta kernel. No curvature hypothesis,
    finite-mode truncation, or RH hypothesis is introduced. -/
theorem actual_phi_radial_curvature_and_square_concavity :
    (∀ x : ℝ, 0 < x →
      0 < x*((iteratedDeriv 1 romikPhi x)^2-
        romikPhi x*iteratedDeriv 2 romikPhi x)+
          romikPhi x*iteratedDeriv 1 romikPhi x) ∧
    StrictConcaveOn ℝ (Ioi (0:ℝ)) (fun r : ℝ => Real.log (romikPhi (Real.sqrt r))) := by
  have hpos (x : ℝ) : 0 < fullJet 0 x := by
    rw [actual_fullJet_zero_eq_phi_all,romikPhi_eq_source]
    exact (source_theta_gaussian_bound x).1
  let ell0 : ℝ → ℝ := fun x => Real.log (fullJet 0 x)
  let ell1 : ℝ → ℝ := logJet1 (fullJet 0) (fullJet 1)
  let ell2 : ℝ → ℝ := logJet2 (fullJet 0) (fullJet 1) (fullJet 2)
  let ell3 : ℝ → ℝ := logJet3 (fullJet 0) (fullJet 1) (fullJet 2) (fullJet 3)
  let ell4 : ℝ → ℝ :=
    logJet4 (fullJet 0) (fullJet 1) (fullJet 2) (fullJet 3) (fullJet 4)
  have hlog (x : ℝ) := hasDerivAt_log_four_jets
    (fullJet 0) (fullJet 1) (fullJet 2) (fullJet 3) (fullJet 4)
    (fullJet_deriv 0 x) (fullJet_deriv 1 x) (fullJet_deriv 2 x) (fullJet_deriv 3 x)
    (hpos x).ne'
  have h10 : ell1 0 = 0 := by
    dsimp [ell1,logJet1]
    rw [actual_fullJet_odd_origin.1]
    simp
  have h30 : ell3 0 = 0 := by
    dsimp [ell3,logJet3]
    rw [actual_fullJet_odd_origin.1,actual_fullJet_odd_origin.2]
    simp
  have h4neg (x : ℝ) (hx : 0 < x) : ell4 x < 0 := by
    change fourthNumerator (fullJet 0 x) (fullJet 1 x) (fullJet 2 x)
      (fullJet 3 x) (fullJet 4 x)/(fullJet 0 x)^4 < 0
    exact div_neg_of_neg_of_pos (actual_fullJet_fourthNumerator_negative hx.le)
      (pow_pos (hpos x) 4)
  have h := squareVariable_strictConcavity_of_fourthJet_neg ell0 ell1 ell2 ell3 ell4
    (fun x _ => (hlog x).1)
    (fun x _ => (hlog x).2.1)
    (fun x _ => (hlog x).2.2.1)
    (fun x _ => (hlog x).2.2.2)
    h10 h30 h4neg
  refine ⟨?_,?_⟩
  · intro x hx
    have hg := mul_pos (pow_pos (hpos x) 2) (h.1 x hx)
    have heq :
        (fullJet 0 x)^2*(ell1 x-x*ell2 x) =
          x*((fullJet 1 x)^2-fullJet 0 x*fullJet 2 x)+fullJet 0 x*fullJet 1 x := by
      dsimp [ell1,ell2,logJet1,logJet2]
      field_simp [(hpos x).ne']
      ring
    rw [heq] at hg
    rw [actual_fullJet_eq_phi_iterated_all 0,actual_fullJet_eq_phi_iterated_all 1,
      actual_fullJet_eq_phi_iterated_all 2] at hg
    simpa only [iteratedDeriv_zero] using hg
  · simpa only [ell0,actual_fullJet_zero_eq_phi_all] using h.2

/-! The finite-mode and full-tail certificate above is internal to the
    construction.  This corollary exposes its analytic conclusion directly
    in terms of the original theta kernel and its ordinary jets. -/
theorem romikPhi_fourth_log_numerator_negative {x : ℝ} (hx : 0 ≤ x) :
    (romikPhi x)^3 * iteratedDeriv 4 romikPhi x -
        4 * (romikPhi x)^2 * iteratedDeriv 1 romikPhi x * iteratedDeriv 3 romikPhi x -
        3 * (romikPhi x)^2 * (iteratedDeriv 2 romikPhi x)^2 +
        12 * romikPhi x * (iteratedDeriv 1 romikPhi x)^2 * iteratedDeriv 2 romikPhi x -
        6 * (iteratedDeriv 1 romikPhi x)^4 < 0 := by
  have h := actual_fullJet_fourthNumerator_negative hx
  rw [actual_fullJet_eq_phi_iterated_all 0 x,
    actual_fullJet_eq_phi_iterated_all 1 x,
    actual_fullJet_eq_phi_iterated_all 2 x,
    actual_fullJet_eq_phi_iterated_all 3 x,
    actual_fullJet_eq_phi_iterated_all 4 x] at h
  simpa only [fourthNumerator, iteratedDeriv_zero] using h
end D5.S3.Analytic.Fourier.ThetaRadialCurvature
