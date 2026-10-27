import D5.S3.Weil.ZetaGamma.FormCore.GaussianGammaDomainCheck
import D5.S3.Zeros.Jensen.OriginalPrimalTailProjection
import Mathlib.Tactic

/- Uncompiled source fragment. All variables and constants here refer to the
   literal complete theta kernel. The analytic tail supplier must retain all
   n >= 3 terms; the polynomial identities alone do not prove the full result. -/


noncomputable section

namespace RhTransient.ThetaLogFourthCertificate

open Real Polynomial
open D5.S3.Zeros.Jensen.OriginalPrimalTailProjection

/-- The five actual primal derivative polynomials. -/
def P : ℕ → ℝ → ℝ
  | 0, u => 4*u^2 - 6*u
  | 1, u => -8*u^3 + 30*u^2 - 15*u
  | 2, u => 16*u^4 - 112*u^3 + 165*u^2 - (75/2)*u
  | 3, u => -32*u^5 + 360*u^4 - 1058*u^3 + (1635/2)*u^2 - (375/4)*u
  | 4, u => 64*u^6 - 1056*u^5 + 5176*u^4 - 8512*u^3 +
      (15465/4)*u^2 - (1875/8)*u
  | _, _ => 0

theorem P_eq_jetPolynomial (k : ℕ) (hk : k ≤ 4) (u : ℝ) :
    P k u = (jetPolynomial k).eval u := by
  interval_cases k <;>
    norm_num [P, jetPolynomial, derivative_sub, derivative_add,
      derivative_mul, derivative_pow] <;> ring

/-- The numerator of the fourth derivative of the logarithm. The five
    arguments are the zeroth through fourth derivatives in x. -/
def fourthNumerator (a b c d e : ℝ) : ℝ :=
  a^3*e - 4*a^2*b*d - 3*a^2*c^2 + 12*a*b^2*c - 6*b^4

/-- Its coefficientwise absolute polynomial, used only for tail perturbations. -/
def absoluteFourth (a b c d e : ℝ) : ℝ :=
  a^3*e + 4*a^2*b*d + 3*a^2*c^2 + 12*a*b^2*c + 6*b^4

/-- Remove the common exp(x/2-y), where y = pi*exp(2*x). The second
    argument is t = exp(-3*y), so these are exactly the first two modes. -/
def twoModeJet (k : ℕ) (y t : ℝ) : ℝ := P k y + t*P k (4*y)

def twoModeNumerator (y t : ℝ) : ℝ :=
  fourthNumerator (twoModeJet 0 y t) (twoModeJet 1 y t)
    (twoModeJet 2 y t) (twoModeJet 3 y t) (twoModeJet 4 y t)

def Q0 (y : ℝ) : ℝ := 16*y^4 - 96*y^3 + 240*y^2 - 72*y + 135
def Q1 (y : ℝ) : ℝ := 5184*y^7 - 35640*y^6 + 106092*y^5 -
  165418*y^4 + 145257*y^3 - 64680*y^2 + 13113*y - 945
def Q2 (y : ℝ) : ℝ := 27648*y^7 - 103680*y^6 + 159024*y^5 -
  94480*y^4 - 444*y^3 + 24780*y^2 - 9054*y + 675
def Q3 (y : ℝ) : ℝ := 82944*y^7 - 51840*y^6 - 71568*y^5 +
  79298*y^4 - 5043*y^3 - 25260*y^2 + 15273*y - 1755
def Q4 (y : ℝ) : ℝ := 4096*y^4 - 6144*y^3 + 3840*y^2 - 288*y + 135

def cubicExpLower (z : ℝ) : ℝ := 1 + 3*z + (9/2)*z^2 + (9/2)*z^3

def firstModeReserve (y : ℝ) : ℝ := 256*y^5*Q0 y

def frontBudget (k : ℕ) : ℝ := (2:ℝ)^(k+2)*(1+(4:ℝ)^(k+2)/8000)
def tailBudget (k : ℕ) : ℝ := (2:ℝ)^(k+3)*(3:ℝ)^(2*k+4)
def tailExponentialDenominator : ℝ := 20^8

/-- The full normalized tail that the analytic supplier must bound. -/
def normalizedTail (k : ℕ) (y : ℝ) : ℝ :=
  ∑' j : ℕ, P k (((j+3:ℕ):ℝ)^2*y) *
    exp (-((((j+3:ℕ):ℝ)^2-1)*y))

theorem twoModeNumerator_expand (y t : ℝ) :
    twoModeNumerator y t = 256*y^5*
      (-Q0 y + 4*t*Q1 y - 48*t^2*Q2 y + 64*t^3*Q3 y - 1024*t^4*Q4 y) := by
  norm_num [twoModeNumerator, fourthNumerator, twoModeJet, P, Q0, Q1, Q2, Q3, Q4]
  <;> ring

/-- Each of the five complete derivative polynomials has its leading-power
    envelope on the whole ray u >= 3. -/
theorem P_abs_le (k : ℕ) (hk : k ≤ 4) {u : ℝ} (hu : 3 ≤ u) :
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

theorem Q0_ge {y : ℝ} (hy : 3 ≤ y) : y^4 ≤ Q0 y := by
  let z := y-3
  have hz : 0 ≤ z := sub_nonneg.mpr hy
  have hyz : y = z+3 := by dsimp [z]; ring
  rw [hyz]
  apply sub_nonneg.mp
  dsimp [Q0]
  ring_nf
  positivity

theorem Q2_nonneg {y : ℝ} (hy : 3 ≤ y) : 0 ≤ Q2 y := by
  let z := y-3
  have hz : 0 ≤ z := sub_nonneg.mpr hy
  have hyz : y = z+3 := by dsimp [z]; ring
  rw [hyz]
  dsimp [Q2]
  ring_nf
  positivity

theorem Q4_nonneg {y : ℝ} (hy : 3 ≤ y) : 0 ≤ Q4 y := by
  let z := y-3
  have hz : 0 ≤ z := sub_nonneg.mpr hy
  have hyz : y = z+3 := by dsimp [z]; ring
  rw [hyz]
  dsimp [Q4]
  ring_nf
  positivity

theorem Q1_certificate {z : ℝ} (hz : 0 ≤ z) :
    4*Q1 (z+3) ≤ 6000*Q0 (z+3)*cubicExpLower z := by
  apply sub_nonneg.mp
  dsimp [Q1, Q0, cubicExpLower]
  ring_nf
  positivity

theorem Q3_certificate {z : ℝ} (hz : 0 ≤ z) :
    64*Q3 (z+3) ≤ 16000000*Q0 (z+3)*(cubicExpLower z)^3 := by
  apply sub_nonneg.mp
  dsimp [Q3, Q0, cubicExpLower]
  ring_nf
  positivity

theorem cubicExpLower_nonneg {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ cubicExpLower z := by dsimp [cubicExpLower]; positivity

theorem cubicExpLower_le_exp {z : ℝ} (hz : 0 ≤ z) :
    cubicExpLower z ≤ exp (3*z) := by
  have h := sum_le_exp_of_nonneg (by positivity : 0 ≤ 3*z) 4
  norm_num [Finset.sum_range_succ] at h
  convert h using 1 <;> dsimp [cubicExpLower] <;> ring

theorem exp_three_gt_twenty : (20:ℝ) < exp 3 := by
  have h := sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 3) 9
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem exp_neg_nine_le : exp (-9:ℝ) ≤ 1/8000 := by
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
theorem twoModeNumerator_bound {y t : ℝ} (hy : 3 ≤ y) (ht : 0 ≤ t)
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

theorem twoMode_actual_bound {y : ℝ} (hy : 3 ≤ y) :
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
theorem rational_perturbation_certificate :
    absoluteFourth
      (frontBudget 0 + tailBudget 0/tailExponentialDenominator)
      (frontBudget 1 + tailBudget 1/tailExponentialDenominator)
      (frontBudget 2 + tailBudget 2/tailExponentialDenominator)
      (frontBudget 3 + tailBudget 3/tailExponentialDenominator)
      (frontBudget 4 + tailBudget 4/tailExponentialDenominator) -
    absoluteFourth (frontBudget 0) (frontBudget 1) (frontBudget 2)
      (frontBudget 3) (frontBudget 4) < 1/2 := by
  norm_num [absoluteFourth, frontBudget, tailBudget, tailExponentialDenominator]

end RhTransient.ThetaLogFourthCertificate

/- Uncompiled source fragment. Append after ThetaLogFourthCertificate.fragment.lean.
   The bound covers the complete infinite tail indexed by j+3, including all
   n >= 3. It uses no truncation or finite sample. The sharp five polynomial
   bounds are supplied by P_abs_le in the preceding fragment. -/

namespace RhTransient.ThetaLogFourthCertificate

open Real

/-- A complete quadratic-exponential mode tail, with the same constant for
    every y >= 3. This is the analytic supplier behind the five tail budgets. -/
theorem quadratic_exponential_tail_bound {P : ℝ → ℝ} {C y : ℝ} {m : ℕ}
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
theorem normalizedTail_bound (k : ℕ) (hk : k ≤ 4) {y : ℝ} (hy : 3 ≤ y) :
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
theorem actual_tailJet_normalized (k : ℕ) (hk : k ≤ 4) (x : ℝ) :
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

end RhTransient.ThetaLogFourthCertificate


#print axioms RhTransient.ThetaLogFourthCertificate.normalizedTail_bound
#print axioms RhTransient.ThetaLogFourthCertificate.twoModeNumerator_bound
