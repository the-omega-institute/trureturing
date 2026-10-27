import D5.S3.Weil.ZetaGamma.FormCore.GaussianGammaDomainCheck
import D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiThetaExcess
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.Bernoulli
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Real

open D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft
open private literalGaussian correctedGaussian centeredGaussianCharge literalGaussian_actualProfile from
  D5.S3.Weil.ZetaGamma.FormCore.GaussianGammaDomainCheck

/-
Transient analytic estimate, not compiled or admitted.
No new canonical G is proposed by the pi-specialized applications below.
Existing Real.rpow identities reduce the two Taylor bounds to polynomial
nonnegativity in the fourth root. No differentiation of rpow at zero occurs.
-/


set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaGamma.FormCore.RpowFiveQuartersDraft

open Real

theorem one_add_rpow_five_quarters_bounds {t : ℝ} (ht : 0 ≤ t) :
    1+(5/4:ℝ)*t ≤ (1+t)^(5/4:ℝ) ∧
    (1+t)^(5/4:ℝ) ≤ 1+(5/4:ℝ)*t+(5/32:ℝ)*t^2 := by
  let z : ℝ := (1+t)^(1/4:ℝ)
  have hz : 1 ≤ z := one_le_rpow (by linarith) (by norm_num)
  have hz0 : 0 ≤ z := by linarith
  have h4 : z^4 = 1+t := by
    dsimp only [z]
    rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ 1+t)]
    norm_num
  have h5 : z^5 = (1+t)^(5/4:ℝ) := by
    dsimp only [z]
    rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ 1+t)]
    norm_num
  have h8 : z^8 = (1+t)^2 := by
    calc
      _ = (z^4)^2 := by ring
      _ = _ := by rw [h4]
  have hlow : 0 ≤ 4*z^5-5*z^4+1 := by
    have he : 4*z^5-5*z^4+1 =
        (z-1)^2*(4*z^3+3*z^2+2*z+1) := by ring
    rw [he]
    positivity
  have hupp : 0 ≤ 5*z^8+30*z^4-32*z^5-3 := by
    have he : 5*z^8+30*z^4-32*z^5-3 =
        (z-1)^3*(5*z^5+15*z^4+30*z^3+18*z^2+9*z+3) := by ring
    rw [he]
    exact mul_nonneg (pow_nonneg (by linarith) 3) (by positivity)
  rw [h4, h5] at hlow
  rw [h8, h4, h5] at hupp
  constructor <;> nlinarith only [hlow, hupp]

/-- Tangent lower bound and quadratic upper bound at any positive base. -/
theorem add_rpow_five_quarters_bounds {a y : ℝ} (ha : 0 < a) (hy : 0 ≤ y) :
    a^(5/4:ℝ)+(5/4:ℝ)*a^(1/4:ℝ)*y ≤ (a+y)^(5/4:ℝ) ∧
    (a+y)^(5/4:ℝ) ≤
      a^(5/4:ℝ)+(5/4:ℝ)*a^(1/4:ℝ)*y+(5/32:ℝ)*a^(-3/4:ℝ)*y^2 := by
  have h := one_add_rpow_five_quarters_bounds (div_nonneg hy ha.le)
  have hp : 0 ≤ a^(5/4:ℝ) := (rpow_pos_of_pos ha _).le
  have hpow : (a+y)^(5/4:ℝ) = a^(5/4:ℝ)*(1+y/a)^(5/4:ℝ) := by
    rw [show a+y = a*(1+y/a) by field_simp [ha.ne'] <;> ring,
      Real.mul_rpow ha.le (by positivity : 0 ≤ 1+y/a)]
  have hlinear : a^(5/4:ℝ)*(y/a) = a^(1/4:ℝ)*y := by
    rw [show (5/4:ℝ) = 1/4+1 by norm_num, Real.rpow_add_one ha.ne']
    field_simp [ha.ne'] <;> ring
  have hquadratic : a^(5/4:ℝ)*(y/a)^2 = a^(-3/4:ℝ)*y^2 := by
    rw [show (5/4:ℝ) = -3/4+2 by norm_num, Real.rpow_add ha,
      Real.rpow_two]
    field_simp [ha.ne'] <;> ring
  constructor
  · calc
      _ = a^(5/4:ℝ)*(1+(5/4:ℝ)*(y/a)) := by
        rw [mul_add, mul_one]
        linear_combination -(5/4:ℝ)*hlinear
      _ ≤ a^(5/4:ℝ)*(1+y/a)^(5/4:ℝ) :=
        mul_le_mul_of_nonneg_left h.1 hp
      _ = _ := hpow.symm
  · calc
      _ = a^(5/4:ℝ)*(1+y/a)^(5/4:ℝ) := hpow
      _ ≤ a^(5/4:ℝ)*(1+(5/4:ℝ)*(y/a)+(5/32:ℝ)*(y/a)^2) :=
        mul_le_mul_of_nonneg_left h.2 hp
      _ = a^(5/4:ℝ)+(5/4:ℝ)*(a^(5/4:ℝ)*(y/a))+
          (5/32:ℝ)*(a^(5/4:ℝ)*(y/a)^2) := by ring
      _ = _ := by rw [hlinear, hquadratic]; ring

theorem pi_add_rpow_five_quarters_bounds {y : ℝ} (hy : 0 ≤ y) :
    Real.pi^(5/4:ℝ)+(5/4:ℝ)*Real.pi^(1/4:ℝ)*y ≤ (Real.pi+y)^(5/4:ℝ) ∧
    (Real.pi+y)^(5/4:ℝ) ≤ Real.pi^(5/4:ℝ)+
      (5/4:ℝ)*Real.pi^(1/4:ℝ)*y+(5/32:ℝ)*Real.pi^(-3/4:ℝ)*y^2 :=
  add_rpow_five_quarters_bounds Real.pi_pos hy

theorem pi_rpow_five_quarters_bounds {x : ℝ} (hx : Real.pi ≤ x) :
    Real.pi^(5/4:ℝ)+(5/4:ℝ)*Real.pi^(1/4:ℝ)*(x-Real.pi) ≤ x^(5/4:ℝ) ∧
    x^(5/4:ℝ) ≤ Real.pi^(5/4:ℝ)+
      (5/4:ℝ)*Real.pi^(1/4:ℝ)*(x-Real.pi)+
      (5/32:ℝ)*Real.pi^(-3/4:ℝ)*(x-Real.pi)^2 := by
  have harg : Real.pi+(x-Real.pi) = x := by ring
  simpa only [harg] using
    (pi_add_rpow_five_quarters_bounds (sub_nonneg.mpr hx))

end D5.S3.Weil.ZetaGamma.FormCore.RpowFiveQuartersDraft

/- SOURCE DRAFT, NOT COMPILED. Transient applications only; no new D5 G.
   Append after RpowFiveQuartersBounds.fragment.lean; merge imports at top.

   EXACT actual-mu coefficient check:
   meanCharge_physical_moment_formula gives
     5*mu(F) = integral_pi^inf (6*pi^(5/4)-x^(5/4))*fullTheta F(x) dx.
   Its Gaussian n-th mode is n^4*A*exp(-lambda*n^2*x), NOT n^2 before
   changing coordinates.  With I_r as defined below,
     5*mu(g_a) = A*exp(-pi*lambda) * C_lambda,
     C_lambda = sum_(n>=1) n^4*exp(-pi*lambda*(n^2-1))*I_(lambda*n^2).
   A=exp(9a/2), lambda=exp(2a). Hence the ACTUAL centered coefficient obeys
     q/B=C_(4/3)/C_1, B=A*exp(-pi*(lambda-1)).
   The 1/5 and the full n^4 are essential; this is not central Mellin mass.

   Bounds and remaining bindings:
   * below: actual I_r bounds from the supplied rpow lemma and genuine
     exponential moments; I_r>0 for every r>=1;
   * below: the actual high-mode geometric tail S <= 1/127;
   * C_lambda>=I_lambda follows by positivity of EVERY mode;
     C_1<=U_1+6*pi^(5/4)*S from I_(n^2)<=6*pi^(5/4)/n^2.
   * at lambda=4/3 the surplus L_lambda-3*U_1/4 is
       pi^(-3/4)*(15*pi/64-135/1024).
     After subtracting (3/4)*6*pi^(5/4)/127 and using 3<pi, pi^2<10,
     the remaining scaled surplus exceeds 585/1024-45/127>0.
   This pays q>3B/4 after the ACTUAL HasSum/formula is bound, not by leaving
   q>3B/4 as an assumption. Root still must bind the source interchange and
   shifted-mode identity from positiveMean_weighted_physical_mode_series.
   The numerical probe independently checks this exact mode formula.
-/


set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaGamma.FormCore.CenteredGaussianChargeBoundsDraft

open Real Set MeasureTheory Filter
open scoped Topology BigOperators
open D5.S3.Weil.ZetaGamma.FormCore.RpowFiveQuartersDraft

def meanModeI (r : ℝ) : ℝ :=
  ∫ y : ℝ in Ioi 0,
    (6*Real.pi^(5/4:ℝ)-(Real.pi+y)^(5/4:ℝ))*exp (-(r*y))

def meanModeLower (r : ℝ) : ℝ :=
  5*Real.pi^(5/4:ℝ)/r - (5/4:ℝ)*Real.pi^(1/4:ℝ)/r^2 -
    (5/16:ℝ)*Real.pi^(-3/4:ℝ)/r^3

def meanModeUpper (r : ℝ) : ℝ :=
  5*Real.pi^(5/4:ℝ)/r - (5/4:ℝ)*Real.pi^(1/4:ℝ)/r^2

private theorem exp_moment {r : ℝ} (hr : 0 < r) (k : ℕ) :
    IntegrableOn (fun y : ℝ => y^k*exp (-(r*y))) (Ioi 0) ∧
    (∫ y : ℝ in Ioi 0, y^k*exp (-(r*y))) = (k.factorial:ℝ)/r^(k+1) := by
  constructor
  · simpa only [Real.rpow_one, Real.rpow_natCast, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1:ℝ)) (s := (k:ℝ)) (b := r)
        (by have hk := Nat.cast_nonneg (α := ℝ) k; linarith) (by norm_num) hr)
  · have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := (k:ℝ)+1) (r := r) (by positivity) hr
    have he : (k:ℝ)+1-1 = (k:ℝ) := by ring
    have hp : (1/r)^((k:ℝ)+1) = (1/r)^(k+1) := by
      rw [show (k:ℝ)+1 = ((k+1:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    simp only [he, hp, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
    simpa only [one_div_pow, div_mul_eq_mul_div, one_mul] using h

/-- Genuine integral bounds; the shifted fractional-power integrability is
    paid by the already supplied upper polynomial, not assumed. -/
theorem meanModeI_bounds {r : ℝ} (hr : 0 < r) :
    meanModeLower r ≤ meanModeI r ∧ meanModeI r ≤ meanModeUpper r := by
  let P := Real.pi^(5/4:ℝ)
  let c := (5/4:ℝ)*Real.pi^(1/4:ℝ)
  let d := (5/32:ℝ)*Real.pi^(-3/4:ℝ)
  let E : ℝ → ℝ := fun y => exp (-(r*y))
  let L : ℝ → ℝ := fun y => P+c*y
  let U : ℝ → ℝ := fun y => P+c*y+d*y^2
  let W : ℝ → ℝ := fun y => (Real.pi+y)^(5/4:ℝ)*E y
  obtain ⟨h0, v0⟩ := exp_moment hr 0
  obtain ⟨h1, v1⟩ := exp_moment hr 1
  obtain ⟨h2, v2⟩ := exp_moment hr 2
  simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one] at h0 v0
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, Nat.reduceAdd] at h1 v1
  norm_num only [Nat.factorial, Nat.cast_mul, Nat.cast_one, Nat.reduceAdd] at v2
  have hL : IntegrableOn (fun y => L y*E y) (Ioi 0) := by
    apply IntegrableOn.congr_fun ((h0.const_mul P).add (h1.const_mul c))
      ?_ measurableSet_Ioi
    intro y _
    dsimp only [L, E, Pi.add_apply]
    ring
  have hU : IntegrableOn (fun y => U y*E y) (Ioi 0) := by
    apply IntegrableOn.congr_fun (hL.add (h2.const_mul d)) ?_ measurableSet_Ioi
    intro y _
    dsimp only [U, L, E, Pi.add_apply]
    ring
  have hW : IntegrableOn W (Ioi 0) := by
    apply hU.mono' (by dsimp [W, E]; fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := hy
    have hyp : 0 < Real.pi+y := by linarith [Real.pi_pos]
    have hw0 : 0 ≤ W y := by dsimp [W, E]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hw0]
    exact mul_le_mul_of_nonneg_right
      (pi_add_rpow_five_quarters_bounds hy0.le).2 (exp_nonneg _)
  have hLo : (∫ y : ℝ in Ioi 0, L y*E y) ≤ ∫ y : ℝ in Ioi 0, W y := by
    apply integral_mono_ae hL hW
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := hy
    exact mul_le_mul_of_nonneg_right
      (pi_add_rpow_five_quarters_bounds hy0.le).1 (exp_nonneg _)
  have hHi : (∫ y : ℝ in Ioi 0, W y) ≤ ∫ y : ℝ in Ioi 0, U y*E y := by
    apply integral_mono_ae hW hU
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := hy
    exact mul_le_mul_of_nonneg_right
      (pi_add_rpow_five_quarters_bounds hy0.le).2 (exp_nonneg _)
  have vL : (∫ y : ℝ in Ioi 0, L y*E y) = P/r+c/r^2 := by
    calc
      _ = ∫ y : ℝ in Ioi 0, P*E y+c*(y*E y) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by dsimp [L]; ring
      _ = _ := by
        rw [integral_add (h0.const_mul P) (h1.const_mul c),
          integral_const_mul, integral_const_mul, v0, v1]
        ring
  have vU : (∫ y : ℝ in Ioi 0, U y*E y) = P/r+c/r^2+(2*d)/r^3 := by
    calc
      _ = ∫ y : ℝ in Ioi 0, L y*E y+d*(y^2*E y) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by dsimp [U, L]; ring
      _ = _ := by
        rw [integral_add hL (h2.const_mul d), integral_const_mul, vL, v2]
        ring
  have vI : meanModeI r = 6*P/r-(∫ y : ℝ in Ioi 0, W y) := by
    calc
      _ = ∫ y : ℝ in Ioi 0, (6*P)*E y-W y := by
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by dsimp [meanModeI, W, E, P]; ring
      _ = _ := by
        rw [integral_sub (h0.const_mul (6*P)) hW, integral_const_mul, v0]
        ring
  rw [vL] at hLo
  rw [vU] at hHi
  constructor
  · rw [vI]
    calc
      meanModeLower r = 6*P/r-(P/r+c/r^2+(2*d)/r^3) := by
        dsimp [meanModeLower, P, c, d]
        ring
      _ ≤ _ := sub_le_sub_left hHi (6*P/r)
  · rw [vI]
    calc
      _ ≤ 6*P/r-(P/r+c/r^2) := sub_le_sub_left hLo (6*P/r)
      _ = meanModeUpper r := by dsimp [meanModeUpper, P, c]; ring

private theorem pi_power_splits :
    Real.pi^(5/4:ℝ)=Real.pi^(-3/4:ℝ)*Real.pi^2 ∧
    Real.pi^(1/4:ℝ)=Real.pi^(-3/4:ℝ)*Real.pi := by
  constructor
  · calc
      _ = Real.pi^((-3/4:ℝ)+2) := by norm_num
      _ = _ := by rw [Real.rpow_add Real.pi_pos, Real.rpow_two]
  · calc
      _ = Real.pi^((-3/4:ℝ)+1) := by norm_num
      _ = _ := by rw [Real.rpow_add_one Real.pi_ne_zero]

theorem meanModeI_pos {r : ℝ} (hr : 1 ≤ r) : 0 < meanModeI r := by
  have hr0 : 0 < r := by linarith
  have hz : 3 < Real.pi*r := by nlinarith [Real.pi_gt_three]
  have hp : 0 < 16*(Real.pi*r)^2-4*(Real.pi*r)-1 := by nlinarith
  have hL : meanModeLower r = (5/16:ℝ)*Real.pi^(-3/4:ℝ)/r^3 *
      (16*(Real.pi*r)^2-4*(Real.pi*r)-1) := by
    rw [meanModeLower, pi_power_splits.1, pi_power_splits.2]
    field_simp
    <;> ring
  have hpos : 0 < meanModeLower r := by rw [hL]; positivity
  exact hpos.trans_le (meanModeI_bounds hr0).1

theorem meanModeI_upper_simple {r : ℝ} (hr : 1 ≤ r) :
    meanModeI r ≤ 6*Real.pi^(5/4:ℝ)/r := by
  have hr0 : 0 < r := by linarith
  have hneg : 0 ≤ (5/4:ℝ)*Real.pi^(1/4:ℝ)/r^2 := by positivity
  have hmain : 0 ≤ Real.pi^(5/4:ℝ)/r := by positivity
  have h := (meanModeI_bounds hr0).2
  dsimp [meanModeUpper] at h
  calc
    _ ≤ 5*Real.pi^(5/4:ℝ)/r := h.trans (sub_le_self _ hneg)
    _ ≤ 5*Real.pi^(5/4:ℝ)/r+Real.pi^(5/4:ℝ)/r :=
      le_add_of_nonneg_right hmain
    _ = _ := by ring

def highModeTail (j : ℕ) : ℝ :=
  (((j+2:ℕ):ℝ)^2)*exp (-Real.pi*((((j+2:ℕ):ℝ)^2)-1))

private theorem square_succ_le_four_pow (j : ℕ) :
    (((j+1:ℕ):ℝ)^2) ≤ (4:ℝ)^j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    have hj : 0 ≤ (j:ℝ) := Nat.cast_nonneg j
    norm_num only [Nat.cast_add, Nat.cast_one] at ih ⊢
    have hsq : ((j:ℝ)+1+1)^2 ≤ 4*((j:ℝ)+1)^2 := by nlinarith
    calc
      _ ≤ 4*((j:ℝ)+1)^2 := hsq
      _ ≤ 4*(4:ℝ)^j := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

private theorem four_exp_neg_nine_lt : (4:ℝ)*exp (-9) < 1/128 := by
  have h3 : (8:ℝ) < exp 3 := by
    have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 3)
    norm_num at h
    linarith
  have heq : exp (9:ℝ) = (exp (3:ℝ))^3 := by
    calc
      exp (9:ℝ) = exp (3+3+3:ℝ) := by norm_num
      _ = exp (3:ℝ)*exp (3:ℝ)*exp (3:ℝ) := by rw [exp_add, exp_add]
      _ = _ := by ring
  have h9 : (512:ℝ) < exp 9 := by
    rw [heq]
    have hprod := mul_pos (sub_pos.mpr h3)
      (show 0 < (exp (3:ℝ))^2+8*exp 3+64 by positivity)
    nlinarith
  have hm := mul_lt_mul_of_pos_right h9 (exp_pos (-9))
  have he : exp (9:ℝ)*exp (-9) = 1 := by rw [← exp_add]; norm_num
  rw [he] at hm
  nlinarith

private theorem highModeTail_lt_geometric (j : ℕ) :
    highModeTail j < (1/128:ℝ)^(j+1) := by
  have hj : 0 ≤ (j:ℝ) := Nat.cast_nonneg j
  have hsq : (((j+2:ℕ):ℝ)^2) ≤ (4:ℝ)^(j+1) := by
    simpa only [Nat.add_assoc] using square_succ_le_four_pow (j+1)
  have hq : 3*((j:ℝ)+1) ≤ ((j:ℝ)+2)^2-1 := by nlinarith
  have hq0 : 0 ≤ ((j:ℝ)+2)^2-1 := by nlinarith
  have hphase : 9*((j:ℝ)+1) ≤ Real.pi*(((j:ℝ)+2)^2-1) := by
    have hpi := mul_le_mul_of_nonneg_right Real.pi_gt_three.le hq0
    nlinarith
  have hexp : exp (-Real.pi*((((j+2:ℕ):ℝ)^2)-1)) ≤ (exp (-9:ℝ))^(j+1) := by
    rw [← Real.exp_nat_mul]
    apply exp_le_exp.mpr
    push_cast
    nlinarith
  have hterm : highModeTail j ≤ (4*exp (-9:ℝ))^(j+1) := by
    calc
      _ ≤ (4:ℝ)^(j+1)*(exp (-9:ℝ))^(j+1) :=
        mul_le_mul hsq hexp (exp_nonneg _) (pow_nonneg (by norm_num) _)
      _ = _ := by rw [mul_pow]
  exact hterm.trans_lt (pow_lt_pow_left₀ four_exp_neg_nine_lt
    (by positivity) (Nat.succ_ne_zero j))

/-- The full n>=2 tail, with the natural n=j+2 indexing.  No finite-mode
    truncation or numerical exponential evaluation is assumed. -/
theorem highModeTail_summable_bound : Summable highModeTail ∧
    (∑' j : ℕ, highModeTail j) < (1/127:ℝ) := by
  have hg : Summable (fun j : ℕ => (1/128:ℝ)^(j+1)) := by
    simpa only [pow_succ] using
      (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/128)
        (by norm_num : (1/128:ℝ) < 1)).mul_right (1/128:ℝ)
  have hnonneg (j : ℕ) : 0 ≤ highModeTail j := by dsimp [highModeTail]; positivity
  have hle (j : ℕ) : highModeTail j ≤ (1/128:ℝ)^(j+1) :=
    (highModeTail_lt_geometric j).le
  have hs : Summable highModeTail := Summable.of_nonneg_of_le hnonneg hle hg
  have hval : (∑' j : ℕ, (1/128:ℝ)^(j+1)) = (1/127:ℝ) := by
    simp_rw [pow_succ]
    rw [tsum_mul_right,
      tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/128)
        (by norm_num : (1/128:ℝ) < 1)]
    norm_num
  refine ⟨hs, ?_⟩
  have hlt := Summable.tsum_lt_tsum hle (highModeTail_lt_geometric 0) hs hg
  rwa [hval] at hlt

/-- Exact scalar cap check at pi_upper=22/7, lambda=4/3.  These are the
    coefficients of the SAME original shifted-source numerator minus 19D/4.
    The two endpoint margins exceed 1/100; concavity pays every s between. -/
theorem cap475_scalar_polynomial_certificate
    (s : ℝ) (hs0 : (3/4:ℝ) ≤ s) (hs1 : s ≤ 1) :
    (-561141687/907039232:ℝ)*s^2 + (20266236/12400927:ℝ)*s -
      (12877086436497/14860930777088:ℝ) > 1/100 := by
  have hprod : 0 ≤ (s-3/4)*(1-s) := mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- lambda=4/3 algebra and a strict rational surplus after the entire
    high-mode allowance.  Root binds C_lambda and C_1 to the actual mu series. -/
theorem mode_ratio_gt_three_quarters (C0 Clam : ℝ) (hpos : 0 < C0)
    (h0 : C0 ≤ meanModeUpper 1+6*Real.pi^(5/4:ℝ)/127)
    (hlam : meanModeLower (4/3) ≤ Clam)
    (hpi2 : Real.pi^2 < 10) : (3/4:ℝ) < Clam/C0 := by
  have hsplit := pi_power_splits
  have hm : 0 < Real.pi^(-3/4:ℝ) := Real.rpow_pos_of_pos Real.pi_pos _
  have hsurplus : 0 < meanModeLower (4/3)-(3/4:ℝ)*
      (meanModeUpper 1+6*Real.pi^(5/4:ℝ)/127) := by
    have he : meanModeLower (4/3)-(3/4:ℝ)*
        (meanModeUpper 1+6*Real.pi^(5/4:ℝ)/127) =
      Real.pi^(-3/4:ℝ)*
        ((15/64:ℝ)*Real.pi-135/1024-(9/254:ℝ)*Real.pi^2) := by
      dsimp [meanModeLower, meanModeUpper]
      rw [hsplit.1, hsplit.2]
      ring
    rw [he]
    apply mul_pos hm
    nlinarith [Real.pi_gt_three]
  apply (lt_div_iff₀ hpos).2
  linarith

end D5.S3.Weil.ZetaGamma.FormCore.CenteredGaussianChargeBoundsDraft

/- SOURCE ASSEMBLY, NOT YET COMPILED IN THIS COMBINED MODULE (2026-10-27).
   Exact accepted supplier proofs, copied once for the two actual Gaussian
   charge consumers. No canonical file or declaration is replaced.

   Prefix this before CenteredGaussianChargeUpper.fragment.lean and
   CenteredGaussianActualChargeSeries.fragment.lean, in the SAME module.
   Dependencies already imported by the main Gaussian check:
     D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanCharge
     D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiThetaExcess
     Batteries.Tactic.OpenPrivate
   Add to its IMPORT BLOCK (not after declarations):
     import Mathlib.MeasureTheory.Integral.DominatedConvergence
     import Mathlib.Analysis.Real.Sqrt
     import Mathlib.Analysis.SumIntegralComparisons
     import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
     import Mathlib.Algebra.BigOperators.Intervals
     import Mathlib.NumberTheory.Bernoulli

   Source identity:
   * PositiveMeanKernelCheck.lean: namespace body (original lines 19-157).
   * ActualSuzukiMeanCharge.accepted.lean: positiveMeanNormSource through
     positiveMean_re_positive / axiom prints (original lines 274-832).
   The only added bridges open TRUE existing private declarations from the
   older canonical modules; no nonexistent positivity import is claimed.
-/

namespace D5.S3.Weil.ZetaGamma.FormCore.PositiveMeanKernelFiniteDraft

open scoped BigOperators
open Set MeasureTheory

/-- Direct application of the upstream antitone sum/integral comparison,
with the first exact term retained. This is transient bind-only evidence. -/
theorem reciprocal_sqrt_sum_le (N : ℕ) (hN : 1 ≤ N) :
    (∑ j ∈ Finset.range N, 1 / Real.sqrt ((j + 1 : ℕ) : ℝ)) ≤
      2 * Real.sqrt (N : ℝ) - 1 := by
  have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hanti : AntitoneOn (fun x : ℝ => 1 / Real.sqrt x) (Icc 1 (N : ℝ)) := by
    intro x hx y hy hxy
    exact one_div_le_one_div_of_le
      (Real.sqrt_pos.mpr (by linarith [hx.1])) (Real.sqrt_le_sqrt hxy)
  have hcomp := AntitoneOn.sum_le_integral_Ico
    (f := fun x : ℝ => 1 / Real.sqrt x) hN
    (by simpa only [Nat.cast_one] using hanti)
  simp only [Nat.cast_one] at hcomp
  have hint : (∫ x in (1 : ℝ)..(N : ℝ), 1 / Real.sqrt x) =
      2 * Real.sqrt (N : ℝ) - 2 := by
    calc
      (∫ x in (1 : ℝ)..(N : ℝ), 1 / Real.sqrt x) =
          ∫ x in (1 : ℝ)..(N : ℝ), x ^ (-1 / 2 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hNreal] at hx
        have hx0 : 0 ≤ x := by linarith [hx.1]
        change 1 / Real.sqrt x = x ^ (-1 / 2 : ℝ)
        rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
          Real.rpow_neg hx0, ← Real.sqrt_eq_rpow, one_div]
      _ = 2 * Real.sqrt (N : ℝ) - 2 := by
        rw [integral_rpow
          (r := (-1 / 2 : ℝ)) (Or.inl (by norm_num))]
        simp only [show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num,
          ← Real.sqrt_eq_rpow, Real.sqrt_one]
        ring
  rw [hint] at hcomp
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun j : ℕ => 1 / Real.sqrt ((j + 1 : ℕ) : ℝ)) hN
  norm_num only [Finset.sum_range_one, Nat.zero_add, Nat.cast_one,
    Real.sqrt_one, one_div_one] at hsplit
  linarith

/-- Consumed finite polynomial identity. -/
private theorem six_sum_squares (N : ℕ) :
    6 * (∑ j ∈ Finset.range N, (((j + 1 : ℕ) : ℝ) ^ 2)) =
      (N : ℝ) * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1) := by
  have hshift :
      (∑ j ∈ Finset.range N, (((j + 1 : ℕ) : ℚ) ^ 2)) =
        ∑ k ∈ Finset.Ico 1 (N + 1), (k : ℚ) ^ 2 := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.add_comm 1 j]
  have hfaulhaber := sum_Ico_pow N 2
  norm_num [Finset.sum_range_succ, bernoulli'_zero,
    bernoulli'_one, bernoulli'_two] at hfaulhaber
  have hq : 6 * (∑ j ∈ Finset.range N, (((j + 1 : ℕ) : ℚ) ^ 2)) =
      (N : ℚ) * ((N : ℚ) + 1) * (2 * (N : ℚ) + 1) := by
    rw [hshift]
    nlinarith [hfaulhaber]
  exact_mod_cast hq

/-- The strict endpoint comparison uses the positive square-root increment;
the other comparison is just (sqrt n - 1)^2 >= 0. -/
private theorem endpoint_cost_lt (n : ℝ) (hn : 1 ≤ n) :
    (n + 1) ^ 2 * Real.sqrt (n + 1) * (2 * Real.sqrt n - 1) <
      n * (n + 1) * (2 * n + 1) := by
  let s := Real.sqrt n
  let t := Real.sqrt (n + 1)
  have hn0 : 0 ≤ n := by linarith
  have hs0 : 0 ≤ s := Real.sqrt_nonneg n
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr hn
  have hs : 0 < s := by linarith
  have ht0 : 0 ≤ t := Real.sqrt_nonneg (n + 1)
  have hs2 : s ^ 2 = n := Real.sq_sqrt hn0
  have ht2 : t ^ 2 = n + 1 := Real.sq_sqrt (by linarith)
  have hst : s < t := by
    exact (Real.sqrt_lt_sqrt_iff hn0).mpr (by linarith)
  have htwost : 2 * s * t < 2 * n + 1 := by
    nlinarith [sq_pos_of_pos (sub_pos.mpr hst)]
  have htwo : 2 * s ≤ n + 1 := by
    nlinarith [sq_nonneg (s - 1)]
  have ha : 0 < n + 1 := by linarith
  have hb : 0 < 2 * n + 1 := by linarith
  have hc : 0 < 2 * s - 1 := by linarith
  have hbudget : (n + 1) * (2 * s - 1) ≤ 2 * n * s := by
    nlinarith [htwo]
  have hmul := mul_lt_mul_of_pos_right htwost (mul_pos ha hc)
  have hmajor := mul_le_mul_of_nonneg_left hbudget hb.le
  have hscaled : (2 * s) * ((n + 1) * t * (2 * s - 1)) <
      (2 * s) * (n * (2 * n + 1)) := by
    convert hmul.trans_le hmajor using 1 <;> ring
  have hcore : (n + 1) * t * (2 * s - 1) < n * (2 * n + 1) :=
by
    by_contra hnot
    have hnonneg := mul_nonneg (show 0 ≤ 2 * s by positivity)
      (sub_nonneg.mpr (le_of_not_gt hnot))
    nlinarith only [hscaled, hnonneg]
  change (n + 1) ^ 2 * t * (2 * s - 1) < n * (n + 1) * (2 * n + 1)
  convert mul_lt_mul_of_pos_right hcore ha using 1 <;> ring

/-- Positive exact finite shell coefficient for every nonempty initial segment
and every radius up to the next integer. The theorem retains the original
coefficient 6 and all N>=1; it uses no asymptotic or numerical premise. -/
theorem finite_positive_mean_kernel
    (N : ℕ) (hN : 1 ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hrN : r ≤ (N : ℝ) + 1) :
    0 < 6 * (∑ j ∈ Finset.range N, (((j + 1 : ℕ) : ℝ) ^ 2)) -
      r ^ 2 * Real.sqrt r *
        (∑ j ∈ Finset.range N, 1 / Real.sqrt ((j + 1 : ℕ) : ℝ)) := by
  have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hsum0 :
      0 ≤ ∑ j ∈ Finset.range N, 1 / Real.sqrt ((j + 1 : ℕ) : ℝ) := by
    exact Finset.sum_nonneg fun _ _ => by positivity
  have hrpow : r ^ 2 * Real.sqrt r ≤
      ((N : ℝ) + 1) ^ 2 * Real.sqrt ((N : ℝ) + 1) :=
    mul_le_mul (pow_le_pow_left₀ hr0 hrN 2) (Real.sqrt_le_sqrt hrN)
      (Real.sqrt_nonneg r) (sq_nonneg _)
  have hcost : r ^ 2 * Real.sqrt r *
      (∑ j ∈ Finset.range N, 1 / Real.sqrt ((j + 1 : ℕ) : ℝ)) ≤
        ((N : ℝ) + 1) ^ 2 * Real.sqrt ((N : ℝ) + 1) *
          (2 * Real.sqrt (N : ℝ) - 1) :=
    (mul_le_mul_of_nonneg_right hrpow hsum0).trans
      (mul_le_mul_of_nonneg_left (reciprocal_sqrt_sum_le N hN)
        (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)))
  apply sub_pos.mpr
  calc
    r ^ 2 * Real.sqrt r *
        (∑ j ∈ Finset.range N, 1 / Real.sqrt ((j + 1 : ℕ) : ℝ)) ≤
      ((N : ℝ) + 1) ^ 2 * Real.sqrt ((N : ℝ) + 1) *
        (2 * Real.sqrt (N : ℝ) - 1) := hcost
    _ < (N : ℝ) * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1) :=
      endpoint_cost_lt (N : ℝ) hNreal
    _ = 6 * (∑ j ∈ Finset.range N, (((j + 1 : ℕ) : ℝ) ^ 2)) :=
      (six_sum_squares N).symm

end D5.S3.Weil.ZetaGamma.FormCore.PositiveMeanKernelFiniteDraft

#print axioms D5.S3.Weil.ZetaGamma.FormCore.PositiveMeanKernelFiniteDraft.finite_positive_mean_kernel


namespace D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample

open MeasureTheory Set Filter
open D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail
open scoped Topology ENNReal
open private physicalTerm_aestronglyMeasurable from
  D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiThetaExcess
open private meanCharge_physical_moment_formula from
  D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanCharge

private def positiveMeanNormSource (F : ℝ → ℂ) (x : ℝ) : ℂ := (‖F x‖ : ℂ)

private theorem positiveMeanNormSource_h6
    (F : ℝ → ℂ) (hF : originalPhysicalH6 F) :
    originalPhysicalH6 (positiveMeanNormSource F) := by
  have hmeas : AEStronglyMeasurable (positiveMeanNormSource F)
      (volume.restrict (Ioi Real.pi)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hF.1.aestronglyMeasurable.norm
  refine ⟨?_, ?_⟩
  · apply (memLp_congr_norm hF.1.aestronglyMeasurable hmeas ?_).1 hF.1
    exact Eventually.of_forall fun x => by simp [positiveMeanNormSource]
  · convert hF.2 using 1
    funext x
    simp [positiveMeanNormSource]

private theorem positiveMean_weighted_mode_norm
    (F : ℝ → ℂ) (β : ℝ) (j : ℕ) (x : ℝ) (hx : Real.pi < x) :
    ‖((x ^ β : ℝ) : ℂ) * physicalTerm F j x‖ =
      (((x ^ β : ℝ) : ℂ) * physicalTerm (positiveMeanNormSource F) j x).re := by
  have hx0 : 0 < x := Real.pi_pos.trans hx
  have hn4 : 0 ≤ (((j + 1 : ℕ) : ℝ) ^ (4 : ℕ)) := by positivity
  have hp : (((j + 1 : ℕ) : ℂ) ^ (4 : ℕ)) =
      (((((j + 1 : ℕ) : ℝ) ^ (4 : ℕ)) : ℝ) : ℂ) := by push_cast; rfl
  dsimp only [physicalTerm, positiveMeanNormSource]
  rw [hp]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hx0.le β), abs_of_nonneg hn4,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero]

private theorem positiveMean_weighted_physical_mode_series
    (F : ℝ → ℂ) (hF : originalPhysicalH6 F) (β : ℝ) (hβ : β < 5 / 2) :
    HasSum
      (fun j : ℕ => ∫ x : ℝ in Ioi Real.pi,
        ((x ^ β : ℝ) : ℂ) * physicalTerm F j x)
      (∫ x : ℝ in Ioi Real.pi, ((x ^ β : ℝ) : ℂ) * fullTheta F x) := by
  let G := positiveMeanNormSource F
  have hG : originalPhysicalH6 G := positiveMeanNormSource_h6 F hF
  have hsumF : ∀ᵐ x : ℝ ∂volume.restrict (Ioi Real.pi),
      HasSum (fun j : ℕ => ((x ^ β : ℝ) : ℂ) * physicalTerm F j x)
        (((x ^ β : ℝ) : ℂ) * fullTheta F x) := by
    filter_upwards [actual_h6_physicalTerm_summable_ae F hF] with x hx
    exact hx.hasSum.mul_left ((x ^ β : ℝ) : ℂ)
  have hsumG : ∀ᵐ x : ℝ ∂volume.restrict (Ioi Real.pi),
      HasSum (fun j : ℕ => (((x ^ β : ℝ) : ℂ) * physicalTerm G j x).re)
        ((((x ^ β : ℝ) : ℂ) * fullTheta G x).re) := by
    filter_upwards [actual_h6_physicalTerm_summable_ae G hG] with x hx
    exact Complex.hasSum_re (hx.hasSum.mul_left ((x ^ β : ℝ) : ℂ))
  have hiG : IntegrableOn
      (fun x : ℝ => (((x ^ β : ℝ) : ℂ) * fullTheta G x).re) (Ioi Real.pi) := by
    simpa only [RCLike.re_eq_complex_re] using
      (physical_h6_weighted_l1 (fullTheta G)
        (actual_h6_fullTheta_excess_bound G hG).1 β hβ).re
  apply hasSum_integral_of_dominated_convergence
    (fun j x => (((x ^ β : ℝ) : ℂ) * physicalTerm G j x).re)
  · intro j
    have hw : AEStronglyMeasurable (fun x : ℝ => ((x ^ β : ℝ) : ℂ))
        (volume.restrict (Ioi Real.pi)) := by fun_prop
    exact hw.mul (physicalTerm_aestronglyMeasurable F hF j)
  · intro j
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact le_of_eq (positiveMean_weighted_mode_norm F β j x hx)
  · exact hsumG.mono fun _ hx => hx.summable
  · apply hiG.congr
    exact hsumG.mono fun _ hx => hx.tsum_eq.symm
  · exact hsumF

private theorem positiveMean_mode_scaling_coefficient
    (n β : ℝ) (hn : 0 < n) :
    n ^ (4 : ℕ) / ((n ^ (2 : ℕ)) ^ β * n ^ (2 : ℕ)) =
      n ^ (2 - 2 * β) := by
  have hp : (n ^ (2 : ℕ)) ^ β = n ^ (2 * β) := by
    rw [← Real.rpow_natCast n 2, ← Real.rpow_mul hn.le]
    norm_num
  rw [hp, ← Real.rpow_natCast n 4, ← Real.rpow_natCast n 2,
    ← Real.rpow_add hn, ← Real.rpow_sub hn]
  congr 1
  ring

private theorem positiveMean_weighted_mode_integral
    (F : ℝ → ℂ) (β : ℝ) (j : ℕ) :
    (∫ x : ℝ in Ioi Real.pi, ((x ^ β : ℝ) : ℂ) * physicalTerm F j x) =
      (((((j + 1 : ℕ) : ℝ) ^ (2 - 2 * β)) : ℝ) : ℂ) *
        (∫ y : ℝ in Ioi ((((j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * Real.pi),
          ((y ^ β : ℝ) : ℂ) * F y) := by
  let n : ℝ := (j + 1 : ℕ)
  let h : ℝ → ℂ := fun y => ((y ^ β : ℝ) : ℂ) * F y
  have hn : 0 < n := by dsimp [n]; positivity
  have hn2 : 0 < n ^ (2 : ℕ) := pow_pos hn 2
  have hden : (n ^ (2 : ℕ)) ^ β ≠ 0 := (Real.rpow_pos_of_pos hn2 β).ne'
  have hnc : (((j + 1 : ℕ) : ℂ) ^ (4 : ℕ)) = ((n ^ (4 : ℕ) : ℝ) : ℂ) := by
    dsimp [n]
    push_cast
    rfl
  have heq : (fun x : ℝ => ((x ^ β : ℝ) : ℂ) * physicalTerm F j x) =ᵐ[
      volume.restrict (Ioi Real.pi)]
      (fun x : ℝ => ((n ^ (4 : ℕ) / (n ^ (2 : ℕ)) ^ β : ℝ) : ℂ) *
        h (n ^ (2 : ℕ) * x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := Real.pi_pos.trans hx
    dsimp only [physicalTerm, h]
    rw [hnc, Real.mul_rpow hn2.le hx0.le]
    change ((x ^ β : ℝ) : ℂ) *
        (((n ^ (4 : ℕ) : ℝ) : ℂ) * F (n ^ (2 : ℕ) * x)) = _
    push_cast
    field_simp [hden]
    <;> ring
  calc
    (∫ x : ℝ in Ioi Real.pi, ((x ^ β : ℝ) : ℂ) * physicalTerm F j x) =
        ((n ^ (4 : ℕ) / (n ^ (2 : ℕ)) ^ β : ℝ) : ℂ) *
          (∫ x : ℝ in Ioi Real.pi, h (n ^ (2 : ℕ) * x)) := by
      rw [integral_congr_ae heq, integral_const_mul]
    _ = ((n ^ (4 : ℕ) / (n ^ (2 : ℕ)) ^ β : ℝ) : ℂ) *
        (((n ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) *
          (∫ y : ℝ in Ioi (n ^ (2 : ℕ) * Real.pi), h y) := by
      rw [integral_comp_mul_left_Ioi h Real.pi hn2]
      simp only [Complex.real_smul]
      ring
    _ = _ := by
      rw [← Complex.ofReal_mul]
      have hc : n ^ (4 : ℕ) / (n ^ (2 : ℕ)) ^ β * (n ^ (2 : ℕ))⁻¹ =
          n ^ (2 - 2 * β) := by
        rw [← div_eq_mul_inv, div_div]
        exact positiveMean_mode_scaling_coefficient n β hn
      rw [hc]

private theorem positiveMean_weighted_tail_series
    (F : ℝ → ℂ) (hF : originalPhysicalH6 F) (β : ℝ) (hβ : β < 5 / 2) :
    HasSum
      (fun j : ℕ => (((((j + 1 : ℕ) : ℝ) ^ (2 - 2 * β)) : ℝ) : ℂ) *
        (∫ y : ℝ in Ioi ((((j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * Real.pi),
          ((y ^ β : ℝ) : ℂ) * F y))
      (∫ x : ℝ in Ioi Real.pi, ((x ^ β : ℝ) : ℂ) * fullTheta F x) := by
  convert positiveMean_weighted_physical_mode_series F hF β hβ using 1
  funext j
  exact (positiveMean_weighted_mode_integral F β j).symm

private theorem positiveMean_mu_tail_series
    (F : ℝ → ℂ) (hF : originalPhysicalH6 F) :
    HasSum
      (fun j : ℕ =>
        (6 / 5 : ℂ) * ((Real.pi ^ (5 / 4 : ℝ) : ℝ) : ℂ) *
          (((((j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) *
            (∫ y : ℝ in Ioi ((((j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * Real.pi), F y) -
        (1 / 5 : ℂ) *
          (((((j + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ) *
            (∫ y : ℝ in Ioi ((((j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * Real.pi),
              ((y ^ (5 / 4 : ℝ) : ℝ) : ℂ) * F y))
      (actualSuzukiMeanCharge F) := by
  have h0 : HasSum
      (fun j : ℕ => (((((j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) *
        (∫ y : ℝ in Ioi ((((j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * Real.pi), F y))
      (∫ x : ℝ in Ioi Real.pi, fullTheta F x) := by
    simpa only [mul_zero, sub_zero, Real.rpow_two, Real.rpow_zero,
      Complex.ofReal_one, one_mul] using
        positiveMean_weighted_tail_series F hF 0 (by norm_num)
  have h5 : HasSum
      (fun j : ℕ => (((((j + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ) *
        (∫ y : ℝ in Ioi ((((j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * Real.pi),
          ((y ^ (5 / 4 : ℝ) : ℝ) : ℂ) * F y))
      (∫ x : ℝ in Ioi Real.pi,
        ((x ^ (5 / 4 : ℝ) : ℝ) : ℂ) * fullTheta F x) := by
    convert positiveMean_weighted_tail_series F hF (5 / 4) (by norm_num) using 1
    norm_num
  have hs :=
    (h0.mul_left ((6 / 5 : ℂ) * ((Real.pi ^ (5 / 4 : ℝ) : ℝ) : ℂ))).sub
      (h5.mul_left (1 / 5 : ℂ))
  convert hs using 1
  · funext j
    ring
  · rw [meanCharge_physical_moment_formula F hF]


private theorem positiveMean_integrable_series
    (f : ℕ → ℝ → ℂ)
    (hf : ∀ j, Integrable (f j) (volume.restrict (Ioi Real.pi)))
    (hs : Summable (fun j => ∫ y : ℝ in Ioi Real.pi, ‖f j y‖)) :
    Integrable (fun y => ∑' j, f j y) (volume.restrict (Ioi Real.pi)) ∧
      (∀ᵐ y : ℝ ∂volume.restrict (Ioi Real.pi), Summable (fun j => f j y)) := by
  let fi (j : ℕ) : Lp ℂ 1 (volume.restrict (Ioi Real.pi)) := (hf j).toL1 (f j)
  have hnorm (j : ℕ) : ‖fi j‖ = ∫ y : ℝ in Ioi Real.pi, ‖f j y‖ := by
    change ‖(hf j).toL1 (f j)‖ = _
    rw [Integrable.norm_toL1]
    simp only [edist_zero_right]
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hf j),
      ENNReal.toReal_ofReal (integral_nonneg (fun y => norm_nonneg (f j y)))]
  have hsnorm : Summable (fun j => ‖fi j‖) := by simpa only [hnorm] using hs
  have he : (∑' j, ‖fi j‖ₑ) ≠ ∞ := tsum_enorm_ne_top_iff_summable_norm.2 hsnorm
  let U : Lp ℂ 1 (volume.restrict (Ioi Real.pi)) := ∑' j, fi j
  have hterms : ∀ᵐ y : ℝ ∂volume.restrict (Ioi Real.pi), ∀ j, fi j y = f j y :=
    ae_all_iff.2 fun j => (hf j).coeFn_toL1
  have hbridge : (fun y => U y) =ᵐ[volume.restrict (Ioi Real.pi)]
      (fun y => ∑' j, f j y) := by
    filter_upwards [Lp.coeFn_tsum he, hterms] with y hy hyt
    exact hy.trans (tsum_congr hyt)
  have hU : MemLp (fun y => ∑' j, f j y) 1 (volume.restrict (Ioi Real.pi)) :=
    (memLp_congr_ae hbridge).1 (Lp.memLp U)
  refine ⟨memLp_one_iff_integrable.1 hU, ?_⟩
  filter_upwards [Lp.hasSum_coeFn_tsum he, hterms] with y hy hyt
  exact hy.summable.congr hyt

private def positiveMeanTailMode (F : ℝ → ℂ) (β : ℝ) (j : ℕ) (y : ℝ) : ℂ :=
  (Ioi ((((j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * Real.pi)).indicator
    (fun z => (((((j + 1 : ℕ) : ℝ) ^ (2 - 2 * β)) : ℝ) : ℂ) *
      (((z ^ β : ℝ) : ℂ) * F z)) y

private theorem positiveMean_mode_endpoint (j : ℕ) :
    Real.pi ≤ ((((j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * Real.pi) := by
  have hn : 1 ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (one_le_pow₀ (n := 2) hn) Real.pi_pos.le

private theorem positiveMeanTailMode_integrable
    (F : ℝ → ℂ) (hF : originalPhysicalH6 F) (β : ℝ) (hβ : β < 5 / 2) (j : ℕ) :
    Integrable (positiveMeanTailMode F β j) (volume.restrict (Ioi Real.pi)) := by
  have hi := (physical_h6_weighted_l1 F hF β hβ).mono_set
    (Ioi_subset_Ioi (positiveMean_mode_endpoint j))
  have hc : IntegrableOn
      (fun x : ℝ => (((((j + 1 : ℕ) : ℝ) ^ (2 - 2 * β)) : ℝ) : ℂ) *
        (((x ^ β : ℝ) : ℂ) * F x))
      (Ioi ((((j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * Real.pi)) :=
    hi.const_mul (((((j + 1 : ℕ) : ℝ) ^ (2 - 2 * β)) : ℝ) : ℂ)
  exact (IntegrableOn.integrable_indicator hc measurableSet_Ioi).restrict

private theorem positiveMeanTailMode_integral
    (F : ℝ → ℂ) (β : ℝ) (j : ℕ) :
    (∫ y : ℝ in Ioi Real.pi, positiveMeanTailMode F β j y) =
      (((((j + 1 : ℕ) : ℝ) ^ (2 - 2 * β)) : ℝ) : ℂ) *
        (∫ y : ℝ in Ioi ((((j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * Real.pi),
          ((y ^ β : ℝ) : ℂ) * F y) := by
  unfold positiveMeanTailMode
  rw [integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict_of_subset (Ioi_subset_Ioi (positiveMean_mode_endpoint j)),
    integral_const_mul]

private theorem positiveMeanTailMode_norm
    (F : ℝ → ℂ) (β : ℝ) (j : ℕ) (y : ℝ) :
    ‖positiveMeanTailMode F β j y‖ =
      (positiveMeanTailMode (positiveMeanNormSource F) β j y).re := by
  have hn : 0 < ((j + 1 : ℕ) : ℝ) := by positivity
  have hc : 0 < (((j + 1 : ℕ) : ℝ) ^ (2 - 2 * β)) := Real.rpow_pos_of_pos hn _
  by_cases hy : y ∈ Ioi ((((j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * Real.pi)
  · have hy0 : 0 < y := (Real.pi_pos.trans_le (positiveMean_mode_endpoint j)).trans hy
    simp only [positiveMeanTailMode, Set.indicator_of_mem hy, positiveMeanNormSource,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc,
      abs_of_nonneg (Real.rpow_nonneg hy0.le β), Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
  · simp only [positiveMeanTailMode, Set.indicator_of_notMem hy, norm_zero, Complex.zero_re]

private theorem positiveMeanTailMode_norm_integrals_summable
    (F : ℝ → ℂ) (hF : originalPhysicalH6 F) (β : ℝ) (hβ : β < 5 / 2) :
    Summable (fun j => ∫ y : ℝ in Ioi Real.pi, ‖positiveMeanTailMode F β j y‖) := by
  let G := positiveMeanNormSource F
  have hG : originalPhysicalH6 G := positiveMeanNormSource_h6 F hF
  have hnorm (j : ℕ) :
      (∫ y : ℝ in Ioi Real.pi, ‖positiveMeanTailMode F β j y‖) =
      (((((((j + 1 : ℕ) : ℝ) ^ (2 - 2 * β)) : ℝ) : ℂ) *
        (∫ y : ℝ in Ioi ((((j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * Real.pi),
          ((y ^ β : ℝ) : ℂ) * G y)).re) := by
    calc
      (∫ y : ℝ in Ioi Real.pi, ‖positiveMeanTailMode F β j y‖) =
          ∫ y : ℝ in Ioi Real.pi, (positiveMeanTailMode G β j y).re := by
        apply integral_congr_ae
        exact Eventually.of_forall fun y => positiveMeanTailMode_norm F β j y
      _ = (∫ y : ℝ in Ioi Real.pi, positiveMeanTailMode G β j y).re := by
        simpa only [RCLike.re_eq_complex_re] using
          integral_re (positiveMeanTailMode_integrable G hG β hβ j)
      _ = _ := congrArg Complex.re (positiveMeanTailMode_integral G β j)
  convert (Complex.hasSum_re (positiveMean_weighted_tail_series G hG β hβ)).summable using 1
  funext j
  exact hnorm j

private theorem positiveMean_source_moment_representation
    (F : ℝ → ℂ) (hF : originalPhysicalH6 F) (β : ℝ) (hβ : β < 5 / 2) :
    Integrable (fun y => ∑' j, positiveMeanTailMode F β j y)
      (volume.restrict (Ioi Real.pi)) ∧
    (∀ᵐ y : ℝ ∂volume.restrict (Ioi Real.pi),
      Summable (fun j => positiveMeanTailMode F β j y)) ∧
    (∫ y : ℝ in Ioi Real.pi, ∑' j, positiveMeanTailMode F β j y) =
      (∫ x : ℝ in Ioi Real.pi, ((x ^ β : ℝ) : ℂ) * fullTheta F x) := by
  have hi := positiveMeanTailMode_integrable F hF β hβ
  have hs := positiveMeanTailMode_norm_integrals_summable F hF β hβ
  obtain ⟨hI, hS⟩ := positiveMean_integrable_series (positiveMeanTailMode F β) hi hs
  refine ⟨hI, hS, ?_⟩
  have hsI := hasSum_integral_of_summable_integral_norm hi hs
  have hsT : HasSum
      (fun j => ∫ y : ℝ in Ioi Real.pi, positiveMeanTailMode F β j y)
      (∫ x : ℝ in Ioi Real.pi, ((x ^ β : ℝ) : ℂ) * fullTheta F x) := by
    convert positiveMean_weighted_tail_series F hF β hβ using 1
    funext j
    exact positiveMeanTailMode_integral F β j
  exact hsI.unique hsT

private def positiveMeanPhysicalKernelTerm (j : ℕ) (y : ℝ) : ℝ :=
  if Real.pi * (((j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) < y then
    6 * Real.pi ^ (5 / 4 : ℝ) * (((j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) -
      y ^ (5 / 4 : ℝ) / Real.sqrt ((j + 1 : ℕ) : ℝ)
  else 0

private def positiveMeanPhysicalKernel (y : ℝ) : ℝ :=
  ∑' j : ℕ, positiveMeanPhysicalKernelTerm j y

private theorem positiveMeanPhysicalKernelTerm_summable (y : ℝ) :
    Summable (fun j : ℕ => positiveMeanPhysicalKernelTerm j y) := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt y
  apply summable_of_ne_finset_zero (s := Finset.range N)
  intro j hj
  have hNj : N ≤ j := Nat.le_of_not_lt (fun h => hj (Finset.mem_range.mpr h))
  have hNjR : (N : ℝ) ≤ (j : ℝ) := by exact_mod_cast hNj
  have hn1 : 1 ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
  have hyn : y < ((j + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hn2 : ((j + 1 : ℕ) : ℝ) ≤ (((j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
    nlinarith
  have hpi : 1 ≤ Real.pi := le_of_lt (by linarith [Real.pi_gt_three])
  have hnp : ((j + 1 : ℕ) : ℝ) ≤
      Real.pi * (((j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) :=
    hn2.trans (le_mul_of_one_le_left (by positivity) hpi)
  exact if_neg (not_lt_of_ge (hyn.le.trans hnp))

private theorem positiveMeanPhysicalKernelTerm_mul
    (F : ℝ → ℂ) (j : ℕ) (y : ℝ) :
    (positiveMeanPhysicalKernelTerm j y : ℂ) * F y =
      ((6 * Real.pi ^ (5 / 4 : ℝ) : ℝ) : ℂ) * positiveMeanTailMode F 0 j y -
        positiveMeanTailMode F (5 / 4) j y := by
  let n : ℝ := (j + 1 : ℕ)
  have hn : 0 < n := by dsimp [n]; positivity
  have hh : n ^ (-(1 / 2 : ℝ)) = (Real.sqrt n)⁻¹ := by
    rw [Real.rpow_neg hn.le, Real.sqrt_eq_rpow]
  have hexp : (2 - 2 * (5 / 4 : ℝ)) = -(1 / 2 : ℝ) := by norm_num
  by_cases hy : n ^ (2 : ℕ) * Real.pi < y
  · have hy' : Real.pi * n ^ (2 : ℕ) < y := by simpa only [mul_comm] using hy
    have hymem : y ∈ Ioi (n ^ (2 : ℕ) * Real.pi) := hy
    dsimp only [positiveMeanPhysicalKernelTerm, positiveMeanTailMode]
    change ((if Real.pi * n ^ (2 : ℕ) < y then
        6 * Real.pi ^ (5 / 4 : ℝ) * n ^ (2 : ℕ) -
          y ^ (5 / 4 : ℝ) / Real.sqrt n else 0 : ℝ) : ℂ) * F y = _
    rw [if_pos hy', Set.indicator_of_mem hymem, Set.indicator_of_mem hymem]
    simp only [mul_zero, sub_zero, Real.rpow_zero, Complex.ofReal_one, one_mul,
      Real.rpow_two, hexp]
    change _ = ((6 * Real.pi ^ (5 / 4 : ℝ) : ℝ) : ℂ) *
        (((n ^ (2 : ℕ) : ℝ) : ℂ) * F y) -
      ((n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (((y ^ (5 / 4 : ℝ) : ℝ) : ℂ) * F y)
    rw [hh]
    push_cast
    ring
  · have hy' : ¬ Real.pi * n ^ (2 : ℕ) < y := by simpa only [mul_comm] using hy
    have hymem : y ∉ Ioi (n ^ (2 : ℕ) * Real.pi) := hy
    dsimp only [n] at hy' hymem
    simp only [Nat.cast_add, Nat.cast_one] at hy' hymem
    simp [positiveMeanPhysicalKernelTerm, positiveMeanTailMode, hy', hymem]

private theorem positiveMeanPhysicalKernel_mul
    (F : ℝ → ℂ) (y : ℝ) :
    (positiveMeanPhysicalKernel y : ℂ) * F y =
      ∑' j : ℕ,
        (((6 * Real.pi ^ (5 / 4 : ℝ) : ℝ) : ℂ) * positiveMeanTailMode F 0 j y -
          positiveMeanTailMode F (5 / 4) j y) := by
  unfold positiveMeanPhysicalKernel
  rw [Complex.ofReal_tsum, ← tsum_mul_right]
  apply tsum_congr
  intro j
  exact positiveMeanPhysicalKernelTerm_mul F j y

-- Exact physical source-kernel application, with all original H6 domains paid.
private theorem positiveMean_physical_kernel_formula
    (F : ℝ → ℂ) (hF : originalPhysicalH6 F) :
    (∀ y : ℝ, Summable (fun j : ℕ => positiveMeanPhysicalKernelTerm j y)) ∧
    Integrable (fun y => (positiveMeanPhysicalKernel y : ℂ) * F y)
      (volume.restrict (Ioi Real.pi)) ∧
    (5 : ℂ) * actualSuzukiMeanCharge F =
      ∫ y : ℝ in Ioi Real.pi, (positiveMeanPhysicalKernel y : ℂ) * F y := by
  obtain ⟨hi0, hs0, hI0⟩ := positiveMean_source_moment_representation F hF 0 (by norm_num)
  obtain ⟨hi5, hs5, hI5⟩ := positiveMean_source_moment_representation F hF (5 / 4) (by norm_num)
  let c : ℂ := ((6 * Real.pi ^ (5 / 4 : ℝ) : ℝ) : ℂ)
  have heq : (fun y => (positiveMeanPhysicalKernel y : ℂ) * F y) =ᵐ[
      volume.restrict (Ioi Real.pi)]
      (fun y => c * (∑' j, positiveMeanTailMode F 0 j y) -
        (∑' j, positiveMeanTailMode F (5 / 4) j y)) := by
    filter_upwards [hs0, hs5] with y hy0 hy5
    rw [positiveMeanPhysicalKernel_mul, (hy0.mul_left c).tsum_sub hy5, tsum_mul_left]
  have hi := (hi0.const_mul c).sub hi5
  refine ⟨positiveMeanPhysicalKernelTerm_summable, hi.congr heq.symm, ?_⟩
  calc
    (5 : ℂ) * actualSuzukiMeanCharge F =
        c * (∫ x : ℝ in Ioi Real.pi, fullTheta F x) -
          (∫ x : ℝ in Ioi Real.pi,
            ((x ^ (5 / 4 : ℝ) : ℝ) : ℂ) * fullTheta F x) := by
      rw [meanCharge_physical_moment_formula F hF]
      dsimp [c]
      push_cast
      ring
    _ = c * (∫ y : ℝ in Ioi Real.pi, ∑' j, positiveMeanTailMode F 0 j y) -
        (∫ y : ℝ in Ioi Real.pi, ∑' j, positiveMeanTailMode F (5 / 4) j y) := by
      have hI0' : (∫ y : ℝ in Ioi Real.pi, ∑' j, positiveMeanTailMode F 0 j y) =
          (∫ x : ℝ in Ioi Real.pi, fullTheta F x) := by
        simpa only [Real.rpow_zero, Complex.ofReal_one, one_mul] using hI0
      rw [hI0', hI5]
    _ = ∫ y : ℝ in Ioi Real.pi,
        c * (∑' j, positiveMeanTailMode F 0 j y) -
          (∑' j, positiveMeanTailMode F (5 / 4) j y) := by
      rw [integral_sub (hi0.const_mul c) hi5, integral_const_mul]
    _ = _ := integral_congr_ae heq.symm

#print axioms positiveMean_source_moment_representation
#print axioms positiveMeanPhysicalKernelTerm_summable

#print axioms positiveMean_physical_kernel_formula

/-
Uncompiled transient exact-application fragment, 2026-10-26.
Append after PositivePhysicalMean.fragment.lean, inside the same
ActualSuzukiDomainCounterexample namespace. The private literal kernel
definitions in that fragment must be in scope, together with the finite
kernel exact-check declaration. No canonical D5/Reg retention is intended.
-/

private theorem positiveMeanPhysicalKernel_pos
    (y : ℝ) (hy : Real.pi < y) : 0 < positiveMeanPhysicalKernel y := by
  classical
  let r : ℝ := Real.sqrt (y / Real.pi)
  let N : ℕ := Nat.ceil r - 1
  have hy0 : 0 < y := Real.pi_pos.trans hy
  have hq0 : 0 ≤ y / Real.pi := (div_pos hy0 Real.pi_pos).le
  have hq1 : 1 < y / Real.pi :=
    (lt_div_iff₀ Real.pi_pos).mpr (by simpa only [one_mul] using hy)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr1 : 1 < r := by
    simpa only [r, Real.sqrt_one] using
      (Real.sqrt_lt_sqrt_iff (show (0 : ℝ) ≤ 1 by norm_num)).mpr hq1
  have hrsq : r ^ (2 : ℕ) = y / Real.pi := Real.sq_sqrt hq0
  have hceil : 1 < Nat.ceil r :=
    Nat.lt_ceil.mpr (by simpa only [Nat.cast_one] using hr1)
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hNplus : N + 1 = Nat.ceil r := by
    dsimp [N]
    exact Nat.sub_add_cancel (by omega)
  have hNcast : (N : ℝ) + 1 = (Nat.ceil r : ℝ) := by
    exact_mod_cast hNplus
  have hrN : r ≤ (N : ℝ) + 1 :=
    (Nat.le_ceil r).trans_eq hNcast.symm

  -- Ceil r - 1 counts the STRICTLY active positive integers. In particular,
  -- an integral r belongs to the shell immediately to its left, so its
  -- endpoint mode is correctly omitted.
  have hactive (j : ℕ) :
      Real.pi * (((j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) < y ↔ j < N := by
    calc
      Real.pi * (((j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) < y ↔
          (((j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) < y / Real.pi := by
        rw [lt_div_iff₀ Real.pi_pos]
        rw [mul_comm ((((j + 1 : ℕ) : ℝ) ^ (2 : ℕ))) Real.pi]
      _ ↔ (((j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) < r ^ (2 : ℕ) := by rw [hrsq]
      _ ↔ ((j + 1 : ℕ) : ℝ) < r :=
        sq_lt_sq₀ (by positivity) hr0
      _ ↔ j < N := by
        rw [← Nat.lt_ceil, ← hNplus]
        omega

  have hfinite : positiveMeanPhysicalKernel y =
      ∑ j ∈ Finset.range N,
        (6 * Real.pi ^ (5 / 4 : ℝ) * (((j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) -
          y ^ (5 / 4 : ℝ) / Real.sqrt ((j + 1 : ℕ) : ℝ)) := by
    unfold positiveMeanPhysicalKernel
    calc
      (∑' j : ℕ, positiveMeanPhysicalKernelTerm j y) =
          ∑ j ∈ Finset.range N, positiveMeanPhysicalKernelTerm j y := by
        apply tsum_eq_sum
        intro j hj
        exact if_neg (fun h => hj (Finset.mem_range.mpr ((hactive j).mp h)))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        exact if_pos ((hactive j).mpr (Finset.mem_range.mp hj))

  have hrpos : 0 < r := lt_trans zero_lt_one hr1
  have hrpow : (r ^ (2 : ℕ)) ^ (5 / 4 : ℝ) =
      r ^ (2 : ℕ) * Real.sqrt r := by
    calc
      (r ^ (2 : ℕ)) ^ (5 / 4 : ℝ) = r ^ (5 / 2 : ℝ) := by
        rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr0]
        norm_num
      _ = r ^ ((2 : ℝ) + 1 / 2) := by norm_num
      _ = r ^ (2 : ℝ) * r ^ (1 / 2 : ℝ) := Real.rpow_add hrpos _ _
      _ = r ^ (2 : ℕ) * Real.sqrt r := by
        rw [Real.rpow_two, ← Real.sqrt_eq_rpow]
  have hyrepr : y = Real.pi * r ^ (2 : ℕ) := by
    have h := (eq_div_iff Real.pi_ne_zero).mp hrsq
    nlinarith
  have hscale : y ^ (5 / 4 : ℝ) =
      Real.pi ^ (5 / 4 : ℝ) * (r ^ (2 : ℕ) * Real.sqrt r) := by
    rw [hyrepr, Real.mul_rpow Real.pi_pos.le (sq_nonneg r), hrpow]

  have hnormalized : positiveMeanPhysicalKernel y =
      Real.pi ^ (5 / 4 : ℝ) *
        (6 * (∑ j ∈ Finset.range N, (((j + 1 : ℕ) : ℝ) ^ (2 : ℕ))) -
          r ^ (2 : ℕ) * Real.sqrt r *
            (∑ j ∈ Finset.range N, 1 / Real.sqrt ((j + 1 : ℕ) : ℝ))) := by
    rw [hfinite, hscale]
    simp only [div_eq_mul_inv, one_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [hnormalized]
  exact mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) 
    (D5.S3.Weil.ZetaGamma.FormCore.PositiveMeanKernelFiniteDraft.finite_positive_mean_kernel
      N hN r hr0 hrN)

-- Literal pointwise sign, including exact square-shell endpoints, checked
-- only through the displayed proof once this transient module compiles.
example : ∀ y : ℝ, Real.pi < y → 0 < positiveMeanPhysicalKernel y :=
  positiveMeanPhysicalKernel_pos

-- This uses the proved original-H6 formula, rather than assuming the desired
-- integral representation. Only positivity of Re F is needed; Im F can be
-- arbitrary. Positive real source mass excludes the zero source a.e.
private theorem positiveMean_re_positive
    (F : ℝ → ℂ) (hF : originalPhysicalH6 F)
    (hRe : ∀ᵐ y : ℝ ∂volume.restrict (Ioi Real.pi), 0 ≤ (F y).re)
    (hmass : 0 < ∫ y : ℝ in Ioi Real.pi, (F y).re) :
    0 < (actualSuzukiMeanCharge F).re := by
  obtain ⟨_, hprod, hformula⟩ := positiveMean_physical_kernel_formula F hF
  have hprodRe : Integrable
      (fun y : ℝ => positiveMeanPhysicalKernel y * (F y).re)
        (volume.restrict (Ioi Real.pi)) := by
    simpa only [RCLike.re_eq_complex_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hprod.re
  have hprod0 : ∀ᵐ y : ℝ ∂volume.restrict (Ioi Real.pi),
      0 ≤ positiveMeanPhysicalKernel y * (F y).re := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi, hRe] with y hy hFy
    exact mul_nonneg (positiveMeanPhysicalKernel_pos y hy).le hFy
  have hIpos : 0 < ∫ y : ℝ in Ioi Real.pi,
      positiveMeanPhysicalKernel y * (F y).re := by
    have hI0 := integral_nonneg_of_ae hprod0
    by_contra hnpos
    have hIeq : (∫ y : ℝ in Ioi Real.pi,
        positiveMeanPhysicalKernel y * (F y).re) = 0 :=
      le_antisymm (le_of_not_gt hnpos) hI0
    have hprodZero :=
      (integral_eq_zero_iff_of_nonneg_ae hprod0 hprodRe).mp hIeq
    have hFZero : (fun y : ℝ => (F y).re) =ᵐ[volume.restrict (Ioi Real.pi)] 0 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi, hprodZero] with y hy hzero
      change positiveMeanPhysicalKernel y * (F y).re = 0 at hzero
      exact (mul_eq_zero.mp hzero).resolve_left
        (positiveMeanPhysicalKernel_pos y hy).ne'
    have hmassZero : (∫ y : ℝ in Ioi Real.pi, (F y).re) = 0 := by
      simpa only [Pi.zero_apply, integral_zero] using (integral_congr_ae hFZero)
    linarith
  have hformulaRe : (5 : ℝ) * (actualSuzukiMeanCharge F).re =
      ∫ y : ℝ in Ioi Real.pi, positiveMeanPhysicalKernel y * (F y).re := by
    calc
      (5 : ℝ) * (actualSuzukiMeanCharge F).re =
          (∫ y : ℝ in Ioi Real.pi, (positiveMeanPhysicalKernel y : ℂ) * F y).re := by
        simpa [Complex.mul_re] using congrArg Complex.re hformula
      _ = ∫ y : ℝ in Ioi Real.pi, positiveMeanPhysicalKernel y * (F y).re := by
        simpa only [RCLike.re_eq_complex_re, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
            (integral_re hprod).symm
  linarith

#print axioms positiveMeanPhysicalKernel_pos
#print axioms positiveMean_re_positive


end D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample

/- SOURCE DRAFT, NOT COMPILED (2026-10-27).
   Append in the SAME MODULE after the actual Gaussian/H6/centering fragments.

   Required shared source prefix (concatenate ONCE in this SAME module):
   E/ActualPositiveMeanSupplier.fragment.lean. This copies the complete
   accepted finite-kernel and actual physical mean suppliers, opening only
   real existing canonical private helpers. Stock dev's older MeanCharge
   module does NOT yet supply the positivity extension by import alone.

   Consumer: the centered-Gaussian original physical-cap calculation needs
   the actual quotient q to be real and its normalized ratio qR/B strictly
   below one. The separate lower-bound/HasSum obligation is not duplicated.
-/

namespace D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft

open Real Set MeasureTheory Filter
open scoped Topology ENNReal
open D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample

private theorem actual_mean_re_pos_of_source_strictly_positive
    (F : ℝ → ℂ) (hF : originalPhysicalH6 F)
    (hpos : ∀ x : ℝ, Real.pi < x → 0 < (F x).re) :
    0 < (actualSuzukiMeanCharge F).re := by
  have hi : IntegrableOn F (Ioi Real.pi) := by
    simpa only [Real.rpow_zero, Complex.ofReal_one, one_mul] using
      physical_h6_weighted_l1 F hF 0 (by norm_num)
  have hiR : IntegrableOn (fun x : ℝ => (F x).re) (Ioi Real.pi) := by
    simpa only [RCLike.re_eq_complex_re] using hi.re
  have hnn : ∀ᵐ x : ℝ ∂volume.restrict (Ioi Real.pi), 0 ≤ (F x).re := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (hpos x hx).le
  have hs : Function.support (fun x : ℝ => (F x).re) ∩ Ioi Real.pi = Ioi Real.pi := by
    ext x
    constructor
    · intro hx
      exact hx.2
    · intro hx
      exact ⟨(hpos x hx).ne', hx⟩
  have hmass : 0 < ∫ x : ℝ in Ioi Real.pi, (F x).re := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae hnn hiR).2
    rw [hs]
    simp
  exact positiveMean_re_positive F hF hnn hmass

private theorem literalGaussian_charge_im_zero {a : ℝ} (ha : 0 ≤ a) :
    (actualSuzukiMeanCharge (literalGaussian a)).im = 0 := by
  apply actual_h6_suzuki_mean_charge_im_eq_zero_of_profile_ae _
    (literalGaussian_original_h6 a)
  filter_upwards with t
  rw [literalGaussian_actualProfile ha]
  dsimp only
  split_ifs <;> simp

private theorem literalGaussian_charge_re_pos (a : ℝ) :
    0 < (actualSuzukiMeanCharge (literalGaussian a)).re := by
  apply actual_mean_re_pos_of_source_strictly_positive _ (literalGaussian_original_h6 a)
  intro x _
  simpa only [literalGaussian, Complex.ofReal_re] using
    exp_pos ((9/2:ℝ)*a-exp (2*a)*x)

private theorem literalGaussian_charge_eq_real {a : ℝ} (ha : 0 ≤ a) :
    actualSuzukiMeanCharge (literalGaussian a) =
      ((actualSuzukiMeanCharge (literalGaussian a)).re:ℂ) := by
  apply Complex.ext
  · simp only [Complex.ofReal_re]
  · simpa only [Complex.ofReal_im] using literalGaussian_charge_im_zero ha

private theorem centeredGaussianCharge_eq_real_quotient {a : ℝ} (ha : 0 ≤ a) :
    centeredGaussianCharge a =
      (((actualSuzukiMeanCharge (literalGaussian a)).re /
        (actualSuzukiMeanCharge (literalGaussian 0)).re:ℝ):ℂ) := by
  calc
    centeredGaussianCharge a =
        ((actualSuzukiMeanCharge (literalGaussian a)).re:ℂ) /
          ((actualSuzukiMeanCharge (literalGaussian 0)).re:ℂ) :=
      congrArg₂ (fun z w : ℂ => z/w) (literalGaussian_charge_eq_real ha)
        (literalGaussian_charge_eq_real (by norm_num : (0:ℝ)≤0))
    _ = _ := (Complex.ofReal_div _ _).symm

/- For every positive shift, B*g0-ga is pointwise strictly positive on the
   ORIGINAL physical half-line x>pi. B is its exact endpoint ratio; no
   numerical quadrature, surrogate mean, or bound on a spectral measure is
   used to prove the strict comparison. -/
private theorem centeredGaussianCharge_strict_upper_general {a : ℝ} (ha : 0 < a) :
    let A : ℝ := exp ((9/2:ℝ)*a)
    let lam : ℝ := exp (2*a)
    let B : ℝ := A*exp (-(lam-1)*Real.pi)
    (centeredGaussianCharge a).im = 0 ∧
      0 < (centeredGaussianCharge a).re ∧
      (centeredGaussianCharge a).re/B < 1 := by
  dsimp only
  let B : ℝ := exp ((9/2:ℝ)*a)*exp (-(exp (2*a)-1)*Real.pi)
  let D : ℝ → ℂ := fun x => (B:ℂ)*literalGaussian 0 x-literalGaussian a x
  have hB : 0 < B := mul_pos (exp_pos _) (exp_pos _)
  have hlam : 1 < exp (2*a) := Real.one_lt_exp_iff.mpr (by linarith)
  have hDpos : ∀ x : ℝ, Real.pi < x → 0 < (D x).re := by
    intro x hx
    have hprod : 0 < (exp (2*a)-1)*(x-Real.pi) :=
      mul_pos (sub_pos.mpr hlam) (sub_pos.mpr hx)
    dsimp only [D, B, literalGaussian]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, zero_mul, exp_zero, zero_sub, one_mul]
    rw [← Real.exp_add, ← Real.exp_add]
    apply sub_pos.mpr
    apply Real.exp_lt_exp.mpr
    nlinarith
  have hD : originalPhysicalH6 D := by
    have hE := correctedGaussian_original_h6 a (B:ℂ)
    have heq : D = fun x => -(correctedGaussian a (B:ℂ) x) := by
      funext x
      dsimp only [D, correctedGaussian]
      ring
    rw [heq]
    refine ⟨hE.1.neg, ?_⟩
    simpa only [norm_neg] using hE.2
  have hDcharge : 0 < (actualSuzukiMeanCharge D).re :=
    actual_mean_re_pos_of_source_strictly_positive D hD hDpos
  have hH : originalPhysicalH6
      (fun x => (B:ℂ)*literalGaussian 0 x+(-1:ℂ)*literalGaussian a x) := by
    simpa only [D, neg_one_mul, ← sub_eq_add_neg] using hD
  have hlinear := actual_h6_suzuki_mean_charge_linear _ _
    (literalGaussian_original_h6 0) (literalGaussian_original_h6 a) (B:ℂ) (-1) hH
  have heq : (fun x => (B:ℂ)*literalGaussian 0 x+(-1:ℂ)*literalGaussian a x) = D := by
    funext x
    dsimp only [D]
    ring
  rw [heq] at hlinear
  have hupper : (actualSuzukiMeanCharge (literalGaussian a)).re <
      B*(actualSuzukiMeanCharge (literalGaussian 0)).re := by
    rw [hlinear] at hDcharge
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im,
      zero_mul, mul_zero, sub_zero, neg_zero, neg_mul, one_mul] at hDcharge
    linarith
  have hq := centeredGaussianCharge_eq_real_quotient ha.le
  have hqim : (centeredGaussianCharge a).im = 0 := by
    rw [hq]
    exact Complex.ofReal_im _
  have hqre : (centeredGaussianCharge a).re =
      (actualSuzukiMeanCharge (literalGaussian a)).re /
        (actualSuzukiMeanCharge (literalGaussian 0)).re := by
    rw [hq]
    exact Complex.ofReal_re _
  have hqpos : 0 < (centeredGaussianCharge a).re := by
    rw [hqre]
    exact div_pos (literalGaussian_charge_re_pos a) (literalGaussian_charge_re_pos 0)
  have hqB : (centeredGaussianCharge a).re < B := by
    rw [hqre]
    exact (div_lt_iff₀ (literalGaussian_charge_re_pos 0)).2 hupper
  refine ⟨hqim, hqpos, ?_⟩
  exact (div_lt_iff₀ hB).2 (by simpa only [one_mul] using hqB)

/-- The actual centering coefficient at the small shift is real, positive,
    and strictly below its exact physical endpoint ratio. This is the upper
    inequality consumed by the centered-Gaussian physical-cap proof. -/
theorem small_shift_centeredGaussianCharge_real_strict_upper :
    let a : ℝ := Real.log (4/3:ℝ)/2
    let A : ℝ := exp ((9/2:ℝ)*a)
    let lam : ℝ := exp (2*a)
    let B : ℝ := A*exp (-(lam-1)*Real.pi)
    (centeredGaussianCharge a).im = 0 ∧
      0 < (centeredGaussianCharge a).re ∧
      (centeredGaussianCharge a).re/B < 1 := by
  exact centeredGaussianCharge_strict_upper_general
    (div_pos (Real.log_pos (by norm_num : (1:ℝ)<4/3)) (by norm_num))

#print axioms small_shift_centeredGaussianCharge_real_strict_upper

end D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft

/- SOURCE DRAFT, NOT COMPILED. Transient exact applications only.
   Append after CenteredGaussianChargeBounds.fragment.lean in the SAME
   GaussianGammaDomainCheck module. Merge the extra imports at its top:
     import Mathlib.MeasureTheory.Group.Integral
     import Mathlib.MeasureTheory.Integral.Bochner.Set
   The expanded ActualSuzukiMeanCharge supplier from
   ActualSuzukiMeanChargeKernelCheck.lean must be available. Its original-H6
   weighted physical HasSum is consumed, not assumed here.

   The final theorem is an ACTUAL mean-charge bound, with no q-bound premise.
   The real/complex identification and strict upper bound are supplied by
   CenteredGaussianChargeUpper.fragment.lean on the same source.
-/

namespace D5.S3.Weil.ZetaGamma.FormCore.CenteredGaussianChargeBoundsDraft

open Real Set MeasureTheory Filter
open scoped Topology
open D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft
open private physicalTerm_h6 from
  D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiThetaExcess
open private meanCharge_physical_moment_formula from
  D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanCharge
-- literalGaussian and the positiveMean suppliers are private declarations in
-- this SAME assembled module; the namespace opens above expose their aliases.
-- The two explicit open-private sources above both exist in imported modules.

def gaussianMeanMode (r : ℝ) (j : ℕ) : ℝ :=
  (((j+1:ℕ):ℝ)^4) * exp (-Real.pi*r*((((j+1:ℕ):ℝ)^2)-1)) *
    meanModeI (r*(((j+1:ℕ):ℝ)^2))

def gaussianMeanSeries (r : ℝ) : ℝ := ∑' j : ℕ, gaussianMeanMode r j

def gaussianMeanScale (a : ℝ) : ℝ := exp ((9/2:ℝ)*a-Real.pi*exp (2*a))

def gaussianBoundaryRatio (a : ℝ) : ℝ :=
  exp ((9/2:ℝ)*a-(exp (2*a)-1)*Real.pi)

private theorem integral_Ioi_pi_translate (f : ℝ → ℂ) :
    (∫ x : ℝ in Ioi Real.pi, f x) =
      ∫ y : ℝ in Ioi 0, f (Real.pi+y) := by
  have hp : (fun y : ℝ => Real.pi+y) ⁻¹' Ioi Real.pi = Ioi 0 := by
    ext y
    simp only [mem_preimage, mem_Ioi]
    constructor <;> intro hy <;> linarith
  have hmp := measurePreserving_add_left (volume : Measure ℝ) Real.pi
  have h := hmp.setIntegral_preimage_emb
    (MeasurableEquiv.addLeft Real.pi).measurableEmbedding f (Ioi Real.pi)
  simpa only [hp] using h.symm

private theorem literalGaussian_shifted_physical_mode (a y : ℝ) (j : ℕ) :
    physicalTerm (literalGaussian a) j (Real.pi+y) =
      ((gaussianMeanScale a * (((j+1:ℕ):ℝ)^4) *
        exp (-Real.pi*exp (2*a)*((((j+1:ℕ):ℝ)^2)-1)) *
        exp (-(exp (2*a)*(((j+1:ℕ):ℝ)^2)*y)) : ℝ) : ℂ) := by
  let n : ℝ := (j+1:ℕ)
  have hpow : (((j+1:ℕ):ℂ)^4) = ((n^4 : ℝ) : ℂ) := by
    dsimp [n]
    push_cast
    rfl
  have he : exp ((9/2:ℝ)*a-exp (2*a)*(n^2*(Real.pi+y))) =
      gaussianMeanScale a * exp (-Real.pi*exp (2*a)*(n^2-1)) *
        exp (-(exp (2*a)*n^2*y)) := by
    rw [gaussianMeanScale, ← exp_add, ← exp_add]
    congr 1
    ring
  simp only [physicalTerm, literalGaussian]
  rw [hpow]
  change ((n^4 : ℝ):ℂ) *
    (exp ((9/2:ℝ)*a-exp (2*a)*(n^2*(Real.pi+y))) : ℂ) = _
  rw [he]
  dsimp [n]
  push_cast
  ring

/-- The original x>pi mode integral equals the shifted J-mode, with the
    full n^4 and original Gaussian scale. No finite truncation is used. -/
private theorem literalGaussian_mean_mode_integral (a : ℝ) (j : ℕ) :
    (∫ x : ℝ in Ioi Real.pi,
      ((6*Real.pi^(5/4:ℝ)-x^(5/4:ℝ) : ℝ):ℂ) *
        physicalTerm (literalGaussian a) j x) =
      ((gaussianMeanScale a * gaussianMeanMode (exp (2*a)) j : ℝ):ℂ) := by
  rw [integral_Ioi_pi_translate]
  calc
    _ = ((gaussianMeanScale a * (((j+1:ℕ):ℝ)^4) *
        exp (-Real.pi*exp (2*a)*((((j+1:ℕ):ℝ)^2)-1)) : ℝ):ℂ) *
        (∫ y : ℝ in Ioi 0,
          (((6*Real.pi^(5/4:ℝ)-(Real.pi+y)^(5/4:ℝ)) *
            exp (-(exp (2*a)*(((j+1:ℕ):ℝ)^2)*y)) : ℝ):ℂ)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        dsimp only
        rw [literalGaussian_shifted_physical_mode]
        push_cast
        ring
    _ = _ := by
      rw [integral_complex_ofReal]
      dsimp [gaussianMeanMode, meanModeI]
      push_cast
      ring

/-- Original H6 supplies the genuine complex HasSum; taking real parts
    preserves it, and division is by a strictly positive literal scale. -/
theorem literalGaussian_actual_mean_mode_series (a : ℝ) :
    HasSum (gaussianMeanMode (exp (2*a)))
      (5*(actualSuzukiMeanCharge (literalGaussian a)).re/gaussianMeanScale a) := by
  let F := literalGaussian a
  have hF : originalPhysicalH6 F := literalGaussian_original_h6 a
  have h0 := positiveMean_weighted_physical_mode_series F hF 0 (by norm_num)
  simp only [Real.rpow_zero, Complex.ofReal_one, one_mul] at h0
  have h5 := positiveMean_weighted_physical_mode_series F hF (5/4) (by norm_num)
  have hs := (h0.mul_left ((6*Real.pi^(5/4:ℝ):ℝ):ℂ)).sub h5
  have hterm (j : ℕ) :
      ((6*Real.pi^(5/4:ℝ):ℝ):ℂ) *
        (∫ x : ℝ in Ioi Real.pi, physicalTerm F j x) -
        (∫ x : ℝ in Ioi Real.pi,
          ((x^(5/4:ℝ):ℝ):ℂ) * physicalTerm F j x) =
        ((gaussianMeanScale a*gaussianMeanMode (exp (2*a)) j : ℝ):ℂ) := by
    have hj := physicalTerm_h6 F hF j
    have hi0 : IntegrableOn (physicalTerm F j) (Ioi Real.pi) := by
      simpa only [Real.rpow_zero, Complex.ofReal_one, one_mul] using
        physical_h6_weighted_l1 (physicalTerm F j) hj 0 (by norm_num)
    have hi5 := physical_h6_weighted_l1 (physicalTerm F j) hj (5/4) (by norm_num)
    calc
      _ = ∫ x : ℝ in Ioi Real.pi,
          ((6*Real.pi^(5/4:ℝ)-x^(5/4:ℝ) : ℝ):ℂ) * physicalTerm F j x := by
        rw [← integral_const_mul, ← integral_sub (hi0.const_mul _) hi5]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by push_cast; ring
      _ = _ := literalGaussian_mean_mode_integral a j
  have hc : HasSum
      (fun j : ℕ => ((gaussianMeanScale a*gaussianMeanMode (exp (2*a)) j : ℝ):ℂ))
      ((5:ℂ)*actualSuzukiMeanCharge F) := by
    convert hs using 1
    · funext j
      exact (hterm j).symm
    · rw [meanCharge_physical_moment_formula F hF]
      push_cast
      ring
  have hr : HasSum
      (fun j : ℕ => gaussianMeanScale a*gaussianMeanMode (exp (2*a)) j)
      (5*(actualSuzukiMeanCharge F).re) := by
    simpa [Complex.mul_re] using Complex.hasSum_re hc
  have hK : gaussianMeanScale a ≠ 0 := (exp_pos _).ne'
  have hn := hr.mul_left (gaussianMeanScale a)⁻¹
  convert hn using 1
  · funext j
    field_simp [hK] <;> ring
  · dsimp only [F]
    ring

theorem literalGaussian_actual_mean_mode_formula (a : ℝ) :
    5*(actualSuzukiMeanCharge (literalGaussian a)).re =
      gaussianMeanScale a*gaussianMeanSeries (exp (2*a)) := by
  have h := (literalGaussian_actual_mean_mode_series a).tsum_eq
  have hK : gaussianMeanScale a ≠ 0 := (exp_pos _).ne'
  dsimp only [gaussianMeanSeries]
  rw [h]
  field_simp [hK] <;> ring

private theorem gaussianMeanMode_nonneg {r : ℝ} (hr : 1 ≤ r) (j : ℕ) :
    0 ≤ gaussianMeanMode r j := by
  have hn : (1:ℝ) ≤ (j+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
  have hn2 : (1:ℝ) ≤ (((j+1:ℕ):ℝ)^2) := by nlinarith
  have hp : 1 ≤ r*(((j+1:ℕ):ℝ)^2) := by
    simpa only [one_mul] using
      (mul_le_mul hr hn2 (by norm_num : (0:ℝ)≤1) (by linarith : 0≤r))
  dsimp only [gaussianMeanMode]
  exact mul_nonneg (by positivity) (meanModeI_pos hp).le

private theorem gaussianMeanSeries_ge_first {r : ℝ} (hr : 1 ≤ r)
    (hs : Summable (gaussianMeanMode r)) : meanModeI r ≤ gaussianMeanSeries r := by
  have h := le_hasSum hs.hasSum 0 (fun j _ => gaussianMeanMode_nonneg hr j)
  simpa [gaussianMeanMode, gaussianMeanSeries] using h

private theorem gaussianMeanMode_one_tail_le (j : ℕ) :
    gaussianMeanMode 1 (j+1) ≤ 6*Real.pi^(5/4:ℝ)*highModeTail j := by
  let n : ℝ := (j+2:ℕ)
  have hn : 1 ≤ n := by dsimp [n]; exact_mod_cast (by omega : 1 ≤ j+2)
  have hn2 : 1 ≤ n^2 := by nlinarith
  have hJ := meanModeI_upper_simple hn2
  have he : 0 ≤ n^4*exp (-Real.pi*(n^2-1)) := by positivity
  have hh := mul_le_mul_of_nonneg_left hJ he
  have hval : n^4*exp (-Real.pi*(n^2-1))*(6*Real.pi^(5/4:ℝ)/n^2) =
      6*Real.pi^(5/4:ℝ)*(n^2*exp (-Real.pi*(n^2-1))) := by
    field_simp [show n ≠ 0 by linarith]
    <;> ring
  rw [hval] at hh
  simpa only [gaussianMeanMode, highModeTail, n, Nat.add_assoc, one_mul, mul_one]
    using hh

private theorem gaussianMeanSeries_one_upper
    (hs : Summable (gaussianMeanMode 1)) :
    gaussianMeanSeries 1 ≤ meanModeUpper 1+6*Real.pi^(5/4:ℝ)/127 := by
  have ht : Summable (fun j : ℕ => gaussianMeanMode 1 (j+1)) :=
    (summable_nat_add_iff 1).2 hs
  obtain ⟨hS, hSbound⟩ := highModeTail_summable_bound
  have hc : Summable (fun j : ℕ => 6*Real.pi^(5/4:ℝ)*highModeTail j) :=
    hS.mul_left (6*Real.pi^(5/4:ℝ))
  have htail := ht.tsum_le_tsum gaussianMeanMode_one_tail_le hc
  rw [tsum_mul_left] at htail
  have htbound : (∑' j : ℕ, gaussianMeanMode 1 (j+1)) ≤
      6*Real.pi^(5/4:ℝ)/127 := by
    have hp : 0 ≤ 6*Real.pi^(5/4:ℝ) := by positivity
    have hm := mul_le_mul_of_nonneg_left hSbound.le hp
    calc
      _ ≤ 6*Real.pi^(5/4:ℝ)*(∑' j : ℕ, highModeTail j) := htail
      _ ≤ 6*Real.pi^(5/4:ℝ)*(1/127:ℝ) := hm
      _ = _ := by ring
  have hfirst := (meanModeI_bounds (by norm_num : (0:ℝ)<1)).2
  have hsplit : gaussianMeanSeries 1 =
      meanModeI 1+(∑' j : ℕ, gaussianMeanMode 1 (j+1)) := by
    simpa [gaussianMeanSeries, gaussianMeanMode] using hs.tsum_eq_zero_add
  rw [hsplit]
  linarith

/-- This is the lower bound for the SAME source's actual centering coefficient,
    obtained from its complete original-H6 series; no q/s bound is assumed. -/
theorem actual_centering_ratio_gt_three_quarters :
    let a : ℝ := Real.log (4/3:ℝ)/2
    (3/4:ℝ) <
      ((actualSuzukiMeanCharge (literalGaussian a)).re /
        (actualSuzukiMeanCharge (literalGaussian 0)).re) / gaussianBoundaryRatio a := by
  let a : ℝ := Real.log (4/3:ℝ)/2
  have he : exp (2*a) = (4/3:ℝ) := by
    dsimp [a]
    rw [show 2*(Real.log (4/3:ℝ)/2) = Real.log (4/3:ℝ) by ring]
    exact exp_log (by norm_num)
  have hs0 : Summable (gaussianMeanMode 1) := by
    simpa only [mul_zero, exp_zero] using
      (literalGaussian_actual_mean_mode_series 0).summable
  have hslam : Summable (gaussianMeanMode (4/3)) := by
    simpa only [he] using (literalGaussian_actual_mean_mode_series a).summable
  have hC0 : 0 < gaussianMeanSeries 1 :=
    (meanModeI_pos (by norm_num : (1:ℝ)≤1)).trans_le
      (gaussianMeanSeries_ge_first (by norm_num) hs0)
  have hClam : meanModeLower (4/3) ≤ gaussianMeanSeries (4/3) :=
    (meanModeI_bounds (by norm_num : (0:ℝ)<4/3)).1.trans
      (gaussianMeanSeries_ge_first (by norm_num) hslam)
  have hpi2 : Real.pi^2 < 10 := by
    have hp := Real.pi_lt_d2
    nlinarith [Real.pi_pos]
  have hratio := mode_ratio_gt_three_quarters
    (gaussianMeanSeries 1) (gaussianMeanSeries (4/3)) hC0
    (gaussianMeanSeries_one_upper hs0) hClam hpi2
  have hμa := literalGaussian_actual_mean_mode_formula a
  rw [he] at hμa
  have hμ0 := literalGaussian_actual_mean_mode_formula 0
  simp only [mul_zero, exp_zero] at hμ0
  have hma : (actualSuzukiMeanCharge (literalGaussian a)).re =
      gaussianMeanScale a/5*gaussianMeanSeries (4/3) := by linarith
  have hm0 : (actualSuzukiMeanCharge (literalGaussian 0)).re =
      gaussianMeanScale 0/5*gaussianMeanSeries 1 := by linarith
  have hscale : gaussianMeanScale a = gaussianBoundaryRatio a*gaussianMeanScale 0 := by
    dsimp only [gaussianMeanScale, gaussianBoundaryRatio]
    rw [← exp_add]
    congr 1
    simp only [mul_zero, exp_zero]
    ring
  have hK : gaussianMeanScale 0 ≠ 0 := (exp_pos _).ne'
  have hB : gaussianBoundaryRatio a ≠ 0 := (exp_pos _).ne'
  have heq :
      ((actualSuzukiMeanCharge (literalGaussian a)).re /
        (actualSuzukiMeanCharge (literalGaussian 0)).re) / gaussianBoundaryRatio a =
      gaussianMeanSeries (4/3)/gaussianMeanSeries 1 := by
    rw [hma, hm0, hscale]
    field_simp [hK, hB, hC0.ne']
    <;> ring
  change (3/4:ℝ) < _
  rw [heq]
  exact hratio

end D5.S3.Weil.ZetaGamma.FormCore.CenteredGaussianChargeBoundsDraft

/- SOURCE DRAFT, NOT COMPILED. Append AFTER both actual charge consumers:
   CenteredGaussianActualChargeSeries and CenteredGaussianChargeUpper.
   This pays the exact complex-q/real-ratio/B identification for the cap
   consumer; the interval is not left as a hypothesis.
-/

namespace D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft

open Real
open D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open D5.S3.Weil.ZetaGamma.FormCore.CenteredGaussianChargeBoundsDraft

theorem small_shift_actual_centering_ratio_interval :
    let a : ℝ := Real.log (4/3:ℝ)/2
    let B : ℝ := exp ((9/2:ℝ)*a)*exp (-(exp (2*a)-1)*Real.pi)
    (centeredGaussianCharge a).im = 0 ∧
      (3/4:ℝ) < (centeredGaussianCharge a).re/B ∧
      (centeredGaussianCharge a).re/B < 1 := by
  let a : ℝ := Real.log (4/3:ℝ)/2
  let B : ℝ := exp ((9/2:ℝ)*a)*exp (-(exp (2*a)-1)*Real.pi)
  have ha : 0 ≤ a :=
    (div_pos (Real.log_pos (by norm_num : (1:ℝ)<4/3))
      (by norm_num : (0:ℝ)<2)).le
  have hq : (centeredGaussianCharge a).re =
      (actualSuzukiMeanCharge (literalGaussian a)).re /
        (actualSuzukiMeanCharge (literalGaussian 0)).re := by
    rw [centeredGaussianCharge_eq_real_quotient ha, Complex.ofReal_re]
  have hB : gaussianBoundaryRatio a = B := by
    dsimp only [gaussianBoundaryRatio, B]
    rw [← exp_add]
    congr 1
    ring
  have hlo := actual_centering_ratio_gt_three_quarters
  change (3/4:ℝ) <
    ((actualSuzukiMeanCharge (literalGaussian a)).re /
      (actualSuzukiMeanCharge (literalGaussian 0)).re) / gaussianBoundaryRatio a at hlo
  have hup := small_shift_centeredGaussianCharge_real_strict_upper
  change (centeredGaussianCharge a).im = 0 ∧
    0 < (centeredGaussianCharge a).re ∧ (centeredGaussianCharge a).re/B < 1 at hup
  change (centeredGaussianCharge a).im = 0 ∧
    (3/4:ℝ) < (centeredGaussianCharge a).re/B ∧
    (centeredGaussianCharge a).re/B < 1
  refine ⟨hup.1, ?_, hup.2.2⟩
  rw [hq, ← hB]
  exact hlo

end D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft

/- Transient exact application draft. Append after the charge interval
   fragments, in the same check module. No completed cap claim is made until
   the original-source substitution and its actual charge interval compile. -/

namespace D5.S3.Weil.ZetaGamma.FormCore.CenteredGaussianChargeBoundsDraft

open Real Set MeasureTheory
open scoped BigOperators

private def squareRay (r s y : ℝ) : ℝ :=
  (exp (-(r*y))-s*exp (-y))^2

private def squareMoment (r s : ℝ) (k : ℕ) : ℝ :=
  (k.factorial:ℝ)*(1/(2*r)^(k+1)-2*s/(r+1)^(k+1)+s^2/2^(k+1))

private theorem squareRay_moment {r : ℝ} (hr : 0 < r) (s : ℝ) (k : ℕ) :
    IntegrableOn (fun y : ℝ => y^k*squareRay r s y) (Ioi 0) ∧
    (∫ y : ℝ in Ioi 0, y^k*squareRay r s y) = squareMoment r s k := by
  obtain ⟨hA,vA⟩ := exp_moment (by positivity : 0 < 2*r) k
  obtain ⟨hB,vB⟩ := exp_moment (by positivity : 0 < r+1) k
  obtain ⟨hC,vC⟩ := exp_moment (by norm_num : (0:ℝ) < 2) k
  have he (y : ℝ) : y^k*squareRay r s y =
      y^k*exp (-((2*r)*y))-(2*s)*(y^k*exp (-((r+1)*y)))+
        s^2*(y^k*exp (-(2*y))) := by
    have hA' : exp (-((2*r)*y)) = exp (-(r*y))*exp (-(r*y)) := by
      rw [← exp_add]
      congr 1
      ring
    have hB' : exp (-((r+1)*y)) = exp (-(r*y))*exp (-y) := by
      rw [← exp_add]
      congr 1
      ring
    have hC' : exp (-(2*y)) = exp (-y)*exp (-y) := by
      rw [← exp_add]
      congr 1
      ring
    rw [hA',hB',hC']
    dsimp only [squareRay]
    ring
  have hI := (hA.sub (hB.const_mul (2*s))).add (hC.const_mul (s^2))
  constructor
  · apply IntegrableOn.congr_fun hI _ measurableSet_Ioi
    intro y _
    exact (he y).symm
  · calc
      _ = ∫ y : ℝ in Ioi 0,
          y^k*exp (-((2*r)*y))-(2*s)*(y^k*exp (-((r+1)*y)))+
            s^2*(y^k*exp (-(2*y))) :=
        setIntegral_congr_fun measurableSet_Ioi (fun y _ => he y)
      _ = squareMoment r s k := by
        have hAdd := integral_add (hA.sub (hB.const_mul (2*s))) (hC.const_mul (s^2))
        have hSub := integral_sub hA (hB.const_mul (2*s))
        simp only [Pi.sub_apply,Pi.add_apply] at hAdd hSub
        rw [hAdd,hSub,integral_const_mul,
          integral_const_mul, vA, vB, vC]
        dsimp only [squareMoment]
        ring

private theorem squareMoment_nonneg {r : ℝ} (hr : 0 < r) (s : ℝ) (k : ℕ) :
    0 ≤ squareMoment r s k := by
  rw [← (squareRay_moment hr s k).2]
  apply setIntegral_nonneg measurableSet_Ioi
  intro y hy
  exact mul_nonneg (pow_nonneg (le_of_lt hy) _) (sq_nonneg _)

private theorem squareMoment_zero_positive (s : ℝ) :
    0 < squareMoment (4/3) s 0 := by
  have h : squareMoment (4/3) s 0 = (s-6/7)^2/2+3/392 := by
    norm_num [squareMoment]
    ring
  rw [h]
  positivity

private theorem squareRay_binomial_integral {r : ℝ} (hr : 0 < r) (s c : ℝ) :
    IntegrableOn (fun y : ℝ => (1+c*y)^6*squareRay r s y) (Ioi 0) ∧
    (∫ y : ℝ in Ioi 0, (1+c*y)^6*squareRay r s y) =
      ∑ k ∈ Finset.range 7, (Nat.choose 6 k:ℝ)*c^k*squareMoment r s k := by
  let W : ℕ → ℝ → ℝ := fun k y =>
    ((Nat.choose 6 k:ℝ)*c^k)*(y^k*squareRay r s y)
  have hW (k : ℕ) : IntegrableOn (W k) (Ioi 0) :=
    (squareRay_moment hr s k).1.const_mul _
  have hEq : (fun y : ℝ => (1+c*y)^6*squareRay r s y) =
      fun y => ∑ k ∈ Finset.range 7, W k y := by
    funext y
    norm_num [W,Finset.sum_range_succ,Nat.choose]
    ring
  rw [hEq]
  refine ⟨integrable_finset_sum _ (fun k _ => hW k), ?_⟩
  rw [integral_finset_sum _ (fun k _ => hW k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [show (∫ y : ℝ in Ioi 0, W k y) =
      ((Nat.choose 6 k:ℝ)*c^k)*
        (∫ y : ℝ in Ioi 0, y^k*squareRay r s y) from integral_const_mul _ _]
  rw [(squareRay_moment hr s k).2]

private theorem squareRay_cap475_normalized (s : ℝ)
    (hs0 : (3/4:ℝ) ≤ s) (hs1 : s ≤ 1) :
    (19/4:ℝ) <
      (∫ y : ℝ in Ioi 0, (1+y/Real.pi)^6*squareRay (4/3) s y) /
        (∫ y : ℝ in Ioi 0, squareRay (4/3) s y) := by
  have hr : (0:ℝ) < 4/3 := by norm_num
  have hD := (squareRay_moment hr s 0).2
  simp only [pow_zero,one_mul] at hD
  have hP := (squareRay_binomial_integral hr s (1/Real.pi)).2
  have hN : (∫ y : ℝ in Ioi 0, (1+y/Real.pi)^6*squareRay (4/3) s y) =
      ∑ k ∈ Finset.range 7, (Nat.choose 6 k:ℝ)*(1/Real.pi)^k*
        squareMoment (4/3) s k := by
    simpa only [div_eq_mul_inv,mul_comm,one_div,one_mul,mul_one] using hP
  have hpi : (7/22:ℝ) ≤ 1/Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).2
    nlinarith [Real.pi_lt_d4]
  have hle : (∑ k ∈ Finset.range 7, (Nat.choose 6 k:ℝ)*(7/22:ℝ)^k*
        squareMoment (4/3) s k) ≤
      ∑ k ∈ Finset.range 7, (Nat.choose 6 k:ℝ)*(1/Real.pi)^k*
        squareMoment (4/3) s k := by
    apply Finset.sum_le_sum
    intro k _
    apply mul_le_mul_of_nonneg_right _ (squareMoment_nonneg hr s k)
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact pow_le_pow_left₀ (by norm_num) hpi k
  have hc := cap475_scalar_polynomial_certificate s hs0 hs1
  have hpoly :
      (∑ k ∈ Finset.range 7, (Nat.choose 6 k:ℝ)*(7/22:ℝ)^k*
        squareMoment (4/3) s k) - (19/4:ℝ)*squareMoment (4/3) s 0 =
      (-561141687/907039232:ℝ)*s^2+(20266236/12400927:ℝ)*s-
        (12877086436497/14860930777088:ℝ) := by
    norm_num [squareMoment,Finset.sum_range_succ,Nat.choose]
    ring
  rw [hD,hN]
  apply (lt_div_iff₀ (squareMoment_zero_positive s)).2
  linarith [hpoly]

#print axioms squareRay_cap475_normalized

end D5.S3.Weil.ZetaGamma.FormCore.CenteredGaussianChargeBoundsDraft

namespace D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft

open Real Set MeasureTheory
open D5.S3.Weil.ZetaGamma.FormCore.CenteredGaussianChargeBoundsDraft

private theorem real_integral_Ioi_pi_translate (f : ℝ → ℝ) :
    (∫ x : ℝ in Ioi Real.pi, f x) = ∫ y : ℝ in Ioi 0, f (Real.pi+y) := by
  have hp : (fun y : ℝ => Real.pi+y) ⁻¹' Ioi Real.pi = Ioi 0 := by
    ext y
    simp only [mem_preimage,mem_Ioi]
    constructor <;> intro hy <;> linarith
  have h := (measurePreserving_add_left (volume : Measure ℝ) Real.pi).setIntegral_preimage_emb
    (MeasurableEquiv.addLeft Real.pi).measurableEmbedding f (Ioi Real.pi)
  simpa only [hp] using h.symm

private theorem centeredGaussian_shifted_square
    {a : ℝ} (ha : exp (2*a) = 4/3) (q y : ℝ) :
    let B : ℝ := exp ((9/2:ℝ)*a-(exp (2*a)-1)*Real.pi)
    ‖correctedGaussian a (q:ℂ) (Real.pi+y)‖^2 =
      (exp (-Real.pi)*B)^2*squareRay (4/3) (q/B) y := by
  dsimp only
  let B : ℝ := exp ((9/2:ℝ)*a-(exp (2*a)-1)*Real.pi)
  change ‖correctedGaussian a (q:ℂ) (Real.pi+y)‖^2 =
    (exp (-Real.pi)*B)^2*squareRay (4/3) (q/B) y
  have hB : B ≠ 0 := (exp_pos _).ne'
  have hga : exp ((9/2:ℝ)*a-exp (2*a)*(Real.pi+y)) =
      exp (-Real.pi)*B*exp (-((4/3:ℝ)*y)) := by
    dsimp only [B]
    rw [← exp_add,← exp_add,ha]
    congr 1
    ring
  have hg0 : exp (-(Real.pi+y)) = exp (-Real.pi)*exp (-y) := by
    rw [← exp_add]
    congr 1
    ring
  have hnorm : ‖correctedGaussian a (q:ℂ) (Real.pi+y)‖^2 =
      (exp ((9/2:ℝ)*a-exp (2*a)*(Real.pi+y))-
        q*exp (-(Real.pi+y)))^2 := by
    simp only [correctedGaussian,literalGaussian,mul_zero,exp_zero,one_mul,zero_sub,
      ← Complex.ofReal_mul,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [hnorm,hga,hg0]
  dsimp only [squareRay]
  field_simp [hB]

private theorem actual_gaussian_physical_cap475_of_interval
    {a : ℝ} (ha : exp (2*a) = 4/3) (q : ℝ)
    (hq0 : (3/4:ℝ) ≤ q/gaussianBoundaryRatio a)
    (hq1 : q/gaussianBoundaryRatio a ≤ 1) :
    (19/4:ℝ) <
      (∫ x : ℝ in Ioi Real.pi, x^6*‖correctedGaussian a (q:ℂ) x‖^2) /
        (Real.pi^6*(∫ x : ℝ in Ioi Real.pi, ‖correctedGaussian a (q:ℂ) x‖^2)) := by
  let B : ℝ := gaussianBoundaryRatio a
  let s : ℝ := q/B
  let K : ℝ := exp (-Real.pi)*B
  have hB : 0 < B := exp_pos _
  have hK : K ≠ 0 := (mul_pos (exp_pos _) hB).ne'
  have hsq (y : ℝ) : ‖correctedGaussian a (q:ℂ) (Real.pi+y)‖^2 =
      K^2*squareRay (4/3) s y := centeredGaussian_shifted_square ha q y
  have hD : (∫ x : ℝ in Ioi Real.pi, ‖correctedGaussian a (q:ℂ) x‖^2) =
      K^2*(∫ y : ℝ in Ioi 0, squareRay (4/3) s y) := by
    rw [real_integral_Ioi_pi_translate]
    simp_rw [hsq]
    exact integral_const_mul _ _
  have hN : (∫ x : ℝ in Ioi Real.pi, x^6*‖correctedGaussian a (q:ℂ) x‖^2) =
      (Real.pi^6*K^2)*(∫ y : ℝ in Ioi 0,
        (1+y/Real.pi)^6*squareRay (4/3) s y) := by
    rw [real_integral_Ioi_pi_translate]
    calc
      _ = ∫ y : ℝ in Ioi 0,
          (Real.pi^6*K^2)*((1+y/Real.pi)^6*squareRay (4/3) s y) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y _
        dsimp only
        rw [hsq]
        field_simp [Real.pi_ne_zero]
      _ = _ := integral_const_mul _ _
  have hden : (∫ y : ℝ in Ioi 0, squareRay (4/3) s y) ≠ 0 := by
    have h := (squareRay_moment (by norm_num : (0:ℝ)<4/3) s 0).2
    simp only [pow_zero,one_mul] at h
    rw [h]
    exact (squareMoment_zero_positive s).ne'
  have hratio := squareRay_cap475_normalized s hq0 hq1
  rw [hN,hD]
  convert hratio using 1
  field_simp [hK,Real.pi_ne_zero,hden]

/-- The actual small-shift centered source, with its actual mean coefficient,
    satisfies the original x>pi sixth-moment ratio strictly above 19/4. -/
theorem small_shift_actual_centered_gaussian_cap475 :
    let a : ℝ := Real.log (4/3:ℝ)/2
    (19/4:ℝ) <
      (∫ x : ℝ in Ioi Real.pi,
        x^6*‖correctedGaussian a (centeredGaussianCharge a) x‖^2) /
      (Real.pi^6*(∫ x : ℝ in Ioi Real.pi,
        ‖correctedGaussian a (centeredGaussianCharge a) x‖^2)) := by
  dsimp only
  let a : ℝ := Real.log (4/3:ℝ)/2
  have ha : exp (2*a) = 4/3 := by
    dsimp only [a]
    rw [show 2*(Real.log (4/3:ℝ)/2) = Real.log (4/3:ℝ) by ring,
      Real.exp_log (by norm_num : (0:ℝ)<4/3)]
  obtain ⟨him,hlo,hhi⟩ := small_shift_actual_centering_ratio_interval
  have hima : (centeredGaussianCharge a).im = 0 := him
  have hq : centeredGaussianCharge a = ((centeredGaussianCharge a).re:ℂ) := by
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · simpa only [Complex.ofReal_im] using hima
  have hboundary : gaussianBoundaryRatio a =
      exp ((9/2:ℝ)*a)*exp (-(exp (2*a)-1)*Real.pi) := by
    dsimp only [gaussianBoundaryRatio]
    rw [← exp_add]
    congr 1
    ring
  have hbound :
      (19/4:ℝ) <
        (∫ x : ℝ in Ioi Real.pi,
          x^6*‖correctedGaussian a ((centeredGaussianCharge a).re:ℂ) x‖^2) /
        (Real.pi^6*(∫ x : ℝ in Ioi Real.pi,
          ‖correctedGaussian a ((centeredGaussianCharge a).re:ℂ) x‖^2)) := by
    apply actual_gaussian_physical_cap475_of_interval ha _
    · simpa only [hboundary] using hlo.le
    · simpa only [hboundary] using hhi.le
  simpa only [← hq] using hbound

#print axioms small_shift_actual_centered_gaussian_cap475

theorem small_shift_actual_centered_gaussian_full_cap475_witness :
    ∃ F : ℝ → ℂ,
      D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample.originalPhysicalH6 F ∧
      D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample.actualSuzukiMeanCharge F = 0 ∧
      (∀ c : ℝ,
        D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample.originalGammaFormDomain c F) ∧
      (19/4:ℝ) < (∫ x : ℝ in Ioi Real.pi, x^6*‖F x‖^2) /
        (Real.pi^6*(∫ x : ℝ in Ioi Real.pi, ‖F x‖^2)) ∧
      ∃ n : ℕ,
        Integrable (fun r : ℝ =>
          D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample.actualSuzukiEvenBProfile F r*
            Complex.exp (Complex.I*
              D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData.zetaZeroData.gamma n*(r:ℂ))) volume ∧
        (∫ r : ℝ,
          D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample.actualSuzukiEvenBProfile F r*
            Complex.exp (Complex.I*
              D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData.zetaZeroData.gamma n*(r:ℂ))) ≠ 0 := by
  obtain ⟨F,hF,hH,hmean,hGamma,n,hI,hnonzero⟩ :=
    small_shift_actual_centered_gaussian_full_spectrum_witness
  refine ⟨F,hH,hmean,hGamma,?_,n,hI,hnonzero⟩
  rw [hF]
  exact small_shift_actual_centered_gaussian_cap475

#print axioms small_shift_actual_centered_gaussian_full_cap475_witness

end D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft
