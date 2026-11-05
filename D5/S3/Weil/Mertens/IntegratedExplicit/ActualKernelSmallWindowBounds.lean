/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelSmallWindowBounds
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualKernelSmallWindowBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact finite-prime and continuum remainder bounds on the inclusive small window. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentPayments
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import D5.S3.Arith.GoldenResource.RobinRationalBasis

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology
open D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
open D5.S3.Arith.Robin.CompleteMertensPeak

namespace D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate

variable {I : Type u} [Fintype I]

private lemma gamma_lower_small : (13 / 25 : ℝ) < Real.eulerMascheroniConstant := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.eulerMascheroni_decimal_bounds
  norm_num at h ⊢
  linarith

private lemma gamma_upper_small : Real.eulerMascheroniConstant < (289 / 500 : ℝ) := by
  have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.eulerMascheroni_decimal_bounds
  norm_num at h ⊢
  linarith

private lemma log_two_pi_upper : Real.log (2 * Real.pi) < (46 / 25 : ℝ) := by
  rw [Real.log_lt_iff_lt_exp (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have he : (12097943374001 / 1922607421875 : ℝ) ≤ Real.exp (46 / 25) := by
    convert (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 46 / 25) 8) using 1 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial_succ]
  have hp : (2 * Real.pi : ℝ) < 44 / 7 := by
    nlinarith [Real.pi_lt_d20]
  have hrat : (44 / 7 : ℝ) < (12097943374001 / 1922607421875 : ℝ) := by norm_num
  exact lt_of_lt_of_le (hp.trans hrat) he

lemma d0_upper_small : d0 < (709 / 500 : ℝ) := by
  dsimp [d0]
  linarith [gamma_upper_small, log_two_pi_upper]

private lemma log_three_lt_eleven_tenths : Real.log 3 < (11 / 10 : ℝ) := by
  have h := Real.log_three_lt_d9
  norm_num at h ⊢
  linarith

lemma small_M_upper {D : ℝ} (hD0 : 0 ≤ D) (hD3 : D ≤ Real.log 3) :
    M D ≤ (7 / 4 : ℝ) := by
  have hE : Real.exp (D / 2) ≤ Real.exp (Real.log 3 / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have hsq : Real.exp (Real.log 3 / 2) = Real.sqrt 3 := by
    have hp : (0 : ℝ) < 3 := by norm_num
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    have he : 0 ≤ Real.exp (Real.log 3 / 2) := Real.exp_pos _ |>.le
    have he2 : (Real.exp (Real.log 3 / 2)) ^ 2 = 3 := by
      rw [pow_two, ← Real.exp_add]
      convert Real.exp_log hp using 1 <;> ring
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  dsimp [M]
  rw [hsq] at hE
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

lemma small_D_upper {D : ℝ} (hD3 : D ≤ Real.log 3) : D < (11 / 10 : ℝ) :=
  lt_of_le_of_lt hD3 log_three_lt_eleven_tenths

lemma primes_empty_small {D : ℝ} (hD0 : 0 ≤ D) (hD2 : D < Real.log 2) :
    primes D = ∅ := by
  have he : Real.exp D < 2 := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_lt_exp.mpr hD2
  have hf : ⌊Real.exp D⌋₊ < 2 := (Nat.floor_lt (Real.exp_pos D).le).2 he
  ext n
  simp [primes]
  omega

lemma primes_two_small {D : ℝ} (hD2 : Real.log 2 ≤ D)
    (hD3 : D < Real.log 3) : primes D = {2} := by
  have he2 : (2 : ℝ) ≤ Real.exp D := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr hD2
  have he3 : Real.exp D < 3 := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_lt_exp.mpr hD3
  have hf : ⌊Real.exp D⌋₊ = 2 := by
    apply (Nat.floor_eq_iff (Real.exp_pos D).le).mpr
    constructor
    · exact_mod_cast he2
    · norm_num at he3 ⊢
      exact he3
  ext n
  simp only [primes, Finset.mem_Icc, Finset.mem_singleton]
  rw [hf]
  omega

lemma primes_three_small : primes (Real.log 3) = {2, 3} := by
  have hf : ⌊Real.exp (Real.log 3)⌋₊ = 3 := by
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    norm_num
  ext n
  simp only [primes, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  rw [hf]
  omega

private lemma b_empty_small {D : ℝ} (hD0 : 0 ≤ D) (hD2 : D < Real.log 2) :
    b D = Real.eulerMascheroniConstant - D := by
  rw [b, F, primes_empty_small hD0 hD2]
  ring_nf

private lemma b_two_small {D : ℝ} (hD2 : Real.log 2 ≤ D)
    (hD3 : D < Real.log 3) :
    b D = Real.eulerMascheroniConstant - D + Real.log 2 / 2 := by
  rw [b, F, primes_two_small hD2 hD3]
  have hΛ : ArithmeticFunction.vonMangoldt 2 = Real.log 2 :=
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)
  norm_num [F, hΛ]
  ring

private lemma b_three_small :
    b (Real.log 3) = Real.eulerMascheroniConstant - Real.log 3 +
      Real.log 2 / 2 + Real.log 3 / 3 := by
  rw [b, F, primes_three_small]
  have h2 : ArithmeticFunction.vonMangoldt 2 = Real.log 2 :=
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)
  have h3 : ArithmeticFunction.vonMangoldt 3 = Real.log 3 :=
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)
  norm_num [F, h2, h3]
  ring

private lemma weighted_S_integral_bound (D : ℝ) (hD : 0 ≤ D)
    (x : I → ℝ) (a : I → ℂ) (hW : 0 ≤ W D x a)
    (hS : ∀ t : ℝ, |S D x a t| ≤ W D x a)
    (ha : ∑ i, a i = 0) :
    |∫ t in Icc (0 : ℝ) D, Real.exp (t / 2) * S D x a t| ≤
      2 * (M D - 1) * W D x a := by
  have hSi : IntegrableOn (fun t : ℝ => Real.exp (t / 2) * S D x a t)
      (Icc (0 : ℝ) D) := by
    have hs : Continuous (S D x a) := by
      rw [show S D x a = fun t => (1 / 4) *
          ∫ s in Icc (-D) D, Real.exp (-|t - s| / 2) * correlation x a s from
        rfl]
      rw [show (fun t : ℝ => (1 / 4) *
          ∫ s in Icc (-D) D, Real.exp (-|t - s| / 2) * correlation x a s) =
          fun t => (1 / 4) * ∫ s in Icc (0 : ℝ) D,
            pairedResolvent t s * correlation x a s from
        funext (S_half_window D hD x a ha)]
      apply continuous_const.mul
      apply continuous_parametric_integral_of_continuous _ isCompact_Icc
      dsimp [pairedResolvent]
      exact (by fun_prop : Continuous (fun z : ℝ × ℝ =>
        (Real.exp (-|z.1 - z.2| / 2) + Real.exp (-|z.1 + z.2| / 2)))).mul
        ((correlation_continuous x a ha).comp continuous_snd)
    exact ((by fun_prop : Continuous (fun t : ℝ => Real.exp (t / 2))).mul hs).integrableOn_Icc
  have hexp : (∫ t in Icc (0 : ℝ) D, Real.exp (t / 2)) = 2 * (M D - 1) := by
    have he (t : ℝ) : HasDerivAt (fun t => 2 * Real.exp (t / 2)) (Real.exp (t / 2)) t := by
      convert (((hasDerivAt_id t).div_const 2).exp.const_mul 2) using 1 <;>
        (try funext y) <;> (try dsimp only [id, Pi.neg_apply]) <;> ring
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hD,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => he t)
        ((by fun_prop : Continuous (fun t : ℝ => Real.exp (t / 2))).intervalIntegrable 0 D)]
    simp [M]
    ring
  calc
    _ ≤ ∫ t in Icc (0 : ℝ) D, |Real.exp (t / 2) * S D x a t| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ t in Icc (0 : ℝ) D, Real.exp (t / 2) * W D x a := by
      apply setIntegral_mono_on hSi.abs
        ((by fun_prop : Continuous (fun t : ℝ => Real.exp (t / 2) * W D x a)).integrableOn_Icc)
        measurableSet_Icc
      intro t ht
      rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hS t) (Real.exp_nonneg _)
    _ = _ := by
      rw [integral_mul_const, hexp]

lemma log_two_weight_bound :
    2 * (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) ≤ (1 : ℝ) := by
  have hΛ : ArithmeticFunction.vonMangoldt 2 = Real.log 2 :=
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)
  rw [hΛ]
  have hs0 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs : (7 / 5 : ℝ) < Real.sqrt 2 := by
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hn := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have hl : Real.log 2 < (7 / 10 : ℝ) := by
    have h := Real.log_two_lt_d9
    norm_num at h ⊢
    linarith
  rw [show 2 * (Real.log 2 / Real.sqrt 2) = (2 * Real.log 2) / Real.sqrt 2 by ring]
  apply (div_le_iff₀ hs0).mpr
  nlinarith

private lemma b_empty_abs_small {D : ℝ} (hD0 : 0 ≤ D)
    (hD2 : D < Real.log 2) (hD3 : D ≤ Real.log 3) :
    |b D| ≤ (29 / 50 : ℝ) := by
  rw [b_empty_small hD0 hD2]
  have hD11 := small_D_upper hD3
  have hlow := gamma_lower_small
  have hupp := gamma_upper_small
  apply (abs_le).2
  constructor <;> linarith

private lemma b_two_abs_small {D : ℝ} (hD2 : Real.log 2 ≤ D)
    (hD3 : D < Real.log 3) :
    |b D| ≤ (29 / 50 : ℝ) := by
  rw [b_two_small hD2 hD3]
  have hD11 := small_D_upper hD3.le
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlow := gamma_lower_small
  have hupp := gamma_upper_small
  apply (abs_le).2
  constructor
  · linarith
  · have : Real.log 2 / 2 ≤ D / 2 := by linarith
    linarith

private lemma b_three_eff_abs_small :
    |Real.eulerMascheroniConstant - Real.log 3 + Real.log 2 / 2| ≤
      (29 / 50 : ℝ) := by
  have hD11 := log_three_lt_eleven_tenths
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlow := gamma_lower_small
  have hupp := gamma_upper_small
  have hlog3lo := Real.log_three_gt_d9
  have hlog3hi := Real.log_three_lt_d9
  have hlog2lo := Real.log_two_gt_d9
  have hlog2hi := Real.log_two_lt_d9
  norm_num at hlog3lo hlog3hi hlog2lo hlog2hi
  apply (abs_le).2
  constructor
  · linarith
  · linarith

lemma small_V_abs_bound (D : ℝ) (hD0 : 0 ≤ D) (hD3 : D ≤ Real.log 3)
    (q : ℕ) (hq : 1 ≤ q) (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hm : ∀ r : ℕ, r ≤ q → ∑ i, a i * (x i : ℂ) ^ r = 0) :
    |V D x a| ≤ (603 / 100 : ℝ) * W D x a := by
  have ha : ∑ i, a i = 0 := by simpa using hm 0 (Nat.zero_le q)
  by_cases hDzero : D = 0
  · subst D
    have hSzero : ∀ t : ℝ, S 0 x a t = 0 := by
      intro t
      unfold S
      rw [show Icc (-0 : ℝ) 0 = ({0} : Set ℝ) by ext; simp]
      simp
    have hVzero : V 0 x a = 0 := by
      rw [V, primes_empty_small (D := 0) (by norm_num)
        (by have h := Real.log_two_gt_d9; norm_num at h ⊢; linarith)]
      simp [hSzero, Z, W, M]
    rw [hVzero, abs_zero]
    simp [W, hSzero]
  have hD0' : 0 < D := lt_of_le_of_ne hD0 (Ne.symm hDzero)
  have hs := actual_resolvent_control D hD0' q hq x a hx hm
  have hI := weighted_S_integral_bound D hD0 x a hs.1 hs.2.1 ha
  have hM := small_M_upper hD0 hD3
  have hD11 := small_D_upper hD3
  have hcoefM : (0 : ℝ) ≤ M D := by dsimp [M]; positivity
  have hmain : 2 * (M D - 1) * W D x a ≤ 2 * (M D - 1) * W D x a := le_rfl
  have hbase : 4 * (M D - 1) * W D x a ≤ (603 / 100 : ℝ) * W D x a := by
    have hM1 : 0 ≤ M D - 1 := by
      have := Real.one_le_exp (show 0 ≤ D / 2 by linarith)
      dsimp [M] at this ⊢
      linarith
    nlinarith
  have hprime : 2 * (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) *
      |S D x a (Real.log 2)| ≤ W D x a := by
    have hw := log_two_weight_bound
    have hs2 := hs.2.1 (Real.log 2)
    have hw0 : 0 ≤ ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 := by
      have hΛ : ArithmeticFunction.vonMangoldt 2 = Real.log 2 :=
        ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)
      rw [hΛ]
      positivity
    have hc0 : 0 ≤ 2 * (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) :=
      mul_nonneg (by norm_num) hw0
    have hs2' := mul_le_mul_of_nonneg_left hs2 hc0
    have hsW := mul_le_mul_of_nonneg_right hw (hs.1)
    nlinarith
  by_cases hEq : D = Real.log 3
  · subst D
    have hVeq : V (Real.log 3) x a =
        2 * (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) * S (Real.log 3) x a (Real.log 2) -
          2 * (∫ t in Icc (0 : ℝ) (Real.log 3), Real.exp (t / 2) * S (Real.log 3) x a t) -
          (Real.eulerMascheroniConstant - Real.log 3 + Real.log 2 / 2) / 2 *
            Z (Real.log 3) x a := by
      rw [V, primes_three_small, b_three_small]
      have h2 : ArithmeticFunction.vonMangoldt 2 = Real.log 2 :=
        ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)
      have h3 : ArithmeticFunction.vonMangoldt 3 = Real.log 3 :=
        ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)
      dsimp [Z, M]
      simp only [Finset.sum_insert, Finset.sum_singleton, h2, h3, ne_eq, OfNat.zero_ne_ofNat,
        not_false_eq_true, zero_add]
      norm_num
      ring_nf
      have hsqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      have hsqrt0 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
      have hexp : Real.exp (Real.log 3 / 2) = Real.sqrt 3 := by
        have hp : (0 : ℝ) < 3 := by norm_num
        have he2 : (Real.exp (Real.log 3 / 2)) ^ 2 = 3 := by
          rw [pow_two, ← Real.exp_add]
          convert Real.exp_log hp using 1 <;> ring
        nlinarith [Real.exp_pos (Real.log 3 / 2), Real.sqrt_nonneg (3 : ℝ)]
      have hexp' : Real.exp (Real.log 3 * (1 / 2 : ℝ)) = Real.sqrt 3 := by
        convert hexp using 1 <;> ring
      rw [hexp']
      have hinv : (Real.sqrt 3)⁻¹ = Real.sqrt 3 / 3 := by
        field_simp [hsqrt0]
        nlinarith [hsqrt]
      rw [h2, h3, hinv]
      ring
    rw [hVeq]
    have hb := b_three_eff_abs_small
    have hz := hs.2.2.2
    have hA := hI
    have hsum : |2 * (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) *
          S (Real.log 3) x a (Real.log 2) -
          2 * (∫ t in Icc (0 : ℝ) (Real.log 3), Real.exp (t / 2) * S (Real.log 3) x a t) -
          (Real.eulerMascheroniConstant - Real.log 3 + Real.log 2 / 2) / 2 *
            Z (Real.log 3) x a| ≤
        |2 * (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) *
          S (Real.log 3) x a (Real.log 2)| +
          |2 * (∫ t in Icc (0 : ℝ) (Real.log 3), Real.exp (t / 2) * S (Real.log 3) x a t)| +
          |(Real.eulerMascheroniConstant - Real.log 3 + Real.log 2 / 2) / 2 *
            Z (Real.log 3) x a| := by
      calc
        _ ≤ |2 * (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) * S (Real.log 3) x a (Real.log 2) -
            2 * (∫ t in Icc (0 : ℝ) (Real.log 3), Real.exp (t / 2) * S (Real.log 3) x a t)| +
            |(Real.eulerMascheroniConstant - Real.log 3 + Real.log 2 / 2) / 2 * Z (Real.log 3) x a| :=
          by simpa using (abs_sub_le
            (2 * (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) * S (Real.log 3) x a (Real.log 2) -
              2 * (∫ t in Icc (0 : ℝ) (Real.log 3), Real.exp (t / 2) * S (Real.log 3) x a t))
            0 ((Real.eulerMascheroniConstant - Real.log 3 + Real.log 2 / 2) / 2 * Z (Real.log 3) x a))
          _ ≤ _ := add_le_add (by simpa using (abs_sub_le
          (2 * (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) * S (Real.log 3) x a (Real.log 2))
          0 (2 * (∫ t in Icc (0 : ℝ) (Real.log 3), Real.exp (t / 2) * S (Real.log 3) x a t)))) (le_rfl)
    have htermI : |2 * (∫ t in Icc (0 : ℝ) (Real.log 3), Real.exp (t / 2) * S (Real.log 3) x a t)| ≤
        4 * (M (Real.log 3) - 1) * W (Real.log 3) x a := by
      have := mul_le_mul_of_nonneg_left hI (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith [abs_mul (2 : ℝ) (∫ t in Icc (0 : ℝ) (Real.log 3), Real.exp (t / 2) * S (Real.log 3) x a t)]
    have htermZ : |(Real.eulerMascheroniConstant - Real.log 3 + Real.log 2 / 2) / 2 *
          Z (Real.log 3) x a| ≤ (29 / 25 : ℝ) * M (Real.log 3) * W (Real.log 3) x a := by
      rw [abs_mul]
      have hbhalf : |(Real.eulerMascheroniConstant - Real.log 3 + Real.log 2 / 2) / 2| ≤
          (29 / 100 : ℝ) := by
        rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
        nlinarith [hb]
      calc
        |(Real.eulerMascheroniConstant - Real.log 3 + Real.log 2 / 2) / 2| *
            |Z (Real.log 3) x a| ≤ (29 / 100 : ℝ) * |Z (Real.log 3) x a| :=
          mul_le_mul_of_nonneg_right hbhalf (abs_nonneg _)
        _ ≤ (29 / 100 : ℝ) * (4 * M (Real.log 3) * W (Real.log 3) x a) :=
          mul_le_mul_of_nonneg_left hz (by norm_num)
        _ = (29 / 25 : ℝ) * M (Real.log 3) * W (Real.log 3) x a := by ring
    have htermP : |2 * (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) *
          S (Real.log 3) x a (Real.log 2)| ≤ W (Real.log 3) x a := by
      simpa [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (show 0 ≤ ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 by
          have hΛ : ArithmeticFunction.vonMangoldt 2 = Real.log 2 :=
            ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)
          rw [hΛ]
          positivity)] using hprime
    have hMW4 : 4 * M (Real.log 3) * W (Real.log 3) x a ≤
        7 * W (Real.log 3) x a := by
      calc
        4 * M (Real.log 3) * W (Real.log 3) x a =
            M (Real.log 3) * (4 * W (Real.log 3) x a) := by ring
        _ ≤ (7 / 4 : ℝ) * (4 * W (Real.log 3) x a) :=
          mul_le_mul_of_nonneg_right hM
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hs.1)
        _ = 7 * W (Real.log 3) x a := by ring
    have hIbound : |2 * (∫ t in Icc (0 : ℝ) (Real.log 3),
          Real.exp (t / 2) * S (Real.log 3) x a t)| ≤
        3 * W (Real.log 3) x a := by
      calc
        _ ≤ 4 * (M (Real.log 3) - 1) * W (Real.log 3) x a := htermI
        _ = 4 * M (Real.log 3) * W (Real.log 3) x a -
            4 * W (Real.log 3) x a := by ring
        _ ≤ 7 * W (Real.log 3) x a - 4 * W (Real.log 3) x a :=
          sub_le_sub_right hMW4 _
        _ = 3 * W (Real.log 3) x a := by ring
    have hZbound : |(Real.eulerMascheroniConstant - Real.log 3 + Real.log 2 / 2) / 2 *
          Z (Real.log 3) x a| ≤ (203 / 100 : ℝ) * W (Real.log 3) x a := by
      calc
        _ ≤ (29 / 25 : ℝ) * M (Real.log 3) * W (Real.log 3) x a := htermZ
        _ = (29 / 100 : ℝ) * (4 * M (Real.log 3) * W (Real.log 3) x a) := by ring
        _ ≤ (29 / 100 : ℝ) * (7 * W (Real.log 3) x a) :=
          mul_le_mul_of_nonneg_left hMW4 (by norm_num)
        _ = (203 / 100 : ℝ) * W (Real.log 3) x a := by ring
    nlinarith only [hsum, htermP, hIbound, hZbound, hs.1]
  · by_cases hD2 : D < Real.log 2
    · have hVeq : V D x a =
          -2 * (∫ t in Icc (0 : ℝ) D, Real.exp (t / 2) * S D x a t) - b D / 2 * Z D x a := by
        rw [V, primes_empty_small hD0 hD2]
        simp
      rw [hVeq]
      have hb := b_empty_abs_small hD0 hD2 hD3
      have hz := hs.2.2.2
      have htermI := mul_le_mul_of_nonneg_left hI (by norm_num : (0 : ℝ) ≤ 2)
      have htermI' : |2 * (∫ t in Icc (0 : ℝ) D,
          Real.exp (t / 2) * S D x a t)| ≤
          4 * (M D - 1) * W D x a := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        nlinarith [htermI]
      have hsum : |(-2 * (∫ t in Icc (0 : ℝ) D,
          Real.exp (t / 2) * S D x a t) - b D / 2 * Z D x a)| ≤
          |2 * (∫ t in Icc (0 : ℝ) D, Real.exp (t / 2) * S D x a t)| +
          |b D / 2 * Z D x a| := by
        calc
          _ ≤ |2 * (∫ t in Icc (0 : ℝ) D,
              Real.exp (t / 2) * S D x a t)| + |b D / 2 * Z D x a| :=
            by simpa using (abs_sub_le
              (-2 * (∫ t in Icc (0 : ℝ) D, Real.exp (t / 2) * S D x a t))
              0 (b D / 2 * Z D x a))
          _ = _ := by ring_nf
      have hbhalf : |b D / 2| ≤ (29 / 100 : ℝ) := by
        rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
        nlinarith [hb]
      have htermZ' : |b D / 2 * Z D x a| ≤
          (29 / 25 : ℝ) * M D * W D x a := by
        rw [abs_mul]
        calc
          |b D / 2| * |Z D x a| ≤ (29 / 100 : ℝ) * |Z D x a| :=
            mul_le_mul_of_nonneg_right hbhalf (abs_nonneg _)
          _ ≤ (29 / 100 : ℝ) * (4 * M D * W D x a) :=
            mul_le_mul_of_nonneg_left hz (by norm_num)
          _ = (29 / 25 : ℝ) * M D * W D x a := by ring
      have hMW4 : 4 * M D * W D x a ≤ 7 * W D x a := by
        calc
          4 * M D * W D x a = M D * (4 * W D x a) := by ring
          _ ≤ (7 / 4 : ℝ) * (4 * W D x a) :=
            mul_le_mul_of_nonneg_right hM
              (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hs.1)
          _ = 7 * W D x a := by ring
      have hIbound : |2 * (∫ t in Icc (0 : ℝ) D,
            Real.exp (t / 2) * S D x a t)| ≤ 3 * W D x a := by
        calc
          _ ≤ 4 * (M D - 1) * W D x a := htermI'
          _ = 4 * M D * W D x a - 4 * W D x a := by ring
          _ ≤ 7 * W D x a - 4 * W D x a := sub_le_sub_right hMW4 _
          _ = 3 * W D x a := by ring
      have hZbound : |b D / 2 * Z D x a| ≤ (203 / 100 : ℝ) * W D x a := by
        calc
          _ ≤ (29 / 25 : ℝ) * M D * W D x a := htermZ'
          _ = (29 / 100 : ℝ) * (4 * M D * W D x a) := by ring
          _ ≤ (29 / 100 : ℝ) * (7 * W D x a) :=
            mul_le_mul_of_nonneg_left hMW4 (by norm_num)
          _ = (203 / 100 : ℝ) * W D x a := by ring
      nlinarith only [hsum, hIbound, hZbound, hs.1]
    · have hD2' : Real.log 2 ≤ D := le_of_not_gt hD2
      have hDlt3 : D < Real.log 3 := lt_of_le_of_ne hD3 hEq
      have hVeq : V D x a =
          2 * (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) * S D x a (Real.log 2) -
            2 * (∫ t in Icc (0 : ℝ) D, Real.exp (t / 2) * S D x a t) - b D / 2 * Z D x a := by
        rw [V, primes_two_small hD2' hDlt3]
        have h2 : ArithmeticFunction.vonMangoldt 2 = Real.log 2 :=
          ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)
        simp [h2]
        ring
      rw [hVeq]
      have hb := b_two_abs_small hD2' hDlt3
      have hz := hs.2.2.2
      have htermI := mul_le_mul_of_nonneg_left hI (by norm_num : (0 : ℝ) ≤ 2)
      have htermI' : |2 * (∫ t in Icc (0 : ℝ) D,
          Real.exp (t / 2) * S D x a t)| ≤
          4 * (M D - 1) * W D x a := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        nlinarith [htermI]
      have htermP : |2 * (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) *
          S D x a (Real.log 2)| ≤ W D x a := by
        simpa [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_nonneg (show 0 ≤ ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 by
            have hΛ : ArithmeticFunction.vonMangoldt 2 = Real.log 2 :=
              ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)
            rw [hΛ]
            positivity)] using hprime
      have hsum : |(2 * (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) *
          S D x a (Real.log 2) - 2 * (∫ t in Icc (0 : ℝ) D,
          Real.exp (t / 2) * S D x a t) - b D / 2 * Z D x a)| ≤
          |2 * (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) * S D x a (Real.log 2)| +
          |2 * (∫ t in Icc (0 : ℝ) D, Real.exp (t / 2) * S D x a t)| +
          |b D / 2 * Z D x a| := by
        calc
          _ ≤ |2 * (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) *
              S D x a (Real.log 2) - 2 * (∫ t in Icc (0 : ℝ) D,
              Real.exp (t / 2) * S D x a t)| + |b D / 2 * Z D x a| :=
            by simpa using (abs_sub_le
              (2 * (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) * S D x a (Real.log 2) -
                2 * (∫ t in Icc (0 : ℝ) D, Real.exp (t / 2) * S D x a t))
              0 (b D / 2 * Z D x a))
          _ ≤ _ := add_le_add (by simpa using (abs_sub_le
            (2 * (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) * S D x a (Real.log 2))
            0 (2 * (∫ t in Icc (0 : ℝ) D, Real.exp (t / 2) * S D x a t)))) (le_rfl)
      have hbhalf : |b D / 2| ≤ (29 / 100 : ℝ) := by
        rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
        nlinarith [hb]
      have htermZ' : |b D / 2 * Z D x a| ≤
          (29 / 25 : ℝ) * M D * W D x a := by
        rw [abs_mul]
        calc
          |b D / 2| * |Z D x a| ≤ (29 / 100 : ℝ) * |Z D x a| :=
            mul_le_mul_of_nonneg_right hbhalf (abs_nonneg _)
          _ ≤ (29 / 100 : ℝ) * (4 * M D * W D x a) :=
            mul_le_mul_of_nonneg_left hz (by norm_num)
          _ = (29 / 25 : ℝ) * M D * W D x a := by ring
      have hMW4 : 4 * M D * W D x a ≤ 7 * W D x a := by
        calc
          4 * M D * W D x a = M D * (4 * W D x a) := by ring
          _ ≤ (7 / 4 : ℝ) * (4 * W D x a) :=
            mul_le_mul_of_nonneg_right hM
              (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hs.1)
          _ = 7 * W D x a := by ring
      have hIbound : |2 * (∫ t in Icc (0 : ℝ) D,
            Real.exp (t / 2) * S D x a t)| ≤ 3 * W D x a := by
        calc
          _ ≤ 4 * (M D - 1) * W D x a := htermI'
          _ = 4 * M D * W D x a - 4 * W D x a := by ring
          _ ≤ 7 * W D x a - 4 * W D x a := sub_le_sub_right hMW4 _
          _ = 3 * W D x a := by ring
      have hZbound : |b D / 2 * Z D x a| ≤ (203 / 100 : ℝ) * W D x a := by
        calc
          _ ≤ (29 / 25 : ℝ) * M D * W D x a := htermZ'
          _ = (29 / 100 : ℝ) * (4 * M D * W D x a) := by ring
          _ ≤ (29 / 100 : ℝ) * (7 * W D x a) :=
            mul_le_mul_of_nonneg_left hMW4 (by norm_num)
          _ = (203 / 100 : ℝ) * W D x a := by ring
      nlinarith only [hsum, htermP, hIbound, hZbound, hs.1]

end D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate
