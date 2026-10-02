/- GID: D5/S3/Arith/Robin/EulerValuationMomentComparison
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/EulerValuationMomentComparison
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: An explicit logarithmic comparison of full valuation and prime-support Euler moments. -/

import D5.S3.Arith.GoldenResource.PrefixDeficitKernel
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.SumPrimeReciprocals

set_option autoImplicit false
noncomputable section

namespace D5.S3.Arith.Robin.EulerValuationMomentComparison

open Finset Real
open D5.S3.Arith.GoldenResource.PrefixDeficitKernel

/-- The full geometric-valuation local moment. -/
def localU (p : Nat.Primes) (s : ℝ) : ℝ :=
  (1 - (p : ℝ)⁻¹) * ∑' a : ℕ, S a (p : ℝ)⁻¹ ^ s * ((p : ℝ)⁻¹) ^ a

/-- The local moment recording the prime support. -/
def localW (p : Nat.Primes) (s : ℝ) : ℝ :=
  1 - (p : ℝ)⁻¹ + (p : ℝ)⁻¹ * (1 - (p : ℝ)⁻¹) ^ (-s)

/-- The Euler product of full valuation moments. -/
def U (s : ℝ) : ℝ := ∏' p : Nat.Primes, localU p s

/-- The Euler product of prime-support moments. -/
def W (s : ℝ) : ℝ := ∏' p : Nat.Primes, localW p s

/-- Local convergence, positive Euler products, and their explicit logarithmic gap. -/
theorem result (s : ℝ) (hs : 4 ≤ s) :
    (∀ p : Nat.Primes,
      Summable (fun a : ℕ => S a (p : ℝ)⁻¹ ^ s * ((p : ℝ)⁻¹) ^ a) ∧
      1 ≤ localU p s ∧ localU p s ≤ localW p s) ∧
    Multipliable (fun p : Nat.Primes => localU p s) ∧
    Multipliable (fun p : Nat.Primes => localW p s) ∧
    0 < U s ∧ 0 < W s ∧
    0 ≤ Real.log (W s) - Real.log (U s) ∧
    Real.log (W s) - Real.log (U s) ≤ Real.sqrt s * (Real.log s + 5) := by
  have hs0 : 0 ≤ s := by linarith
  have hlocal (p : Nat.Primes) :
      Summable (fun a : ℕ => S a (p : ℝ)⁻¹ ^ s * ((p : ℝ)⁻¹) ^ a) ∧
      1 ≤ localU p s ∧ localU p s ≤ localW p s ∧
      1 - (p : ℝ)⁻¹ + (p : ℝ)⁻¹ * (1 + (p : ℝ)⁻¹) ^ s ≤ localU p s := by
    let q : ℝ := (p : ℝ)⁻¹
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.prop.two_le
    have hq0 : 0 < q := by dsimp [q]; positivity
    have hqhalf : q ≤ 1 / 2 := by
      simpa only [q, one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2
    have hq1 : q < 1 := by linarith
    have hc : 0 < 1 - q := by linarith
    let P : ℝ := (1 - q) ^ (-s)
    have hP : P = ((1 - q)⁻¹) ^ s := Real.rpow_neg_eq_inv_rpow _ _
    have hSlo (a : ℕ) : 1 ≤ S a q := geometric_prefix_one_le a q hq0.le
    have hSup (a : ℕ) : S a q ≤ (1 - q)⁻¹ := by
      rw [← one_div]
      apply (le_div_iff₀ hc).mpr
      have h := geometric_prefix_mul a q
      nlinarith [pow_nonneg hq0.le (a + 1)]
    have hterm0 (a : ℕ) : 0 ≤ S a q ^ s * q ^ a :=
      mul_nonneg (Real.rpow_nonneg (by linarith [hSlo a]) _) (pow_nonneg hq0.le _)
    have htermup (a : ℕ) : S a q ^ s * q ^ a ≤ P * q ^ a := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hq0.le a)
      rw [hP]
      exact Real.rpow_le_rpow (by linarith [hSlo a]) (hSup a) hs0
    have hgeo : Summable (fun a : ℕ => q ^ a) := summable_geometric_of_lt_one hq0.le hq1
    have hsum : Summable (fun a : ℕ => S a q ^ s * q ^ a) :=
      (hgeo.mul_left P).of_nonneg_of_le hterm0 htermup
    have hgeoeq : ∑' a : ℕ, q ^ a = (1 - q)⁻¹ :=
      tsum_geometric_of_lt_one hq0.le hq1
    have hlo : 1 ≤ localU p s := by
      have hcompare : (∑' a : ℕ, q ^ a) ≤ ∑' a : ℕ, S a q ^ s * q ^ a := by
        apply hgeo.tsum_le_tsum _ hsum
        intro a
        have ht : (1 : ℝ) ≤ S a q ^ s := by
          simpa only [Real.one_rpow] using Real.rpow_le_rpow zero_le_one (hSlo a) hs0
        nlinarith [pow_nonneg hq0.le a]
      change 1 ≤ (1 - q) * ∑' a : ℕ, S a q ^ s * q ^ a
      have heq : (1 - q) * (∑' a : ℕ, q ^ a) = 1 := by
        rw [hgeoeq, mul_inv_cancel₀ hc.ne']
      calc
        1 = (1 - q) * (∑' a : ℕ, q ^ a) := heq.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hcompare hc.le
    have hsplit : (∑' a : ℕ, S a q ^ s * q ^ a) =
        1 + ∑' a : ℕ, S (a + 1) q ^ s * q ^ (a + 1) := by
      simpa [S] using (hsum.sum_add_tsum_nat_add 1).symm
    have htail : Summable (fun a : ℕ => S (a + 1) q ^ s * q ^ (a + 1)) :=
      hsum.comp_injective (fun a b h => Nat.add_right_cancel h)
    have hgeotail : Summable (fun a : ℕ => q ^ (a + 1)) :=
      hgeo.comp_injective (fun a b h => Nat.add_right_cancel h)
    have hgeotaileq : (∑' a : ℕ, q ^ (a + 1)) = q * (1 - q)⁻¹ := by
      simp_rw [pow_succ]
      rw [tsum_mul_right, hgeoeq]
      ring
    have hup : localU p s ≤ localW p s := by
      have ht := htail.tsum_le_tsum (fun a => htermup (a + 1)) (hgeotail.mul_left P)
      rw [tsum_mul_left, hgeotaileq] at ht
      change (1 - q) * (∑' a : ℕ, S a q ^ s * q ^ a) ≤ 1 - q + q * P
      rw [hsplit]
      have hm := mul_le_mul_of_nonneg_left ht hc.le
      field_simp at hm ⊢
      nlinarith
    have hfirst : 1 - q + q * (1 + q) ^ s ≤ localU p s := by
      have hSpair (a : ℕ) : 1 + q ≤ S (a + 1) q := by
        have htwo : (∑ k ∈ range 2, q ^ k) = 1 + q := by simp [sum_range_succ]
        rw [← htwo]
        change (∑ k ∈ range 2, q ^ k) ≤ ∑ k ∈ range (a + 1 + 1), q ^ k
        exact sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
            (fun k _ _ => pow_nonneg hq0.le k)
      have ht : (∑' a : ℕ, (1 + q) ^ s * q ^ (a + 1)) ≤
          ∑' a : ℕ, S (a + 1) q ^ s * q ^ (a + 1) := by
        apply (hgeotail.mul_left ((1 + q) ^ s)).tsum_le_tsum _ htail
        intro a
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (by positivity) (hSpair a) hs0) (pow_nonneg hq0.le _)
      rw [tsum_mul_left, hgeotaileq] at ht
      change 1 - q + q * (1 + q) ^ s ≤ (1 - q) * (∑' a : ℕ, S a q ^ s * q ^ a)
      rw [hsplit]
      have hm := mul_le_mul_of_nonneg_left ht hc.le
      field_simp at hm ⊢
      nlinarith
    exact ⟨hsum, hlo, hup, hfirst⟩
  have hpositive (p : Nat.Primes) : 0 < localU p s ∧ 0 < localW p s := by
    have h := (hlocal p).2
    constructor <;> linarith
  have hlarge (p : Nat.Primes) :
      0 ≤ Real.log (localW p s) - Real.log (localU p s) ∧
      Real.log (localW p s) - Real.log (localU p s) ≤ s / ((p : ℝ) ^ 2 - 1) := by
    let q : ℝ := (p : ℝ)⁻¹
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.prop.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hq0 : 0 < q := by dsimp [q]; positivity
    have hqhalf : q ≤ 1 / 2 := by
      simpa only [q, one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2
    have hq1 : q < 1 := by linarith
    have hc : 0 < 1 - q := by linarith
    have hc2 : 0 < 1 - q ^ 2 := by nlinarith
    let P : ℝ := (1 - q) ^ (-s)
    let Q : ℝ := (1 + q) ^ s
    have hPpos : 0 < P := Real.rpow_pos_of_pos hc _
    have hQpos : 0 < Q := Real.rpow_pos_of_pos (by linarith) _
    have hPQ : Q ≤ P := by
      dsimp [P, Q]
      rw [Real.rpow_neg_eq_inv_rpow]
      apply Real.rpow_le_rpow (by linarith) _ hs0
      rw [← one_div, le_div_iff₀ hc]
      nlinarith
    have hquot : localW p s / localU p s ≤ P / Q := by
      apply (div_le_div_iff₀ (hpositive p).1 hQpos).mpr
      have hlo := (hlocal p).2.2.2
      change 1 - q + q * Q ≤ localU p s at hlo
      have ht := mul_le_mul_of_nonneg_right hlo hPpos.le
      change (1 - q + q * P) * Q ≤ P * localU p s
      nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hPQ)]
    have hlog := Real.log_le_log (div_pos (hpositive p).2 (hpositive p).1) hquot
    rw [Real.log_div (hpositive p).2.ne' (hpositive p).1.ne',
      Real.log_div hPpos.ne' hQpos.ne'] at hlog
    have hlogs : Real.log P - Real.log Q = -s * Real.log (1 - q ^ 2) := by
      dsimp [P, Q]
      rw [Real.log_rpow hc, Real.log_rpow (by linarith : 0 < 1 + q)]
      have heq : 1 - q ^ 2 = (1 - q) * (1 + q) := by ring
      rw [heq, Real.log_mul hc.ne' (by linarith : 1 + q ≠ 0)]
      ring
    have hlogtail : -Real.log (1 - q ^ 2) ≤ q ^ 2 / (1 - q ^ 2) := by
      have h := Real.one_sub_inv_le_log_of_pos hc2
      have heq : (1 - q ^ 2)⁻¹ - 1 = q ^ 2 / (1 - q ^ 2) := by
        field_simp
        ring
      linarith
    have hden : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
    have htailid : q ^ 2 / (1 - q ^ 2) = 1 / ((p : ℝ) ^ 2 - 1) := by
      dsimp [q]
      field_simp
    constructor
    · exact sub_nonneg.mpr (Real.log_le_log (hpositive p).1 (hlocal p).2.2.1)
    · calc
        Real.log (localW p s) - Real.log (localU p s) ≤
            -s * Real.log (1 - q ^ 2) := hlog.trans_eq hlogs
        _ ≤ s * (q ^ 2 / (1 - q ^ 2)) := by nlinarith
        _ = s / ((p : ℝ) ^ 2 - 1) := by rw [htailid]; ring
  have hsmall (p : Nat.Primes) :
      Real.exp (-2) / (2 * s) * (1 - (p : ℝ)⁻¹) ^ (-s) ≤ localU p s ∧
      Real.log (localW p s) - Real.log (localU p s) ≤ Real.log s + Real.log 2 + 2 := by
    let q : ℝ := (p : ℝ)⁻¹
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.prop.two_le
    have hq0 : 0 < q := by dsimp [q]; positivity
    have hqhalf : q ≤ 1 / 2 := by
      simpa only [q, one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2
    have hq1 : q < 1 := by linarith
    have hc : 0 < 1 - q := by linarith
    have hspos : 0 < s := by linarith
    have hsinv : 0 < s⁻¹ := inv_pos.mpr hspos
    have hsone : s⁻¹ ≤ 1 := (inv_le_one₀ hspos).mpr (by linarith)
    obtain ⟨a, ha, ha'⟩ := exists_nat_pow_near_of_lt_one hsinv hsone hq0 hq1
    let u : ℝ := q ^ (a + 1)
    have hu0 : 0 ≤ u := pow_nonneg hq0.le _
    have huinv : u ≤ s⁻¹ := ha.le
    have huquarter : u ≤ 1 / 4 := by
      exact huinv.trans (by simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 4) hs)
    have huc : 0 < 1 - u := by linarith
    have hsule : s * u ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left huinv hspos.le
      simpa only [mul_inv_cancel₀ hspos.ne'] using h
    have hulog : -2 * u ≤ Real.log (1 - u) := by
      have h := Real.one_sub_inv_le_log_of_pos huc
      have hi : (1 - u)⁻¹ ≤ 1 + 2 * u := by
        rw [← one_div, div_le_iff₀ huc]
        nlinarith
      linarith
    have hpower : Real.exp (-2) ≤ (1 - u) ^ s := by
      rw [Real.rpow_def_of_pos huc]
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_right hulog hspos.le
      nlinarith
    have hgeom : S a q = (1 - u) / (1 - q) := by
      apply (eq_div_iff hc.ne').mpr
      simpa only [mul_comm] using geometric_prefix_mul a q
    have hpowid : S a q ^ s = (1 - u) ^ s * (1 - q) ^ (-s) := by
      rw [hgeom, Real.div_rpow huc.le hc.le, Real.rpow_neg hc.le, div_eq_mul_inv]
    have hsum := (hlocal p).1
    have hterm : S a q ^ s * q ^ a ≤ ∑' b : ℕ, S b q ^ s * q ^ b := by
      exact hsum.le_tsum a (fun b _ => by
        apply mul_nonneg _ (pow_nonneg hq0.le _)
        exact Real.rpow_nonneg (by linarith [geometric_prefix_one_le b q hq0.le]) _)
    have hU : Real.exp (-2) / (2 * s) * (1 - q) ^ (-s) ≤ localU p s := by
      have hPpos : 0 ≤ (1 - q) ^ (-s) := Real.rpow_nonneg hc.le _
      have hexp : 0 ≤ Real.exp (-2) := (Real.exp_pos _).le
      have htermlo := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpower hPpos) (pow_nonneg hq0.le a)
      rw [← hpowid] at htermlo
      have hcoefficient : Real.exp (-2) / (2 * s) ≤ (1 - q) * Real.exp (-2) * q ^ a := by
        have hmul := mul_le_mul_of_nonneg_left ha' (mul_nonneg hc.le hexp)
        have hhalf : (1 / 2 : ℝ) ≤ 1 - q := by linarith
        have hmul' := mul_le_mul_of_nonneg_right hhalf (mul_nonneg hexp hsinv.le)
        calc
          Real.exp (-2) / (2 * s) = (1 / 2) * (Real.exp (-2) * s⁻¹) := by ring
          _ ≤ (1 - q) * (Real.exp (-2) * s⁻¹) := hmul'
          _ ≤ (1 - q) * Real.exp (-2) * q ^ a := by nlinarith
      have htermlo' := mul_le_mul_of_nonneg_left htermlo hc.le
      have hlast := mul_le_mul_of_nonneg_left hterm hc.le
      change _ ≤ (1 - q) * ∑' b : ℕ, S b q ^ s * q ^ b
      nlinarith [mul_le_mul_of_nonneg_right hcoefficient hPpos]
    have hW : localW p s ≤ (1 - q) ^ (-s) := by
      have hPone : (1 : ℝ) ≤ (1 - q) ^ (-s) := by
        rw [Real.rpow_neg_eq_inv_rpow]
        apply Real.one_le_rpow _ hs0
        exact (one_le_inv₀ hc).mpr (by linarith)
      change 1 - q + q * (1 - q) ^ (-s) ≤ (1 - q) ^ (-s)
      nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hPone)]
    have hquot : localW p s / localU p s ≤ 2 * s * Real.exp 2 := by
      apply (div_le_iff₀ (hpositive p).1).mpr
      have h := mul_le_mul_of_nonneg_left hU (by positivity : 0 ≤ 2 * s * Real.exp 2)
      have hcancel : (2 * s * Real.exp 2) *
          (Real.exp (-2) / (2 * s) * (1 - q) ^ (-s)) = (1 - q) ^ (-s) := by
        rw [Real.exp_neg]
        field_simp
      rw [hcancel] at h
      nlinarith
    have hlog := Real.log_le_log (div_pos (hpositive p).2 (hpositive p).1) hquot
    rw [Real.log_div (hpositive p).2.ne' (hpositive p).1.ne'] at hlog
    have hlogeq : Real.log (2 * s * Real.exp 2) = Real.log s + Real.log 2 + 2 := by
      rw [Real.log_mul (by positivity : 2 * s ≠ 0) (Real.exp_ne_zero 2),
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hspos.ne', Real.log_exp]
      ring
    exact ⟨hU, hlog.trans_eq hlogeq⟩
  have hsquare : Summable (fun p : Nat.Primes => ((p : ℝ)⁻¹) ^ 2) := by
    have h := (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).comp_injective
      (show Function.Injective (fun p : Nat.Primes => (p : ℕ)) from Subtype.val_injective)
    simpa only [Function.comp_def, one_div, inv_pow] using h
  have hWminus (p : Nat.Primes) :
      0 ≤ localW p s - 1 ∧
      localW p s - 1 ≤ 2 * (Real.exp s - 1) * ((p : ℝ)⁻¹) ^ 2 := by
    let q : ℝ := (p : ℝ)⁻¹
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.prop.two_le
    have hq0 : 0 < q := by dsimp [q]; positivity
    have hqhalf : q ≤ 1 / 2 := by
      simpa only [q, one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2
    have hc : 0 < 1 - q := by linarith
    have hlog : -Real.log (1 - q) ≤ 2 * q := by
      have h := Real.one_sub_inv_le_log_of_pos hc
      have hi : (1 - q)⁻¹ ≤ 1 + 2 * q := by
        rw [← one_div, div_le_iff₀ hc]
        nlinarith
      linarith
    have hexp : Real.exp (2 * q * s) ≤ 1 + 2 * q * (Real.exp s - 1) := by
      have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ s)
        (show 0 ≤ 1 - 2 * q by linarith) (show 0 ≤ 2 * q by positivity)
        (show (1 - 2 * q) + 2 * q = 1 by ring)
      simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
      nlinarith
    have hP : (1 - q) ^ (-s) ≤ 1 + 2 * q * (Real.exp s - 1) := by
      rw [Real.rpow_def_of_pos hc]
      apply (Real.exp_le_exp.mpr ?_).trans hexp
      nlinarith
    constructor
    · have h := (hlocal p).2
      linarith
    · change 1 - q + q * (1 - q) ^ (-s) - 1 ≤ 2 * (Real.exp s - 1) * q ^ 2
      nlinarith [mul_le_mul_of_nonneg_left hP hq0.le]
  have hsumWminus : Summable (fun p : Nat.Primes => localW p s - 1) :=
    (hsquare.mul_left (2 * (Real.exp s - 1))).of_nonneg_of_le
      (fun p => (hWminus p).1) (fun p => (hWminus p).2)
  have hlogW : Summable (fun p : Nat.Primes => Real.log (localW p s)) := by
    simpa only [add_sub_cancel] using Real.summable_log_one_add_of_summable hsumWminus
  have hlogU : Summable (fun p : Nat.Primes => Real.log (localU p s)) := by
    apply hlogW.of_nonneg_of_le
    · intro p
      exact Real.log_nonneg (hlocal p).2.1
    · intro p
      exact Real.log_le_log (hpositive p).1 (hlocal p).2.2.1
  have hmU : Multipliable (fun p : Nat.Primes => localU p s) :=
    Real.multipliable_of_summable_log (fun p => (hpositive p).1) hlogU
  have hmW : Multipliable (fun p : Nat.Primes => localW p s) :=
    Real.multipliable_of_summable_log (fun p => (hpositive p).2) hlogW
  have heU : U s = Real.exp (∑' p : Nat.Primes, Real.log (localU p s)) :=
    (Real.rexp_tsum_eq_tprod (fun p => (hpositive p).1) hlogU).symm
  have heW : W s = Real.exp (∑' p : Nat.Primes, Real.log (localW p s)) :=
    (Real.rexp_tsum_eq_tprod (fun p => (hpositive p).2) hlogW).symm
  have hsumloss : Summable (fun p : Nat.Primes => Real.log (localW p s) - Real.log (localU p s)) :=
    hlogW.sub hlogU
  have hloggap : Real.log (W s) - Real.log (U s) =
      ∑' p : Nat.Primes, (Real.log (localW p s) - Real.log (localU p s)) := by
    rw [heW, heU, Real.log_exp, Real.log_exp, hlogW.tsum_sub hlogU]
  refine ⟨fun p => ⟨(hlocal p).1, (hlocal p).2.1, (hlocal p).2.2.1⟩,
    hmU, hmW, by rw [heU]; positivity, by rw [heW]; positivity, ?_, ?_⟩
  · rw [hloggap]
    exact tsum_nonneg (fun p => (hlarge p).1)
  · sorry

end D5.S3.Arith.Robin.EulerValuationMomentComparison
