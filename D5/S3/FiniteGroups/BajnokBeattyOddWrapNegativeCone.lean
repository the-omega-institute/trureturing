/- GID: D5/S3/FiniteGroups/BajnokBeattyOddWrapNegativeCone
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattyOddWrapNegativeCone
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Finite logarithmic products give the strict negative cone 25t at most 24p. -/

import D5.S3.FiniteGroups.BajnokBeattyOddWrapPositiveCone
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.FiniteGroups.BajnokBeattyOddWrapNegativeCone

open BajnokBeattyOddWrapPositiveCone BajnokBeattyOddWrapSingleCrossing
open BajnokBeattyOddWrapReturnCounts
open Finset

private theorem two_lt_exp_twentyfive_thirtysixths :
    (2 : ℝ) < Real.exp (25/36 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (x := (25/36 : ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith only [h]

/-- The left binomial alone dominates twice the middle one throughout the cone. -/
private theorem left_binomial_dominates (p t : ℕ) (hp3 : 3 ≤ p) (ht2 : 2 ≤ t)
    (hcone : 25*t ≤ 24*p) :
    let n := p*(6*t-1)
    2*Nat.choose n (3*p*t+p) < Nat.choose n (3*p*t) := by
  let P : ℝ := p
  let T : ℝ := t
  let a : ℕ := 3*p*t
  let n : ℕ := p*(6*t-1)
  let A : ℝ := Nat.choose n a
  let B : ℝ := Nat.choose n (a+p)
  have hP3 : 3 ≤ P := by dsimp [P]; exact_mod_cast hp3
  have hT2 : 2 ≤ T := by dsimp [T]; exact_mod_cast ht2
  have hP : 0 < P := by linarith
  have hconeR : 25*T ≤ 24*P := by dsimp [P, T]; exact_mod_cast hcone
  have haR : (a : ℝ) = 3*P*T := by dsimp [a, P, T]; push_cast; ring
  have hnR : (n : ℝ) = 6*P*T-P := by
    dsimp [n]
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ 6*t)]
    push_cast
    dsimp [P, T]
    ring
  have hPT : 0 ≤ P*(T-2) := mul_nonneg hP.le (by linarith)
  have hab : a+p ≤ n := by
    have hh : ((a+p : ℕ) : ℝ) ≤ (n : ℝ) := by
      push_cast
      rw [haR, hnR]
      change 3*P*T+P ≤ 6*P*T-P
      nlinarith only [hPT, hP.le]
    exact_mod_cast hh
  have hA : 0 < A := by dsimp [A]; exact_mod_cast Nat.choose_pos (by omega : a ≤ n)
  have hB : 0 < B := by dsimp [B]; exact_mod_cast Nat.choose_pos hab
  let R : ℝ := (n : ℝ)+1
  have hR : 0 < R := by dsimp [R]; positivity
  let x (i : ℕ) : ℝ := (P+2*(i : ℝ)+1)/R
  have hx (i : ℕ) (hi : i ∈ Finset.range p) : 0 ≤ x i ∧ x i < 1 := by
    have hiN : i+1 ≤ p := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
    have hiR : (i : ℝ)+1 ≤ P := by dsimp [P]; exact_mod_cast hiN
    constructor
    · dsimp [x]; positivity
    · dsimp [x]
      apply (div_lt_iff₀ hR).2
      dsimp [R]
      rw [hnR]
      nlinarith only [hiR, hPT, hP3]
  have hsumI : (∑ i ∈ Finset.range p, (i : ℝ))*2 = P*(P-1) := by
    have h := congrArg (fun z : ℕ ↦ (z : ℝ)) (Finset.sum_range_id_mul_two p)
    simpa only [Nat.cast_mul, Nat.cast_sum,
      Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_ofNat, Nat.cast_one] using h
  have hsumd : (∑ i ∈ Finset.range p, (P+2*(i : ℝ)+1)) = 2*P^2 := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, ← Finset.mul_sum]
    change P*P+2*(∑ i ∈ Finset.range p, (i : ℝ))+P*1 = 2*P^2
    nlinarith only [hsumI]
  have hxsum : (∑ i ∈ Finset.range p, x i) = 2*P^2/R := by
    dsimp only [x]
    rw [← Finset.sum_div, hsumd]
  have hratio : A/B = ∏ i ∈ Finset.range p, (1+x i)/(1-x i) := by
    have hh := choose_ratio_prod n a p hab
    change A/B = _ at hh
    rw [hh]
    apply Finset.prod_congr rfl
    intro i hi
    have hiN : i+1 ≤ p := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
    have hiR : (i : ℝ)+1 ≤ P := by dsimp [P]; exact_mod_cast hiN
    have hden : 0 < (n : ℝ)-(a : ℝ)-(i : ℝ) := by
      rw [hnR, haR]
      nlinarith only [hiR, hPT, hP3]
    have hxm : 1-x i ≠ 0 := by linarith [(hx i hi).2]
    apply (div_eq_div_iff hden.ne' hxm).2
    dsimp only [x]
    have hdiv := div_mul_cancel₀ (P+2*(i : ℝ)+1) hR.ne'
    dsimp only [R] at hdiv ⊢
    rw [hnR] at hdiv
    rw [haR, hnR]
    linear_combination -hdiv
  have hfactor (i : ℕ) (hi : i ∈ Finset.range p) :
      2*x i ≤ Real.log ((1+x i)/(1-x i)) := by
    have hh := Real.sum_range_le_log_div (hx i hi).1 (hx i hi).2 1
    norm_num [Finset.sum_range_succ] at hh
    linarith only [hh]
  have hlog : 4*P^2/R ≤ Real.log (A/B) := by
    rw [hratio, Real.log_prod (fun i hi ↦
      (div_pos (by linarith [(hx i hi).1]) (by linarith [(hx i hi).2])).ne')]
    have hh := Finset.sum_le_sum hfactor
    rw [← Finset.mul_sum, hxsum] at hh
    calc
      4*P^2/R = 2*(2*P^2/R) := by ring
      _ ≤ _ := hh
  have hbound : (25/36 : ℝ) ≤ 4*P^2/R := by
    apply (le_div_iff₀ hR).2
    dsimp [R]
    rw [hnR]
    have hc : 0 ≤ P*(24*P-25*T) := mul_nonneg hP.le (by linarith)
    nlinarith only [hc, hP3]
  have hloglower : (25/36 : ℝ) ≤ Real.log (A/B) := hbound.trans hlog
  have hratioPos : 0 < A/B := div_pos hA hB
  have hexp : Real.exp (25/36 : ℝ) ≤ A/B :=
    (Real.le_log_iff_exp_le hratioPos).mp hloglower
  have hquot : (2 : ℝ) < A/B := two_lt_exp_twentyfive_thirtysixths.trans_le hexp
  have hh : 2*B < A := (lt_div_iff₀ hB).mp hquot
  change 2*(Nat.choose n (a+p) : ℝ) < (Nat.choose n a : ℝ) at hh
  exact_mod_cast hh

/-- The complete original return counts have negative defect whenever
25t<=24p, for every odd integer p>=3 and integer t>=2. -/
theorem actual_negative_odd_wrap_cone (p t : ℤ) (hp3 : 3 ≤ p) (hpo : Odd p)
    (ht2 : 2 ≤ t) (hcone : 25*t ≤ 24*p) :
    (original_return_pair p t).2 < (original_return_pair p t).1 := by
  let P : ℕ := p.toNat
  let T : ℕ := t.toNat
  let N : ℕ := P*(6*T-1)
  have hP : (P : ℤ) = p := Int.toNat_of_nonneg (by omega)
  have hT : (T : ℤ) = t := Int.toNat_of_nonneg (by omega)
  have hP3 : 3 ≤ P := by omega
  have hT2 : 2 ≤ T := by omega
  have hconeN : 25*T ≤ 24*P := by omega
  have hb : 2*Nat.choose N (3*P*T+P) < Nat.choose N (3*P*T) :=
    left_binomial_dominates P T hP3 hT2 hconeN
  have hc := actual_odd_wrap_counts p t hp3 hpo ht2
  have hhalf1 : p*((6*t-1)+1)/2 = 3*p*t := by
    have hh : p*((6*t-1)+1) = 2*(3*p*t) := by ring
    omega
  have hhalf3 : p*((6*t-1)+3)/2 = 3*p*t+p := by
    have hh : p*((6*t-1)+3) = 2*(3*p*t+p) := by ring
    omega
  have hhalf9 : p*((6*t-1)+9)/2 = 3*p*t+4*p := by
    have hh : p*((6*t-1)+9) = 2*(3*p*t+4*p) := by ring
    omega
  have hN : (p*(6*t-1)).toNat = N := by
    have hh : p*(6*t-1) = (N : ℤ) := by
      simp only [N, Nat.cast_mul, Nat.cast_sub (show 1 ≤ 6*T by omega),
        Nat.cast_ofNat, Nat.cast_one, hP, hT]
    exact (congrArg Int.toNat hh).trans (Int.toNat_natCast _)
  have hI1 : (3*p*t).toNat = 3*P*T := by
    have hh : 3*p*t = ((3*P*T : ℕ) : ℤ) := by rw [← hP, ← hT]; push_cast <;> ring
    exact (congrArg Int.toNat hh).trans (Int.toNat_natCast _)
  have hI3 : (3*p*t+p).toNat = 3*P*T+P := by
    have hh : 3*p*t+p = ((3*P*T+P : ℕ) : ℤ) := by rw [← hP, ← hT]; push_cast <;> ring
    exact (congrArg Int.toNat hh).trans (Int.toNat_natCast _)
  have hI9 : (3*p*t+4*p).toNat = 3*P*T+4*P := by
    have hh : 3*p*t+4*p = ((3*P*T+4*P : ℕ) : ℤ) := by rw [← hP, ← hT]; push_cast <;> ring
    exact (congrArg Int.toNat hh).trans (Int.toNat_natCast _)
  have hW19 : (original_return_pair p t).1 =
      2*(Nat.choose N (3*P*T)+Nat.choose N (3*P*T+4*P)) := by
    calc
      (original_return_pair p t).1 =
          2*(Nat.choose (p*(6*t-1)).toNat (p*((6*t-1)+1)/2).toNat +
            Nat.choose (p*(6*t-1)).toNat (p*((6*t-1)+9)/2).toNat) := hc.1
      _ = _ := by rw [hhalf1, hhalf9, hN, hI1, hI9]
  have hW33 : (original_return_pair p t).2 = 4*Nat.choose N (3*P*T+P) := by
    calc
      (original_return_pair p t).2 =
          4*Nat.choose (p*(6*t-1)).toNat (p*((6*t-1)+3)/2).toNat := hc.2
      _ = _ := by rw [hhalf3, hN, hI3]
  rw [hW19, hW33]
  omega

end D5.S3.FiniteGroups.BajnokBeattyOddWrapNegativeCone
