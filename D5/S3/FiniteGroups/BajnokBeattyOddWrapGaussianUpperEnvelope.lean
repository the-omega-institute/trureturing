/- GID: D5/S3/FiniteGroups/BajnokBeattyOddWrapGaussianUpperEnvelope
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattyOddWrapGaussianUpperEnvelope
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A finite cubic logarithmic remainder bounds the original Gaussian ratio from above. -/

import D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianEnvelope
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianUpperEnvelope

open BajnokBeattyOddWrapPositiveCone BajnokBeattyOddWrapSingleCrossing
open BajnokBeattyOddWrapReturnCounts BajnokBeattyOddWrapGaussianEnvelope
open Finset

theorem choose_ratio_centered_prod (n k r : ℕ) (q R : ℝ)
    (hkr : k+r ≤ n) (hR : R = (n : ℝ)+1) (hq : q = 2*(k : ℝ)-(n : ℝ)) :
    (Nat.choose n k : ℝ)/(Nat.choose n (k+r) : ℝ) =
      ∏ i ∈ Finset.range r,
        (1+(q+2*(i : ℝ)+1)/R)/(1-(q+2*(i : ℝ)+1)/R) := by
  rw [choose_ratio_prod n k r hkr]
  have hRpos : 0 < R := by rw [hR]; positivity
  apply Finset.prod_congr rfl
  intro i hi
  have hki : k+i < n := by
    have hi' := Finset.mem_range.mp hi
    omega
  have hkiR : (k : ℝ)+(i : ℝ) < (n : ℝ) := by exact_mod_cast hki
  have hden : 0 < (n : ℝ)-(k : ℝ)-(i : ℝ) := by linarith only [hkiR]
  have hx1 : (q+2*(i : ℝ)+1)/R < 1 := by
    apply (div_lt_iff₀ hRpos).2
    rw [hq, hR]
    linarith only [hden]
  apply (div_eq_div_iff hden.ne' (show 1-(q+2*(i : ℝ)+1)/R ≠ 0 by
    linarith only [hx1])).2
  have hdiv := div_mul_cancel₀ (q+2*(i : ℝ)+1) hRpos.ne'
  rw [hq, hR] at hdiv ⊢
  linear_combination -hdiv

private theorem log_lower_linear {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    2*x ≤ Real.log ((1+x)/(1-x)) := by
  have h := Real.sum_range_le_log_div hx hx1 1
  norm_num [Finset.sum_range_succ] at h
  linarith only [h]

theorem log_upper_small {x : ℝ} (hx : 0 ≤ x) (hx2 : x ≤ 3/28) :
    Real.log ((1+x)/(1-x)) ≤ 2*x+((2/3)+(18/775))*x^3 := by
  have hx1 : x < 1 := by linarith only [hx2]
  have hxsq : x^2 ≤ 9/784 := by
    have h := pow_le_pow_left₀ hx hx2 2
    norm_num at h
    exact h
  have hden : 0 < 1-x^2 := by linarith only [hxsq]
  have hrem : x^5/(1-x^2) ≤ (9/775)*x^3 := by
    apply (div_le_iff₀ hden).2
    have hmul : 0 ≤ x^3*(9/784-x^2) :=
      mul_nonneg (pow_nonneg hx 3) (sub_nonneg.mpr hxsq)
    nlinarith only [hmul]
  have h := Real.log_div_le_sum_range_add hx hx1 2
  norm_num [Finset.sum_range_succ] at h
  linarith only [h, hrem]

private theorem exp_one_tenth_lt : Real.exp (1/10 : ℝ) < 111/100 := by
  have h := Real.exp_bound' (x := (1/10 : ℝ)) (by norm_num) (by norm_num)
    (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith only [h]

theorem exp_three_quarters_lt : Real.exp (3/4 : ℝ) < 9/4 := by
  have h := Real.exp_bound' (x := (3/4 : ℝ)) (by norm_num) (by norm_num)
    (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith only [h]

private theorem exp_small_secant {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1/10) :
    Real.exp δ ≤ 1+(11/10)*δ := by
  have ha : 0 ≤ 1-10*δ := by linarith only [hδ]
  have hb : 0 ≤ 10*δ := by linarith only [hδ0]
  have hab : (1-10*δ)+10*δ = 1 := by ring
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1/10 : ℝ))
    ha hb hab
  have hid : (1-10*δ)*0+(10*δ)*(1/10) = δ := by ring
  simp only [smul_eq_mul, hid, Real.exp_zero, mul_one] at h
  have hcoef := mul_nonneg hδ0 (sub_nonneg.mpr exp_one_tenth_lt.le)
  nlinarith only [h, hcoef]

private theorem binomial_gaussian_upper_envelope (p t : ℕ) (hp5 : 5 ≤ p) (ht2 : 2 ≤ t)
    (htp : t ≤ p) (hband : 24*p ≤ 25*t) :
    let n := p*(6*t-1)
    let s : ℝ := 4*(p : ℝ)^2/((n : ℝ)+1)
    ((Nat.choose n (3*p*t) : ℝ)+Nat.choose n (3*p*t+4*p))/
        (Nat.choose n (3*p*t+p) : ℝ) <
      Real.exp s+Real.exp (-9*s)+1/(10*(p : ℝ)^2) := by
  let P : ℝ := p
  let T : ℝ := t
  let a : ℕ := 3*p*t
  let n : ℕ := p*(6*t-1)
  let A : ℝ := Nat.choose n a
  let B : ℝ := Nat.choose n (a+p)
  let D : ℝ := Nat.choose n (a+4*p)
  let R : ℝ := (n : ℝ)+1
  let s : ℝ := 4*P^2/R
  have hP5 : 5 ≤ P := by dsimp [P]; exact_mod_cast hp5
  have hP : 0 < P := by linarith only [hP5]
  have hPsq : 0 < P^2 := pow_pos hP 2
  have hT2 : 2 ≤ T := by dsimp [T]; exact_mod_cast ht2
  have hbandR : 24*P ≤ 25*T := by dsimp [P, T]; exact_mod_cast hband
  have haR : (a : ℝ) = 3*P*T := by dsimp [a, P, T]; push_cast; ring
  have hnR : (n : ℝ) = 6*P*T-P := by
    dsimp [n]
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ 6*t)]
    push_cast
    dsimp [P, T]
    ring
  have hPT : 0 ≤ P*(T-2) := mul_nonneg hP.le (by linarith only [hT2])
  have had : a+4*p ≤ n := by
    have hh : ((a+4*p : ℕ) : ℝ) ≤ (n : ℝ) := by
      push_cast
      rw [haR, hnR]
      change 3*P*T+4*P ≤ 6*P*T-P
      nlinarith only [hPT, hP.le]
    exact_mod_cast hh
  have hA : 0 < A := by dsimp [A]; exact_mod_cast Nat.choose_pos (by omega : a ≤ n)
  have hB : 0 < B := by dsimp [B]; exact_mod_cast Nat.choose_pos (by omega : a+p ≤ n)
  have hD : 0 < D := by dsimp [D]; exact_mod_cast Nat.choose_pos had
  have hR : 0 < R := by dsimp [R]; positivity
  have hRlow : 11*P+1 ≤ R := by
    dsimp [R]
    rw [hnR]
    nlinarith only [hPT]
  have hRquad : (28/5)*P^2 ≤ R := by
    have hprod : 0 ≤ P*(25*T-24*P) :=
      mul_nonneg hP.le (sub_nonneg.mpr hbandR)
    have hres : 0 ≤ (P-5)*(4*P-5) :=
      mul_nonneg (by linarith only [hP5]) (by linarith only [hP5])
    dsimp [R]
    rw [hnR]
    nlinarith only [hprod, hres]
  have hRcube : ((28/5)*P^2)^3 ≤ R^3 :=
    pow_le_pow_left₀ (by positivity) hRquad 3
  have hs5 : s ≤ 5/7 := by
    dsimp [s]
    apply (div_le_iff₀ hR).2
    nlinarith only [hRquad]
  have hs34 : s < 3/4 := by linarith only [hs5]
  let x (i : ℕ) : ℝ := (P+2*(i : ℝ)+1)/R
  let y (j : ℕ) : ℝ := (3*P+2*(j : ℝ)+1)/R
  have hxP (i : ℕ) (hi : i ∈ Finset.range p) : x i ≤ 15/(28*P) := by
    have hiR : (i : ℝ)+1 ≤ P := by
      dsimp [P]
      exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hi)
    have hnum : P+2*(i : ℝ)+1 ≤ 3*P := by linarith only [hiR]
    have hmul := mul_le_mul_of_nonneg_left hnum (show 0 ≤ 28*P by positivity)
    dsimp only [x]
    apply (div_le_div_iff₀ hR (show 0 < 28*P by positivity)).2
    nlinarith only [hmul, hRquad]
  have hx (i : ℕ) (hi : i ∈ Finset.range p) : 0 ≤ x i ∧ x i ≤ 3/28 := by
    constructor
    · dsimp [x]; positivity
    · apply (hxP i hi).trans
      apply (div_le_iff₀ (show 0 < 28*P by positivity)).2
      linarith only [hP5]
  have hy (j : ℕ) (hj : j ∈ Finset.range (3*p)) : 0 ≤ y j ∧ y j ≤ 9/11 := by
    have hjR : (j : ℝ)+1 ≤ 3*P := by
      dsimp [P]
      exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hj)
    constructor
    · dsimp [y]; positivity
    · dsimp [y]
      apply (div_le_iff₀ hR).2
      linarith only [hjR, hRlow]
  have hxp (i : ℕ) (hi : i ∈ Finset.range p) : 0 < (1+x i)/(1-x i) :=
    div_pos (by linarith [(hx i hi).1]) (by linarith [(hx i hi).2])
  have hyp (j : ℕ) (hj : j ∈ Finset.range (3*p)) : 0 < (1+y j)/(1-y j) :=
    div_pos (by linarith [(hy j hj).1]) (by linarith [(hy j hj).2])
  have hAB : A/B = ∏ i ∈ Finset.range p, (1+x i)/(1-x i) := by
    apply choose_ratio_centered_prod n a p P R (by omega) rfl
    rw [haR, hnR]
    ring
  have hBD : B/D = ∏ j ∈ Finset.range (3*p), (1+y j)/(1-y j) := by
    have hq : 3*P = 2*((a+p : ℕ) : ℝ)-(n : ℝ) := by
      push_cast
      rw [haR, hnR]
      change 3*P = 2*(3*P*T+P)-(6*P*T-P)
      ring
    have hh := choose_ratio_centered_prod n (a+p) (3*p) (3*P) R
      (by omega : a+p+3*p ≤ n) rfl hq
    rw [show a+p+3*p = a+4*p by omega] at hh
    exact hh
  have h3P : ((3*p : ℕ) : ℝ) = 3*P := by dsimp [P]; push_cast; ring
  have hxsum : (∑ i ∈ Finset.range p, x i) = 2*P^2/R := by
    dsimp only [x]
    rw [← Finset.sum_div, sum_linear]
    change P*(P+P)/R = 2*P^2/R
    ring
  have hysum : (∑ j ∈ Finset.range (3*p), y j) = 18*P^2/R := by
    dsimp only [y]
    rw [← Finset.sum_div, sum_linear, h3P]
    ring
  let X3 : ℝ := ∑ i ∈ Finset.range p, (x i)^3
  have hX3 : X3 = 2*P^2*(5*P^2-1)/R^3 := by
    dsimp only [X3, x]
    simp_rw [div_pow]
    rw [← Finset.sum_div, sum_cubic]
    change P*(P+P)*((P+P)^2+P^2-1)/R^3 = _
    ring
  have hXtimes : X3*P^2 ≤ 1250/21952 := by
    rw [hX3, div_mul_eq_mul_div]
    apply (div_le_iff₀ (pow_pos hR 3)).2
    nlinarith only [hRcube, sq_nonneg (P^2)]
  let L : ℝ := Real.log (A/B)
  let M : ℝ := Real.log (B/D)
  have hlogL : L = ∑ i ∈ Finset.range p, Real.log ((1+x i)/(1-x i)) := by
    dsimp only [L]
    rw [hAB, Real.log_prod (fun i hi ↦ (hxp i hi).ne')]
  have hlogM : M = ∑ j ∈ Finset.range (3*p), Real.log ((1+y j)/(1-y j)) := by
    dsimp only [M]
    rw [hBD, Real.log_prod (fun j hj ↦ (hyp j hj).ne')]
  have hLlo : s ≤ L := by
    have hsum := Finset.sum_le_sum (fun i hi ↦
      log_lower_linear (hx i hi).1 (by linarith [(hx i hi).2]))
    rw [← hlogL, ← Finset.mul_sum, hxsum] at hsum
    rw [show 2*(2*P^2/R) = 4*P^2/R by ring] at hsum
    exact hsum
  have hLhi : L ≤ s+((2/3)+(18/775))*X3 := by
    have hsum := Finset.sum_le_sum (fun i hi ↦ log_upper_small (hx i hi).1 (hx i hi).2)
    rw [← hlogL] at hsum
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hxsum] at hsum
    change L ≤ 2*(2*P^2/R)+((2/3)+(18/775))*X3 at hsum
    rw [show 2*(2*P^2/R) = 4*P^2/R by ring] at hsum
    exact hsum
  have hMlo : 9*s ≤ M := by
    have hsum := Finset.sum_le_sum (fun j hj ↦
      log_lower_linear (hy j hj).1 (by linarith [(hy j hj).2]))
    rw [← hlogM, ← Finset.mul_sum, hysum] at hsum
    rw [show 2*(18*P^2/R) = 9*(4*P^2/R) by ring] at hsum
    exact hsum
  let δ : ℝ := L-s
  have hδ0 : 0 ≤ δ := sub_nonneg.mpr hLlo
  have hδupper : δ ≤ ((2/3)+(18/775))*X3 := by dsimp only [δ]; linarith only [hLhi]
  have hδtimes : δ*P^2 ≤ 10025/255192 := by
    have hh := mul_le_mul_of_nonneg_right hδupper hPsq.le
    nlinarith only [hh, hXtimes]
  have hδbound : δ ≤ 1/(25*P^2) := by
    apply (le_div_iff₀ (show 0 < 25*P^2 by positivity)).2
    nlinarith only [hδtimes]
  have hδsmall : δ ≤ 1/625 := by
    apply hδbound.trans
    apply (div_le_iff₀ (show 0 < 25*P^2 by positivity)).2
    nlinarith only [sq_nonneg (P-5), hP5]
  have hexpδ : Real.exp δ ≤ 1+(11/10)*δ :=
    exp_small_secant hδ0 (by linarith only [hδsmall])
  have hexps : Real.exp s < 9/4 :=
    (Real.exp_lt_exp.mpr hs34).trans exp_three_quarters_lt
  have hABexp : A/B = Real.exp s*Real.exp δ := by
    calc
      A/B = Real.exp L := (Real.exp_log (div_pos hA hB)).symm
      _ = Real.exp s*Real.exp δ := by
        rw [← Real.exp_add]
        congr 1
        dsimp only [δ]
        ring
  have hDB : D/B ≤ Real.exp (-9*s) := by
    have hexpM : Real.exp (-M) = D/B := by
      dsimp only [M]
      rw [Real.exp_neg, Real.exp_log (div_pos hB hD), inv_div]
    rw [← hexpM]
    exact Real.exp_le_exp.mpr (by linarith only [hMlo])
  have hratio : (A+D)/B ≤ Real.exp s+Real.exp (-9*s)+(99/40)*δ := by
    rw [add_div, hABexp]
    have hprod := mul_le_mul_of_nonneg_left hexpδ (Real.exp_pos s).le
    have hcoef := mul_nonneg hδ0 (sub_nonneg.mpr hexps.le)
    nlinarith only [hprod, hDB, hcoef]
  have herr : (99/40)*δ < 1/(10*P^2) := by
    apply (lt_div_iff₀ (show 0 < 10*P^2 by positivity)).2
    nlinarith only [hδtimes]
  change (A+D)/B < Real.exp s+Real.exp (-9*s)+1/(10*P^2)
  exact hratio.trans_lt (by linarith only [herr])

private theorem integer_binomial_gaussian_upper_envelope (p t : ℤ) (hp5 : 5 ≤ p)
    (ht2 : 2 ≤ t) (htp : t ≤ p) (hband : 24*p ≤ 25*t) :
    let n : ℕ := (p*(6*t-1)).toNat
    let s : ℝ := 4*(p : ℝ)^2/((p : ℝ)*(6*(t : ℝ)-1)+1)
    ((Nat.choose n (3*p*t).toNat : ℝ)+Nat.choose n (3*p*t+4*p).toNat)/
        (Nat.choose n (3*p*t+p).toNat : ℝ) <
      Real.exp s+Real.exp (-9*s)+1/(10*(p : ℝ)^2) := by
  let P : ℕ := p.toNat
  let T : ℕ := t.toNat
  have hP : (P : ℤ) = p := Int.toNat_of_nonneg (by omega)
  have hT : (T : ℤ) = t := Int.toNat_of_nonneg (by omega)
  have hP5 : 5 ≤ P := by omega
  have hT2 : 2 ≤ T := by omega
  have hTP : T ≤ P := by omega
  have hbandP : 24*P ≤ 25*T := by omega
  have hPR : (P : ℝ) = (p : ℝ) := by exact_mod_cast hP
  have hTR : (T : ℝ) = (t : ℝ) := by exact_mod_cast hT
  have hN : (p*(6*t-1)).toNat = P*(6*T-1) := by
    have hh : p*(6*t-1) = ((P*(6*T-1) : ℕ) : ℤ) := by
      simp only [Nat.cast_mul, Nat.cast_sub (show 1 ≤ 6*T by omega),
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
  have hs : 4*(P : ℝ)^2/(((P*(6*T-1) : ℕ) : ℝ)+1) =
      4*(p : ℝ)^2/((p : ℝ)*(6*(t : ℝ)-1)+1) := by
    rw [Nat.cast_mul, Nat.cast_sub (show 1 ≤ 6*T by omega)]
    push_cast
    rw [hPR, hTR]
  have hh := binomial_gaussian_upper_envelope P T hP5 hT2 hTP hbandP
  dsimp only at hh ⊢
  rw [hN, hI1, hI3, hI9]
  rw [hs, hPR] at hh
  exact hh

theorem actual_ratio_eq_binomial (p t : ℤ) (hp3 : 3 ≤ p) (hpo : Odd p)
    (ht2 : 2 ≤ t) :
    let N : ℕ := (p*(6*t-1)).toNat
    2*((original_return_pair p t).1 : ℝ)/((original_return_pair p t).2 : ℝ) =
      ((Nat.choose N (3*p*t).toNat : ℝ)+Nat.choose N (3*p*t+4*p).toNat)/
        (Nat.choose N (3*p*t+p).toNat : ℝ) := by
  let N : ℕ := (p*(6*t-1)).toNat
  let A : ℝ := Nat.choose N (3*p*t).toNat
  let B : ℝ := Nat.choose N (3*p*t+p).toNat
  let D : ℝ := Nat.choose N (3*p*t+4*p).toNat
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
  have hW19 : (original_return_pair p t).1 =
      2*(Nat.choose N (3*p*t).toNat+Nat.choose N (3*p*t+4*p).toNat) := by
    calc
      (original_return_pair p t).1 =
          2*(Nat.choose (p*(6*t-1)).toNat (p*((6*t-1)+1)/2).toNat +
            Nat.choose (p*(6*t-1)).toNat (p*((6*t-1)+9)/2).toNat) := hc.1
      _ = _ := by rw [hhalf1, hhalf9]
  have hW33 : (original_return_pair p t).2 = 4*Nat.choose N (3*p*t+p).toNat := by
    calc
      (original_return_pair p t).2 =
          4*Nat.choose (p*(6*t-1)).toNat (p*((6*t-1)+3)/2).toNat := hc.2
      _ = _ := by rw [hhalf3]
  have h19R : ((original_return_pair p t).1 : ℝ) = 2*(A+D) := by
    dsimp only [A, D]
    exact_mod_cast hW19
  have h33R : ((original_return_pair p t).2 : ℝ) = 4*B := by
    dsimp only [B]
    exact_mod_cast hW33
  have hratio : 2*((original_return_pair p t).1 : ℝ)/
      ((original_return_pair p t).2 : ℝ) = (A+D)/B := by
    rw [h19R, h33R]
    by_cases hB : B = 0
    · simp only [hB, mul_zero, div_zero]
    · field_simp [hB] <;> ring
  exact hratio

theorem actual_gaussian_upper_envelope (p t : ℤ) (hp5 : 5 ≤ p) (hpo : Odd p)
    (ht2 : 2 ≤ t) (htp : t ≤ p) (hband : 24*p ≤ 25*t) :
    let s : ℝ := 4*(p : ℝ)^2/((p : ℝ)*(6*(t : ℝ)-1)+1)
    2*((original_return_pair p t).1 : ℝ)/((original_return_pair p t).2 : ℝ) <
      Real.exp s+Real.exp (-9*s)+1/(10*(p : ℝ)^2) := by
  dsimp only
  rw [actual_ratio_eq_binomial p t (by omega) hpo ht2]
  exact integer_binomial_gaussian_upper_envelope p t hp5 ht2 htp hband

end D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianUpperEnvelope
