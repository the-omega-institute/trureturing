/- GID: D5/S3/FiniteGroups/BajnokBeattyOddWrapGaussianSecondOrder
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattyOddWrapGaussianSecondOrder
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A finite second-order correction bounds the original Gaussian ratio with error at most 1/(5*p^4). -/

import D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianEnvelope
import D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianUpperEnvelope

set_option autoImplicit false

namespace D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianSecondOrder

open BajnokBeattyOddWrapPositiveCone BajnokBeattyOddWrapSingleCrossing
open BajnokBeattyOddWrapReturnCounts
open BajnokBeattyOddWrapGaussianEnvelope
open BajnokBeattyOddWrapGaussianUpperEnvelope
open Finset

/-- The cubic logarithmic truncation, retaining the parameter-dependent
fifth-order tail rather than replacing it by a fixed cubic coefficient. -/
private theorem log_cubic_remainder_scaled {z P K : ℝ}
    (hz : 0 ≤ z) (hz1 : z < 1) (hP : 0 < P)
    (hcoef : 2*z^2*P^2 ≤ K*(1-z^2)) :
    0 ≤ Real.log ((1+z)/(1-z))-2*z-(2/3)*z^3 ∧
      Real.log ((1+z)/(1-z))-2*z-(2/3)*z^3 ≤ K/P^2*z^3 := by
  have hden : 0 < 1-z^2 := by
    have hh := mul_pos (sub_pos.mpr hz1) (show 0 < 1+z by linarith only [hz])
    nlinarith only [hh]
  have hlo := Real.sum_range_le_log_div hz hz1 2
  norm_num [Finset.sum_range_succ] at hlo
  have hhi := Real.log_div_le_sum_range_add hz hz1 2
  norm_num [Finset.sum_range_succ] at hhi
  have htail : 2*(z^5/(1-z^2)) ≤ K/P^2*z^3 := by
    rw [← mul_div_assoc, show K/P^2*z^3 = K*z^3/P^2 by ring]
    apply (div_le_div_iff₀ hden (pow_pos hP 2)).2
    have hh := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hz 3)
    nlinarith only [hh]
  constructor <;> linarith only [hlo, hhi, htail]

/-- The finite quadratic remainder for a positive displacement. -/
theorem exp_positive_quadratic_remainder {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |Real.exp u-1-u| ≤ (3/4)*u^2 := by
  have hlo := Real.add_one_le_exp u
  have hhi := Real.exp_bound' hu0 hu1 (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hhi
  rw [abs_of_nonneg (by linarith only [hlo] : 0 ≤ Real.exp u-1-u)]
  linarith only [hhi]

/-- This negative-displacement bound holds for every nonnegative u.
The reciprocal is cleared against a strictly positive exponential. -/
theorem exp_negative_quadratic_remainder {u : ℝ} (hu0 : 0 ≤ u) :
    |Real.exp (-u)-1+u| ≤ u^2/2 := by
  have hlo : 1-u ≤ Real.exp (-u) := by
    have hh := Real.add_one_le_exp (-u)
    linarith only [hh]
  have hQ : 0 < 1-u+u^2/2 := by nlinarith only [sq_nonneg (u-1)]
  have hquad := Real.quadratic_le_exp_of_nonneg hu0
  have hmul := mul_le_mul_of_nonneg_left hquad hQ.le
  have hid : (1-u+u^2/2)*(1+u+u^2/2) = 1+u^4/4 := by ring
  rw [hid] at hmul
  have hhi : Real.exp (-u) ≤ 1-u+u^2/2 := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply (div_le_iff₀ (Real.exp_pos u)).2
    nlinarith only [hmul, pow_nonneg hu0 4]
  rw [abs_of_nonneg (by linarith only [hlo] : 0 ≤ Real.exp (-u)-1+u)]
  linarith only [hhi]

/-- A short rational certificate used to suppress the negative block. -/
private theorem exp_six_gt_three_hundred : (300 : ℝ) < Real.exp 6 := by
  have hh := Real.sum_le_exp_of_nonneg (x := (6 : ℝ)) (by norm_num) 9
  norm_num [Finset.sum_range_succ, Nat.factorial] at hh
  linarith only [hh]

/-- Finite second-order estimate for the same three binomial coefficients.
Parity is unnecessary here; it enters only at the original-count bridge. -/
private theorem binomial_gaussian_second_order_envelope (p t : ℕ)
    (hp5 : 5 ≤ p) (ht2 : 2 ≤ t) (htp : t ≤ p) (hband : 24*p ≤ 25*t) :
    let n := p*(6*t-1)
    let s : ℝ := 4*(p : ℝ)^2/((n : ℝ)+1)
    |((Nat.choose n (3*p*t) : ℝ)+Nat.choose n (3*p*t+4*p))/
        (Nat.choose n (3*p*t+p) : ℝ) - (Real.exp s+Real.exp (-9*s)) -
        (s^3/48)*(5*Real.exp s-405*Real.exp (-9*s))/(p : ℝ)^2| ≤
      1/(5*(p : ℝ)^4) := by
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
  have hPfour : 0 < P^4 := pow_pos hP 4
  have hPsq25 : 25 ≤ P^2 := by nlinarith only [sq_nonneg (P-5), hP5]
  have hT2 : 2 ≤ T := by dsimp [T]; exact_mod_cast ht2
  have hTP : T ≤ P := by dsimp [P, T]; exact_mod_cast htp
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
  have hslo : (2/3 : ℝ) ≤ s := by
    dsimp [s]
    apply (le_div_iff₀ hR).2
    have hprod : 0 ≤ P*(P-T) := mul_nonneg hP.le (sub_nonneg.mpr hTP)
    dsimp [R]
    rw [hnR]
    nlinarith only [hprod, hP5]
  have hs0 : 0 ≤ s := by linarith only [hslo]
  have hshi : s ≤ 5/7 := by
    dsimp [s]
    apply (div_le_iff₀ hR).2
    nlinarith only [hRquad]
  have hscube : s^3 ≤ 125/343 := by
    have hh := pow_le_pow_left₀ hs0 hshi 3
    norm_num at hh
    exact hh
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
  have hyP (j : ℕ) (hj : j ∈ Finset.range (3*p)) : y j ≤ 45/(28*P) := by
    have hjR : (j : ℝ)+1 ≤ 3*P := by
      dsimp [P]
      exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hj)
    have hnum : 3*P+2*(j : ℝ)+1 ≤ 9*P := by linarith only [hjR]
    have hmul := mul_le_mul_of_nonneg_left hnum (show 0 ≤ 28*P by positivity)
    dsimp only [y]
    apply (div_le_div_iff₀ hR (show 0 < 28*P by positivity)).2
    nlinarith only [hmul, hRquad]
  have hx (i : ℕ) (hi : i ∈ Finset.range p) : 0 ≤ x i ∧ x i ≤ 3/28 := by
    constructor
    · dsimp [x]; positivity
    · apply (hxP i hi).trans
      apply (div_le_iff₀ (show 0 < 28*P by positivity)).2
      linarith only [hP5]
  have hy (j : ℕ) (hj : j ∈ Finset.range (3*p)) : 0 ≤ y j ∧ y j ≤ 9/28 := by
    constructor
    · dsimp [y]; positivity
    · apply (hyP j hj).trans
      apply (div_le_iff₀ (show 0 < 28*P by positivity)).2
      linarith only [hP5]
  have hxrem (i : ℕ) (hi : i ∈ Finset.range p) :
      0 ≤ Real.log ((1+x i)/(1-x i))-2*x i-(2/3)*(x i)^3 ∧
        Real.log ((1+x i)/(1-x i))-2*x i-(2/3)*(x i)^3 ≤
          ((18/31)/P^2)*(x i)^3 := by
    have hscaled : x i*P ≤ 15/28 := by
      have hh := (le_div_iff₀ (show 0 < 28*P by positivity)).1 (hxP i hi)
      nlinarith only [hh]
    have hsq := pow_le_pow_left₀ (mul_nonneg (hx i hi).1 hP.le) hscaled 2
    have hsmall := pow_le_pow_left₀ (hx i hi).1 (hx i hi).2 2
    norm_num at hsq hsmall
    apply log_cubic_remainder_scaled (hx i hi).1
      (by linarith only [(hx i hi).2]) hP
    nlinarith only [hsq, hsmall]
  have hyrem (j : ℕ) (hj : j ∈ Finset.range (3*p)) :
      0 ≤ Real.log ((1+y j)/(1-y j))-2*y j-(2/3)*(y j)^3 ∧
        Real.log ((1+y j)/(1-y j))-2*y j-(2/3)*(y j)^3 ≤
          ((4050/703)/P^2)*(y j)^3 := by
    have hscaled : y j*P ≤ 45/28 := by
      have hh := (le_div_iff₀ (show 0 < 28*P by positivity)).1 (hyP j hj)
      nlinarith only [hh]
    have hsq := pow_le_pow_left₀ (mul_nonneg (hy j hj).1 hP.le) hscaled 2
    have hsmall := pow_le_pow_left₀ (hy j hj).1 (hy j hj).2 2
    norm_num at hsq hsmall
    apply log_cubic_remainder_scaled (hy j hj).1
      (by linarith only [(hy j hj).2]) hP
    nlinarith only [hsq, hsmall]
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
  let Y3 : ℝ := ∑ j ∈ Finset.range (3*p), (y j)^3
  have hX3 : X3 = 2*P^2*(5*P^2-1)/R^3 := by
    dsimp only [X3, x]
    simp_rw [div_pow]
    rw [← Finset.sum_div, sum_cubic]
    change P*(P+P)*((P+P)^2+P^2-1)/R^3 = _
    ring
  have hY3 : Y3 = 18*P^2*(45*P^2-1)/R^3 := by
    dsimp only [Y3, y]
    simp_rw [div_pow]
    rw [← Finset.sum_div, sum_cubic, h3P]
    ring
  have hXtimes : X3*P^2 ≤ 625/10976 := by
    rw [hX3, div_mul_eq_mul_div]
    apply (div_le_iff₀ (pow_pos hR 3)).2
    nlinarith only [hRcube, sq_nonneg (P^2)]
  have hYtimes : Y3*P^2 ≤ 50625/10976 := by
    rw [hY3, div_mul_eq_mul_div]
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
  let EL : ℝ := ∑ i ∈ Finset.range p,
    (Real.log ((1+x i)/(1-x i))-2*x i-(2/3)*(x i)^3)
  let EM : ℝ := ∑ j ∈ Finset.range (3*p),
    (Real.log ((1+y j)/(1-y j))-2*y j-(2/3)*(y j)^3)
  have hEL0 : 0 ≤ EL := Finset.sum_nonneg (fun i hi ↦ (hxrem i hi).1)
  have hEM0 : 0 ≤ EM := Finset.sum_nonneg (fun j hj ↦ (hyrem j hj).1)
  have hELupper : EL ≤ ((18/31)/P^2)*X3 := by
    calc
      EL ≤ ∑ i ∈ Finset.range p, ((18/31)/P^2)*(x i)^3 :=
        Finset.sum_le_sum (fun i hi ↦ (hxrem i hi).2)
      _ = ((18/31)/P^2)*X3 := by rw [← Finset.mul_sum]
  have hEMupper : EM ≤ ((4050/703)/P^2)*Y3 := by
    calc
      EM ≤ ∑ j ∈ Finset.range (3*p), ((4050/703)/P^2)*(y j)^3 :=
        Finset.sum_le_sum (fun j hj ↦ (hyrem j hj).2)
      _ = ((4050/703)/P^2)*Y3 := by rw [← Finset.mul_sum]
  have hLexact : L = s+(2/3)*X3+EL := by
    dsimp only [EL]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← hlogL, hxsum]
    change L = s+(2/3)*X3+(L-2*(2*P^2/R)-(2/3)*X3)
    dsimp only [s]
    ring
  have hMexact : M = 9*s+(2/3)*Y3+EM := by
    dsimp only [EM]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← hlogM, hysum]
    change M = 9*s+(2/3)*Y3+(M-2*(18*P^2/R)-(2/3)*Y3)
    dsimp only [s]
    ring
  have hELtimes : EL*P^4 ≤ 5625/170128 := by
    have hh := mul_le_mul_of_nonneg_right hELupper hPfour.le
    have hid : (((18/31)/P^2)*X3)*P^4 = (18/31)*(X3*P^2) := by
      field_simp [hP.ne'] <;> ring
    rw [hid] at hh
    linarith only [hh, hXtimes]
  have hEMtimes : EM*P^4 ≤ 102515625/3858064 := by
    have hh := mul_le_mul_of_nonneg_right hEMupper hPfour.le
    have hid : (((4050/703)/P^2)*Y3)*P^4 = (4050/703)*(Y3*P^2) := by
      field_simp [hP.ne'] <;> ring
    rw [hid] at hh
    linarith only [hh, hYtimes]
  let aL : ℝ := (5/48)*s^3/P^2
  let aM : ℝ := (135/16)*s^3/P^2
  have hXidentity : (2/3)*X3 = aL-s^3/(48*P^4) := by
    rw [hX3]
    dsimp only [aL, s]
    field_simp [hR.ne', hP.ne'] <;> ring
  have hYidentity : (2/3)*Y3 = aM-3*s^3/(16*P^4) := by
    rw [hY3]
    dsimp only [aM, s]
    field_simp [hR.ne', hP.ne'] <;> ring
  have hLcorr : (L-s-aL)*P^4 = -s^3/48+EL*P^4 := by
    rw [hLexact, hXidentity]
    field_simp [hP.ne'] <;> ring
  have hMcorr : (M-9*s-aM)*P^4 = -3*s^3/16+EM*P^4 := by
    rw [hMexact, hYidentity]
    field_simp [hP.ne'] <;> ring
  have hLerr : |L-s-aL| ≤ 1/(30*P^4) := by
    have hh : |(L-s-aL)*P^4| ≤ 1/30 := by
      rw [hLcorr]
      apply abs_le.mpr
      constructor <;> nlinarith only [hscube, hELtimes,
        mul_nonneg hEL0 hPfour.le, pow_nonneg hs0 3]
    rw [abs_mul, abs_of_pos hPfour] at hh
    calc
      |L-s-aL| ≤ (1/30)/P^4 := (le_div_iff₀ hPfour).2 hh
      _ = 1/(30*P^4) := by ring
  have hMerr : |M-9*s-aM| ≤ 27/P^4 := by
    have hh : |(M-9*s-aM)*P^4| ≤ 27 := by
      rw [hMcorr]
      apply abs_le.mpr
      constructor <;> nlinarith only [hscube, hEMtimes,
        mul_nonneg hEM0 hPfour.le, pow_nonneg hs0 3]
    rw [abs_mul, abs_of_pos hPfour] at hh
    exact (le_div_iff₀ hPfour).2 hh
  -- Retain the sharper first-block displacement from the original upper proof.
  have hLlo : s ≤ L := by
    have hsum := Finset.sum_le_sum (fun i hi ↦
      show 2*x i ≤ Real.log ((1+x i)/(1-x i)) from by
        have hlo := Real.sum_range_le_log_div (hx i hi).1
          (by linarith [(hx i hi).2]) 1
        norm_num [Finset.sum_range_succ] at hlo
        linarith only [hlo])
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
      show 2*y j ≤ Real.log ((1+y j)/(1-y j)) from by
        have hlo := Real.sum_range_le_log_div (hy j hj).1
          (by linarith [(hy j hj).2]) 1
        norm_num [Finset.sum_range_succ] at hlo
        linarith only [hlo])
    rw [← hlogM, ← Finset.mul_sum, hysum] at hsum
    rw [show 2*(18*P^2/R) = 9*(4*P^2/R) by ring] at hsum
    exact hsum
  let δL : ℝ := L-s
  let δM : ℝ := M-9*s
  have hδL0 : 0 ≤ δL := sub_nonneg.mpr hLlo
  have hδM0 : 0 ≤ δM := sub_nonneg.mpr hMlo
  have hδLupper : δL ≤ ((2/3)+(18/775))*X3 := by
    dsimp only [δL]
    linarith only [hLhi]
  have hδLtimes : δL*P^2 ≤ 10025/255192 := by
    have hh := mul_le_mul_of_nonneg_right hδLupper hPsq.le
    nlinarith only [hh, hXtimes]
  have hδLbound : δL ≤ 1/(25*P^2) := by
    apply (le_div_iff₀ (show 0 < 25*P^2 by positivity)).2
    nlinarith only [hδLtimes]
  have hδLsmall : δL ≤ 1 := by
    apply hδLbound.trans
    apply (div_le_iff₀ (show 0 < 25*P^2 by positivity)).2
    nlinarith only [hPsq25]
  have hδMupper : δM ≤ aM+27/P^4 := by
    have hh := (le_abs_self (M-9*s-aM)).trans hMerr
    dsimp only [δM]
    linarith only [hh]
  have hδMbound : δM ≤ (25/6)/P^2 := by
    have hh := mul_le_mul_of_nonneg_right hδMupper hPsq.le
    have hid : (aM+27/P^4)*P^2 = (135/16)*s^3+27/P^2 := by
      dsimp only [aM]
      field_simp [hP.ne'] <;> ring
    rw [hid] at hh
    have h27 : 27/P^2 ≤ 27/25 := by
      apply (div_le_iff₀ hPsq).2
      nlinarith only [hPsq25]
    apply (le_div_iff₀ hPsq).2
    nlinarith only [hh, hscube, h27]
  have hδLsq : δL^2*P^4 ≤ 1/625 := by
    have hh := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hδL0 hδLbound 2) hPfour.le
    have hid : (1/(25*P^2))^2*P^4 = 1/625 := by
      field_simp [hP.ne'] <;> ring
    rwa [hid] at hh
  have hδMsq : δM^2*P^4 ≤ 625/36 := by
    have hh := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hδM0 hδMbound 2) hPfour.le
    have hid : ((25/6)/P^2)^2*P^4 = 625/36 := by
      field_simp [hP.ne'] <;> ring
    rwa [hid] at hh
  have hexps : Real.exp s < 9/4 :=
    (Real.exp_lt_exp.mpr (by linarith only [hshi] : s < 3/4)).trans
      exp_three_quarters_lt
  have hexpneg : Real.exp (-9*s) < 1/300 := by
    have hh : (300 : ℝ) < Real.exp (9*s) :=
      exp_six_gt_three_hundred.trans_le (Real.exp_le_exp.mpr (by linarith only [hslo]))
    rw [show -9*s = -(9*s) by ring, Real.exp_neg, inv_eq_one_div]
    apply (div_lt_div_iff₀ (Real.exp_pos (9*s)) (by norm_num : (0 : ℝ) < 300)).2
    simpa only [one_mul] using hh
  have hLexp : Real.exp L = Real.exp s*Real.exp δL := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [δL]
    ring
  have hMexp : Real.exp (-M) = Real.exp (-9*s)*Real.exp (-δM) := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [δM]
    ring
  have hLsplit : |Real.exp L-Real.exp s*(1+aL)| ≤
      Real.exp s*((3/4)*δL^2+1/(30*P^4)) := by
    have hid : Real.exp L-Real.exp s*(1+aL) =
        Real.exp s*((Real.exp δL-1-δL)+(δL-aL)) := by rw [hLexp]; ring
    rw [hid, abs_mul, abs_of_pos (Real.exp_pos s)]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos s).le
    calc
      |(Real.exp δL-1-δL)+(δL-aL)| ≤
          |Real.exp δL-1-δL|+|δL-aL| := abs_add_le _ _
      _ ≤ (3/4)*δL^2+1/(30*P^4) :=
        add_le_add (exp_positive_quadratic_remainder hδL0 hδLsmall) hLerr
  have hMsplit : |Real.exp (-M)-Real.exp (-9*s)*(1-aM)| ≤
      Real.exp (-9*s)*(δM^2/2+27/P^4) := by
    have hid : Real.exp (-M)-Real.exp (-9*s)*(1-aM) =
        Real.exp (-9*s)*((Real.exp (-δM)-1+δM)-(δM-aM)) := by
      rw [hMexp]
      ring
    rw [hid, abs_mul, abs_of_pos (Real.exp_pos (-9*s))]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos (-9*s)).le
    calc
      |(Real.exp (-δM)-1+δM)-(δM-aM)| ≤
          |Real.exp (-δM)-1+δM|+|δM-aM| := abs_sub _ _
      _ ≤ δM^2/2+27/P^4 :=
        add_le_add (exp_negative_quadratic_remainder hδM0) hMerr
  have hLblock : |Real.exp L-Real.exp s*(1+aL)| *P^4 ≤ 777/10000 := by
    have hh := mul_le_mul_of_nonneg_right hLsplit hPfour.le
    have hid : (Real.exp s*((3/4)*δL^2+1/(30*P^4)))*P^4 =
        Real.exp s*((3/4)*(δL^2*P^4)+1/30) := by
      field_simp [hP.ne'] <;> ring
    rw [hid] at hh
    have hcoef := mul_le_mul_of_nonneg_right hexps.le
      (show 0 ≤ (3/4)*(δL^2*P^4)+1/30 by positivity)
    have hnum : (9/4)*((3/4)*(δL^2*P^4)+1/30) ≤ 777/10000 := by
      linarith only [hδLsq]
    exact hh.trans (hcoef.trans hnum)
  have hMblock : |Real.exp (-M)-Real.exp (-9*s)*(1-aM)| *P^4 ≤ 2569/21600 := by
    have hh := mul_le_mul_of_nonneg_right hMsplit hPfour.le
    have hid : (Real.exp (-9*s)*(δM^2/2+27/P^4))*P^4 =
        Real.exp (-9*s)*((δM^2*P^4)/2+27) := by
      field_simp [hP.ne'] <;> ring
    rw [hid] at hh
    have hcoef := mul_le_mul_of_nonneg_right hexpneg.le
      (show 0 ≤ (δM^2*P^4)/2+27 by positivity)
    have hnum : (1/300)*((δM^2*P^4)/2+27) ≤ 2569/21600 := by
      linarith only [hδMsq]
    exact hh.trans (hcoef.trans hnum)
  have hexpL : Real.exp L = A/B := Real.exp_log (div_pos hA hB)
  have hexpM : Real.exp (-M) = D/B := by
    dsimp only [M]
    rw [Real.exp_neg, Real.exp_log (div_pos hB hD), inv_div]
  have hcorrection : aL*Real.exp s-aM*Real.exp (-9*s) =
      (s^3/48)*(5*Real.exp s-405*Real.exp (-9*s))/P^2 := by
    dsimp only [aL, aM]
    ring
  have hmainalg : (A+D)/B-(Real.exp s+Real.exp (-9*s))-
        (s^3/48)*(5*Real.exp s-405*Real.exp (-9*s))/P^2 =
      (Real.exp L-Real.exp s*(1+aL))+
        (Real.exp (-M)-Real.exp (-9*s)*(1-aM)) := by
    rw [hexpL, hexpM, ← hcorrection, add_div]
    ring
  have hmainbound : |(A+D)/B-(Real.exp s+Real.exp (-9*s))-
      (s^3/48)*(5*Real.exp s-405*Real.exp (-9*s))/P^2| *P^4 ≤ 1/5 := by
    rw [hmainalg]
    have hh := mul_le_mul_of_nonneg_right
      (abs_add_le (Real.exp L-Real.exp s*(1+aL))
        (Real.exp (-M)-Real.exp (-9*s)*(1-aM))) hPfour.le
    rw [add_mul] at hh
    linarith only [hh, hLblock, hMblock]
  change |(A+D)/B-(Real.exp s+Real.exp (-9*s))-
      (s^3/48)*(5*Real.exp s-405*Real.exp (-9*s))/P^2| ≤ 1/(5*P^4)
  calc
    _ ≤ (1/5)/P^4 := (le_div_iff₀ hPfour).2 hmainbound
    _ = 1/(5*P^4) := by ring

/-- Exact Nat/Int transport of the second-order estimate, including its band. -/
private theorem integer_binomial_gaussian_second_order_envelope (p t : ℤ)
    (hp5 : 5 ≤ p) (ht2 : 2 ≤ t) (htp : t ≤ p) (hband : 24*p ≤ 25*t) :
    let n : ℕ := (p*(6*t-1)).toNat
    let s : ℝ := 4*(p : ℝ)^2/((p : ℝ)*(6*(t : ℝ)-1)+1)
    |((Nat.choose n (3*p*t).toNat : ℝ)+Nat.choose n (3*p*t+4*p).toNat)/
        (Nat.choose n (3*p*t+p).toNat : ℝ) - (Real.exp s+Real.exp (-9*s)) -
        (s^3/48)*(5*Real.exp s-405*Real.exp (-9*s))/(p : ℝ)^2| ≤
      1/(5*(p : ℝ)^4) := by
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
  have hh := binomial_gaussian_second_order_envelope P T hP5 hT2 hTP hbandP
  dsimp only at hh ⊢
  rw [hN, hI1, hI3, hI9]
  rw [hs, hPR] at hh
  exact hh

/-- Finite second-order Gaussian error for the full original return counts.
All odd integers p ≥ 5, including composites, are covered on the stated band. -/
theorem actual_gaussian_second_order_envelope (p t : ℤ) (hp5 : 5 ≤ p) (hpo : Odd p)
    (ht2 : 2 ≤ t) (htp : t ≤ p) (hband : 24*p ≤ 25*t) :
    let s : ℝ := 4*(p : ℝ)^2/((p : ℝ)*(6*(t : ℝ)-1)+1)
    |2*((original_return_pair p t).1 : ℝ)/((original_return_pair p t).2 : ℝ) -
        (Real.exp s+Real.exp (-9*s)) -
        (s^3/48)*(5*Real.exp s-405*Real.exp (-9*s))/(p : ℝ)^2| ≤
      1/(5*(p : ℝ)^4) := by
  dsimp only
  rw [actual_ratio_eq_binomial p t (by omega) hpo ht2]
  exact integer_binomial_gaussian_second_order_envelope p t hp5 ht2 htp hband

end D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianSecondOrder
