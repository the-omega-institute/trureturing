/- GID: D5/S3/FiniteGroups/BajnokBeattyOddWrapGaussianEnvelope
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattyOddWrapGaussianEnvelope
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Coupled finite logarithmic errors give the strict original Gaussian lower envelope. -/

/- Coupled finite Gaussian lower estimate for the original quotient returns.

The original PositiveCone.choose_ratio_prod and sum_linear are reused;
neither is reproved here.

The new content is the exact cubic moment, the coupled logarithmic error
bound M-9s <= (29997/40)(L-s), and the strict absorption of both errors.
For natural p>=3 and 2<=t<=p it proves
  exp s + exp (-9s) < (A+D)/B,
where a=3pt, n=p(6t-1), R=n+1, s=4p^2/R,
A=choose(n,a), B=choose(n,a+p), D=choose(n,a+4p).
An integer theorem below transports the complete original integer domain.
The final theorem consumes the existing exact original count formula
W19=2(A+D), W33=4B; no new count premise is introduced.
-/

import D5.S3.FiniteGroups.BajnokBeattyOddWrapPositiveCone
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianEnvelope

open BajnokBeattyOddWrapPositiveCone BajnokBeattyOddWrapSingleCrossing
open BajnokBeattyOddWrapReturnCounts
open Finset

theorem sum_cubic (q : ℝ) (r : ℕ) :
    (∑ i ∈ Finset.range r, (q+2*(i : ℝ)+1)^3) =
      (r : ℝ)*(q+r)*((q+r)^2+(r : ℝ)^2-1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

private theorem log_lower_cubic {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    2*x+(2/3)*x^3 ≤ Real.log ((1+x)/(1-x)) := by
  have h := Real.sum_range_le_log_div hx hx1 2
  norm_num [Finset.sum_range_succ] at h
  linarith only [h]

private theorem log_upper_cubic {y : ℝ} (hy : 0 ≤ y) (hy9 : y ≤ 9/11) :
    Real.log ((1+y)/(1-y)) ≤ 2*y+(121/20)*y^3 := by
  have hy1 : y < 1 := by linarith
  have hy2 : y^2 ≤ 81/121 := by
    nlinarith [mul_nonneg hy (sub_nonneg.mpr hy9)]
  have hden : 0 < 1-y^2 := by linarith
  have hrem : y^3/(1-y^2) ≤ (121/40)*y^3 := by
    apply (div_le_iff₀ hden).2
    have hmul : 0 ≤ y^3*(81/121-y^2) :=
      mul_nonneg (pow_nonneg hy 3) (sub_nonneg.mpr hy2)
    nlinarith only [hmul]
  have h := Real.log_div_le_sum_range_add hy hy1 1
  norm_num [Finset.sum_range_succ] at h
  linarith only [h, hrem]

private theorem exp_twenty_thirds_gt : (750 : ℝ) < Real.exp (20/3 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (x := (20/3 : ℝ)) (by norm_num) 12
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith only [h]

/-- A positive first-block error absorbs the larger second-block error.
The two tangent-line bounds apply at both positive and negative arguments. -/
private theorem absorb_log_errors (s L M : ℝ) (hs : (2/3 : ℝ) ≤ s)
    (hL : s < L) (hM : M ≤ 9*s+750*(L-s)) :
    Real.exp s+Real.exp (-9*s) < Real.exp L+Real.exp (-M) := by
  let δ : ℝ := L-s
  have hδ : 0 < δ := by dsimp [δ]; linarith only [hL]
  have he : (750 : ℝ) < Real.exp (10*s) :=
    exp_twenty_thirds_gt.trans_le (Real.exp_le_exp.mpr (by linarith only [hs]))
  have hcoef : 750*Real.exp (-9*s) < Real.exp s := by
    have hh := mul_lt_mul_of_pos_right he (Real.exp_pos (-9*s))
    have hid : Real.exp (10*s)*Real.exp (-9*s) = Real.exp s := by
      rw [← Real.exp_add]
      congr 1
      ring
    rwa [hid] at hh
  have hleft : Real.exp s*(1+δ) ≤ Real.exp L := by
    calc
      Real.exp s*(1+δ) ≤ Real.exp s*Real.exp δ := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos s).le
        simpa only [add_comm] using Real.add_one_le_exp δ
      _ = Real.exp L := by
        rw [← Real.exp_add]
        congr 1
        dsimp [δ]
        ring
  have hright : Real.exp (-9*s)*(1-750*δ) ≤ Real.exp (-M) := by
    calc
      Real.exp (-9*s)*(1-750*δ) ≤ Real.exp (-9*s)*Real.exp (-750*δ) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos (-9*s)).le
        convert Real.add_one_le_exp (-750*δ) using 1 <;> ring
      _ = Real.exp (-9*s-750*δ) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-M) := Real.exp_le_exp.mpr (by dsimp [δ]; linarith only [hM])
  have hsurplus : 0 < δ*(Real.exp s-750*Real.exp (-9*s)) :=
    mul_pos hδ (sub_pos.mpr hcoef)
  nlinarith only [hleft, hright, hsurplus]

/-- Strict finite Gaussian lower envelope for the binomial comparison.
No parity condition is needed for this finite binomial theorem. -/
private theorem binomial_gaussian_envelope (p t : ℕ) (hp3 : 3 ≤ p) (ht2 : 2 ≤ t)
    (htp : t ≤ p) :
    let n := p*(6*t-1)
    let s : ℝ := 4*(p : ℝ)^2/((n : ℝ)+1)
    Real.exp s+Real.exp (-9*s) <
      ((Nat.choose n (3*p*t) : ℝ)+Nat.choose n (3*p*t+4*p))/
        (Nat.choose n (3*p*t+p) : ℝ) := by
  let P : ℝ := p
  let T : ℝ := t
  let a : ℕ := 3*p*t
  let n : ℕ := p*(6*t-1)
  let A : ℝ := Nat.choose n a
  let B : ℝ := Nat.choose n (a+p)
  let D : ℝ := Nat.choose n (a+4*p)
  let R : ℝ := (n : ℝ)+1
  let s : ℝ := 4*P^2/R
  have hP3 : 3 ≤ P := by dsimp [P]; exact_mod_cast hp3
  have hP : 0 < P := by linarith only [hP3]
  have hT2 : 2 ≤ T := by dsimp [T]; exact_mod_cast ht2
  have hTP : T ≤ P := by dsimp [P, T]; exact_mod_cast htp
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
  have hs : (2/3 : ℝ) ≤ s := by
    dsimp [s]
    apply (le_div_iff₀ hR).2
    have hprod : 0 ≤ P*(P-T) := mul_nonneg hP.le (sub_nonneg.mpr hTP)
    dsimp [R]
    rw [hnR]
    nlinarith only [hprod, hP3]
  let x (i : ℕ) : ℝ := (P+2*(i : ℝ)+1)/R
  let y (j : ℕ) : ℝ := (3*P+2*(j : ℝ)+1)/R
  have hx (i : ℕ) (hi : i ∈ Finset.range p) : 0 ≤ x i ∧ x i < 1 := by
    have hiR : (i : ℝ)+1 ≤ P := by
      dsimp [P]
      exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hi)
    constructor
    · dsimp [x]; positivity
    · dsimp [x]
      apply (div_lt_iff₀ hR).2
      linarith only [hiR, hRlow, hP3]
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
    have hh := choose_ratio_prod n a p (by omega : a+p ≤ n)
    change A/B = _ at hh
    rw [hh]
    apply Finset.prod_congr rfl
    intro i hi
    have hiR : (i : ℝ)+1 ≤ P := by
      dsimp [P]
      exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hi)
    have hden : 0 < (n : ℝ)-(a : ℝ)-(i : ℝ) := by
      rw [hnR, haR]
      nlinarith only [hiR, hPT, hP3]
    apply (div_eq_div_iff hden.ne' (show 1-x i ≠ 0 by linarith [(hx i hi).2])).2
    dsimp only [x]
    have hdiv := div_mul_cancel₀ (P+2*(i : ℝ)+1) hR.ne'
    dsimp only [R] at hdiv ⊢
    rw [hnR] at hdiv
    rw [haR, hnR]
    linear_combination -hdiv
  have hBD : B/D = ∏ j ∈ Finset.range (3*p), (1+y j)/(1-y j) := by
    have hh := choose_ratio_prod n (a+p) (3*p) (by omega : a+p+3*p ≤ n)
    rw [show a+p+3*p = a+4*p by omega] at hh
    change B/D = _ at hh
    rw [hh]
    apply Finset.prod_congr rfl
    intro j hj
    have hjR : (j : ℝ)+1 ≤ 3*P := by
      dsimp [P]
      exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hj)
    have hden : 0 < (n : ℝ)-((a+p : ℕ) : ℝ)-(j : ℝ) := by
      push_cast
      rw [hnR, haR]
      change 0 < 6*P*T-P-(3*P*T+P)-(j : ℝ)
      nlinarith only [hjR, hPT, hP3]
    apply (div_eq_div_iff hden.ne' (show 1-y j ≠ 0 by linarith [(hy j hj).2])).2
    dsimp only [y]
    have hdiv := div_mul_cancel₀ (3*P+2*(j : ℝ)+1) hR.ne'
    dsimp only [R] at hdiv ⊢
    push_cast at hdiv ⊢
    rw [hnR] at hdiv
    rw [haR, hnR]
    linear_combination -hdiv
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
  have hXpos : 0 < X3 := by
    rw [hX3]
    have hquad : 0 < 5*P^2-1 := by nlinarith only [sq_nonneg (P-1), hP3]
    exact div_pos (mul_pos (by positivity) hquad) (pow_pos hR 3)
  have hmoment : Y3 ≤ (909/11)*X3 := by
    rw [hY3, hX3]
    rw [← mul_div_assoc]
    apply (div_le_div_iff_of_pos_right (pow_pos hR 3)).2
    have hquad : 0 ≤ P^2-9 := by nlinarith only [sq_nonneg (P-3), hP3]
    have hmul : 0 ≤ P^2*(P^2-9) := mul_nonneg (sq_nonneg P) hquad
    nlinarith only [hmul]
  let L : ℝ := Real.log (A/B)
  let M : ℝ := Real.log (B/D)
  have hL : s+(2/3)*X3 ≤ L := by
    have hsum := Finset.sum_le_sum (fun i hi ↦ log_lower_cubic (hx i hi).1 (hx i hi).2)
    have hlog : L = ∑ i ∈ Finset.range p, Real.log ((1+x i)/(1-x i)) := by
      dsimp only [L]
      rw [hAB, Real.log_prod (fun i hi ↦ (hxp i hi).ne')]
    rw [← hlog] at hsum
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hxsum] at hsum
    change 2*(2*P^2/R)+(2/3)*X3 ≤ L at hsum
    dsimp only [s]
    calc
      4*P^2/R+(2/3)*X3 = 2*(2*P^2/R)+(2/3)*X3 := by ring
      _ ≤ L := hsum
  have hM : M ≤ 9*s+(121/20)*Y3 := by
    have hsum := Finset.sum_le_sum (fun j hj ↦ log_upper_cubic (hy j hj).1 (hy j hj).2)
    have hlog : M = ∑ j ∈ Finset.range (3*p), Real.log ((1+y j)/(1-y j)) := by
      dsimp only [M]
      rw [hBD, Real.log_prod (fun j hj ↦ (hyp j hj).ne')]
    rw [← hlog] at hsum
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hysum] at hsum
    change M ≤ 2*(18*P^2/R)+(121/20)*Y3 at hsum
    dsimp only [s]
    calc
      M ≤ 2*(18*P^2/R)+(121/20)*Y3 := hsum
      _ = 9*(4*P^2/R)+(121/20)*Y3 := by ring
  have hLstrict : s < L := by linarith only [hL, hXpos]
  have hMerror : M ≤ 9*s+750*(L-s) := by
    linarith only [hM, hmoment, hL, hLstrict]
  have habsorb := absorb_log_errors s L M hs hLstrict hMerror
  have hexpL : Real.exp L = A/B := Real.exp_log (div_pos hA hB)
  have hexpM : Real.exp (-M) = D/B := by
    dsimp only [M]
    rw [Real.exp_neg, Real.exp_log (div_pos hB hD), inv_div]
  rw [hexpL, hexpM] at habsorb
  change Real.exp s+Real.exp (-9*s) < (A+D)/B
  simpa only [add_div] using habsorb

/-- Transport to exactly the original integer parameter domain.
The three natural indices are the original nonnegative integer indices. -/
private theorem integer_binomial_gaussian_envelope (p t : ℤ) (hp3 : 3 ≤ p)
    (ht2 : 2 ≤ t) (htp : t ≤ p) :
    let n : ℕ := (p*(6*t-1)).toNat
    let s : ℝ := 4*(p : ℝ)^2/((p : ℝ)*(6*(t : ℝ)-1)+1)
    Real.exp s+Real.exp (-9*s) <
      ((Nat.choose n (3*p*t).toNat : ℝ)+Nat.choose n (3*p*t+4*p).toNat)/
        (Nat.choose n (3*p*t+p).toNat : ℝ) := by
  let P : ℕ := p.toNat
  let T : ℕ := t.toNat
  have hP : (P : ℤ) = p := Int.toNat_of_nonneg (by omega)
  have hT : (T : ℤ) = t := Int.toNat_of_nonneg (by omega)
  have hP3 : 3 ≤ P := by omega
  have hT2 : 2 ≤ T := by omega
  have hTP : T ≤ P := by omega
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
  have hh := binomial_gaussian_envelope P T hP3 hT2 hTP
  dsimp only at hh ⊢
  rw [hN, hI1, hI3, hI9]
  simpa only [hs] using hh

/-- The strict finite envelope for the full original quotient readouts.
Both components are the existing original_return_pair, at exactly p,t. -/
theorem actual_gaussian_envelope (p t : ℤ) (hp3 : 3 ≤ p) (hpo : Odd p)
    (ht2 : 2 ≤ t) (htp : t ≤ p) :
    let s : ℝ := 4*(p : ℝ)^2/((p : ℝ)*(6*(t : ℝ)-1)+1)
    Real.exp s+Real.exp (-9*s) <
      2*((original_return_pair p t).1 : ℝ)/((original_return_pair p t).2 : ℝ) := by
  let N : ℕ := (p*(6*t-1)).toNat
  let A : ℝ := Nat.choose N (3*p*t).toNat
  let B : ℝ := Nat.choose N (3*p*t+p).toNat
  let D : ℝ := Nat.choose N (3*p*t+4*p).toNat
  let s : ℝ := 4*(p : ℝ)^2/((p : ℝ)*(6*(t : ℝ)-1)+1)
  have hb : Real.exp s+Real.exp (-9*s) < (A+D)/B :=
    integer_binomial_gaussian_envelope p t hp3 ht2 htp
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
  change Real.exp s+Real.exp (-9*s) < _
  rw [hratio]
  exact hb

end D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianEnvelope
