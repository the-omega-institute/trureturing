/- GID: D5/S3/FiniteGroups/BajnokBeattyOddWrapPositiveCone
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattyOddWrapPositiveCone
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Finite logarithmic binomial estimates give actual positivity for t at least p. -/

import D5.S3.FiniteGroups.BajnokBeattyOddWrapSingleCrossing
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-! # A sharper positive cone for the original odd-wrap return counts

Finite logarithmic estimates prove a positive endpoint at `t = p` for `p ≥ 5`.
The established single-crossing theorem extends it to every `t ≥ p`.
-/

set_option autoImplicit false

namespace D5.S3.FiniteGroups.BajnokBeattyOddWrapPositiveCone

open BajnokBeattyOddWrapSingleCrossing BajnokBeattyOddWrapReturnCounts

open Finset

private theorem log_symmetric_bound {x : ℝ} (hx : 0 ≤ x) (hx10 : x ≤ 1/10) :
    Real.log ((1+x)/(1-x)) ≤ (4967/2475)*x := by
  have hx1 : x < 1 := by linarith
  have hx2 : x^2 ≤ 1/100 := by
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hx10)]
  have hx4 : x^4 ≤ 1/10000 := by
    have h := pow_le_pow_left₀ hx hx10 4
    norm_num at h
    exact h
  have hx3 : x^3 ≤ x/100 := by
    calc
      x^3 = x*x^2 := by ring
      _ ≤ x*(1/100) := mul_le_mul_of_nonneg_left hx2 hx
      _ = x/100 := by ring
  have hx5 : x^5 ≤ x/10000 := by
    calc
      x^5 = x*x^4 := by ring
      _ ≤ x*(1/10000) := mul_le_mul_of_nonneg_left hx4 hx
      _ = x/10000 := by ring
  have hden : 0 < 1-x^2 := by linarith
  have hrem : x^5/(1-x^2) ≤ x/9900 := by
    apply (div_le_iff₀ hden).2
    nlinarith only [hx3, hx5]
  have ht := Real.log_div_le_sum_range_add hx hx1 2
  norm_num [Finset.sum_range_succ] at ht
  nlinarith only [ht, hx3, hrem]

private theorem exp_eleven_sixteenths_lt :
    Real.exp (11/16 : ℝ) < 199/100 := by
  have h := Real.exp_bound' (x := (11/16 : ℝ)) (by norm_num) (by norm_num)
    (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith only [h]

private theorem exp_sixty_thirteenths_gt :
    (100 : ℝ) < Real.exp (60/13 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (x := (60/13 : ℝ)) (by norm_num) 11
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith only [h]

private theorem log_one_add_bound {c : ℝ} (hc : 0 ≤ c) (hc3 : c ≤ 3/5) :
    (10/13)*c ≤ Real.log (1+c) := by
  have hden : 0 < c+2 := by linarith
  have hrat : (10/13)*c ≤ 2*c/(c+2) := by
    apply (le_div_iff₀ hden).2
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hc3)]
  exact hrat.trans (Real.le_log_one_add_of_nonneg hc)

/-- A finite product estimate with a fixed rational certificate. -/
private theorem symmetric_product_lt {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1/10)
    (hsum : ∑ i ∈ s, x i ≤ 25/73) :
    (∏ i ∈ s, (1+x i)/(1-x i)) < 199/100 := by
  have hpos (i : ι) (hi : i ∈ s) : 0 < (1+x i)/(1-x i) := by
    obtain ⟨h0, h10⟩ := hx i hi
    apply div_pos <;> linarith
  have hprod : 0 < ∏ i ∈ s, (1+x i)/(1-x i) := Finset.prod_pos hpos
  have hlog : Real.log (∏ i ∈ s, (1+x i)/(1-x i)) ≤
      (4967/2475)*(∑ i ∈ s, x i) := by
    rw [Real.log_prod (fun i hi ↦ (hpos i hi).ne')]
    calc
      ∑ i ∈ s, Real.log ((1+x i)/(1-x i)) ≤
          ∑ i ∈ s, (4967/2475)*x i := by
        exact Finset.sum_le_sum fun i hi ↦ log_symmetric_bound (hx i hi).1 (hx i hi).2
      _ = (4967/2475)*(∑ i ∈ s, x i) := (Finset.mul_sum ..).symm
  have hsmall : Real.log (∏ i ∈ s, (1+x i)/(1-x i)) < 11/16 := by
    nlinarith only [hlog, hsum]
  exact ((Real.log_lt_iff_lt_exp hprod).mp hsmall).trans exp_eleven_sixteenths_lt

/-- The sum six and pointwise bound three fifths force a factor exceeding one hundred. -/
private theorem one_add_product_gt {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i ∧ c i ≤ 3/5)
    (hsum : 6 ≤ ∑ i ∈ s, c i) :
    (100 : ℝ) < ∏ i ∈ s, (1+c i) := by
  have hpos (i : ι) (hi : i ∈ s) : 0 < 1+c i := by linarith [(hc i hi).1]
  have hprod : 0 < ∏ i ∈ s, (1+c i) := Finset.prod_pos hpos
  have hlog : (10/13)*(∑ i ∈ s, c i) ≤ Real.log (∏ i ∈ s, (1+c i)) := by
    rw [Real.log_prod (fun i hi ↦ (hpos i hi).ne'), Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi ↦ log_one_add_bound (hc i hi).1 (hc i hi).2
  have hlarge : (60/13 : ℝ) ≤ Real.log (∏ i ∈ s, (1+c i)) := by
    nlinarith only [hlog, hsum]
  exact exp_sixty_thirteenths_gt.trans_le ((Real.le_log_iff_exp_le hprod).mp hlarge)

theorem sum_linear (q : ℝ) (r : ℕ) :
    (∑ i ∈ Finset.range r, (q+2*(i : ℝ)+1)) = (r : ℝ)*(q+r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- Exact adjacent-index ratios multiplied over a finite block. -/
theorem choose_ratio_prod (n k r : ℕ) (hkr : k+r ≤ n) :
    (Nat.choose n k : ℝ)/(Nat.choose n (k+r) : ℝ) =
      ∏ i ∈ Finset.range r, ((k : ℝ)+i+1)/((n : ℝ)-k-i) := by
  revert hkr
  induction r with
  | zero =>
    intro hkr
    have hC : (Nat.choose n k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega : k ≤ n)).ne'
    simp [hC]
  | succ r ih =>
    intro hkr
    have hk0 : k+r ≤ n := by omega
    have hi := ih hk0
    have hC0 : (Nat.choose n (k+r) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hk0).ne'
    have hC1 : (Nat.choose n (k+r+1) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega : k+r+1 ≤ n)).ne'
    have hden : (n : ℝ)-(k : ℝ)-(r : ℝ) ≠ 0 := by
      have hlt : (k : ℝ)+(r : ℝ) < n := by exact_mod_cast (show k+r < n by omega)
      linarith
    have hstep : (Nat.choose n (k+r+1) : ℝ)*((k : ℝ)+r+1) =
        (Nat.choose n (k+r) : ℝ)*((n : ℝ)-k-r) := by
      have hs := Nat.choose_succ_right_eq n (k+r)
      have hsR : (Nat.choose n (k+r+1) : ℝ)*((k+r+1 : ℕ) : ℝ) =
          (Nat.choose n (k+r) : ℝ)*((n-(k+r) : ℕ) : ℝ) := by exact_mod_cast hs
      rw [Nat.cast_sub hk0] at hsR
      push_cast at hsR
      convert hsR using 1 <;> ring
    rw [show k+Nat.succ r = k+r+1 by omega, Finset.prod_range_succ, ← hi]
    field_simp [hC0, hC1, hden]
    nlinarith only [congrArg (fun z : ℝ ↦ (Nat.choose n k : ℝ)*z) hstep]

/-- The positive endpoint needed by the already established strict persistence theorem.
No parity hypothesis is needed for this binomial inequality. -/
private theorem positive_endpoint_binomial (p : ℕ) (hp : 5 ≤ p) :
    let n := p*(6*p-1)
    Nat.choose n (3*p^2) + Nat.choose n (3*p^2+4*p) <
      2*Nat.choose n (3*p^2+p) := by
  let P : ℝ := p
  let a : ℕ := 3*p^2
  let n : ℕ := p*(6*p-1)
  let A : ℝ := Nat.choose n a
  let B : ℝ := Nat.choose n (a+p)
  let D : ℝ := Nat.choose n (a+4*p)
  have hP5 : 5 ≤ P := by dsimp [P]; exact_mod_cast hp
  have hP : 0 < P := by linarith
  have haR : (a : ℝ) = 3*P^2 := by dsimp [a, P]; push_cast; ring
  have hnR : (n : ℝ) = 6*P^2-P := by
    dsimp [n]
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ 6*p)]
    push_cast
    dsimp [P]
    ring
  have han : a+4*p ≤ n := by
    have hh : ((a+4*p : ℕ) : ℝ) ≤ (n : ℝ) := by
      push_cast
      rw [haR, hnR]
      change 3*P^2+4*P ≤ 6*P^2-P
      nlinarith [mul_nonneg hP.le (show 0 ≤ 3*P-5 by linarith)]
    exact_mod_cast hh
  have hB : 0 < B := by dsimp [B]; exact_mod_cast Nat.choose_pos (by omega : a+p ≤ n)
  have hD : 0 < D := by dsimp [D]; exact_mod_cast Nat.choose_pos han
  let R : ℝ := 6*P^2-P+1
  have hR : 0 < R := by
    dsimp [R]
    nlinarith [sq_nonneg (P-1)]
  let x (i : ℕ) : ℝ := (P+2*(i : ℝ)+1)/R
  have hx (i : ℕ) (hi : i ∈ Finset.range p) : 0 ≤ x i ∧ x i ≤ 1/10 := by
    have hiN : i+1 ≤ p := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
    have hiR : (i : ℝ)+1 ≤ P := by dsimp [P]; exact_mod_cast hiN
    have hi0 : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
    constructor
    · dsimp [x]; positivity
    · dsimp [x]
      apply (div_le_iff₀ hR).2
      have hc : 0 ≤ (P-5)*(6*P-1) := mul_nonneg (by linarith) (by linarith)
      dsimp [R]
      nlinarith only [hiR, hc]
  have hxsum : (∑ i ∈ Finset.range p, x i) ≤ 25/73 := by
    have hsum : (∑ i ∈ Finset.range p, x i) = 2*P^2/R := by
      dsimp only [x]
      rw [← Finset.sum_div, sum_linear]
      change P*(P+P)/R = 2*P^2/R
      ring
    rw [hsum]
    apply (div_le_iff₀ hR).2
    have hc : 0 ≤ (P-5)*(4*P-5) := mul_nonneg (by linarith) (by linarith)
    dsimp [R]
    nlinarith only [hc]
  have hAB : A/B < 199/100 := by
    have hratio := choose_ratio_prod n a p (by omega : a+p ≤ n)
    change A/B = _ at hratio
    rw [hratio]
    have hid : (∏ i ∈ Finset.range p, ((a : ℝ)+i+1)/((n : ℝ)-a-i)) =
        ∏ i ∈ Finset.range p, (1+x i)/(1-x i) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hiN : i+1 ≤ p := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
      have hiR : (i : ℝ)+1 ≤ P := by dsimp [P]; exact_mod_cast hiN
      have hden : 0 < (n : ℝ)-(a : ℝ)-(i : ℝ) := by
        rw [hnR, haR]
        nlinarith [mul_nonneg hP.le (show 0 ≤ 3*P-2 by linarith)]
      have hxm : 1-x i ≠ 0 := by linarith [(hx i hi).2]
      apply (div_eq_div_iff hden.ne' hxm).2
      dsimp only [x]
      rw [haR, hnR]
      have hdiv := div_mul_cancel₀ (P+2*(i : ℝ)+1) hR.ne'
      dsimp only [R] at hdiv ⊢
      linear_combination -hdiv
    rw [hid]
    exact symmetric_product_lt (Finset.range p) x hx hxsum
  let c (i : ℕ) : ℝ := (3*P+2*(i : ℝ)+1)/(3*P^2)
  have haPos : 0 < 3*P^2 := by positivity
  have hc (i : ℕ) (hi : i ∈ Finset.range (3*p)) : 0 ≤ c i ∧ c i ≤ 3/5 := by
    have hiN : i+1 ≤ 3*p := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
    have hiR : (i : ℝ)+1 ≤ 3*P := by dsimp [P]; exact_mod_cast hiN
    have hi0 : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
    constructor
    · dsimp [c]; positivity
    · dsimp [c]
      apply (div_le_iff₀ haPos).2
      have hquad : 0 ≤ (P-5)*(9*P) := mul_nonneg (by linarith) (by linarith)
      nlinarith only [hiR, hquad]
  have hcsum : (∑ i ∈ Finset.range (3*p), c i) = 6 := by
    dsimp only [c]
    rw [← Finset.sum_div, sum_linear]
    have hcast : ((3*p : ℕ) : ℝ) = 3*P := by dsimp [P]; push_cast; ring
    rw [hcast]
    field_simp [hP.ne'] <;> ring
  have hBD : (100 : ℝ) < B/D := by
    have hratio := choose_ratio_prod n (a+p) (3*p) (by omega : a+p+3*p ≤ n)
    have hindex : a+p+3*p = a+4*p := by omega
    rw [hindex] at hratio
    change B/D = _ at hratio
    rw [hratio]
    apply (one_add_product_gt (Finset.range (3*p)) c hc (by rw [hcsum])).trans_le
    apply Finset.prod_le_prod₀
    · intro i hi
      linarith [(hc i hi).1]
    · intro i hi
      have hiN : i+1 ≤ 3*p := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
      have hiR : (i : ℝ)+1 ≤ 3*P := by dsimp [P]; exact_mod_cast hiN
      have hi0 : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
      let z : ℝ := (n : ℝ)-((a+p : ℕ) : ℝ)-(i : ℝ)
      let v : ℝ := 3*P+2*(i : ℝ)+1
      have hz : z = 3*P^2-2*P-i := by
        dsimp [z]
        push_cast
        rw [haR, hnR]
        change 6*P^2-P-(3*P^2+P)-(i : ℝ) = _
        ring
      have hzPos : 0 < z := by
        rw [hz]
        nlinarith [mul_nonneg hP.le (show 0 ≤ 3*P-5 by linarith)]
      have hzLe : z ≤ 3*P^2 := by rw [hz]; nlinarith only [hP.le, hi0]
      have hv : 0 ≤ v := by dsimp [v]; positivity
      have hdiv : c i ≤ v/z := by
        dsimp [c, v]
        apply (div_le_div_iff₀ haPos hzPos).2
        exact mul_le_mul_of_nonneg_left hzLe hv
      calc
        1+c i ≤ 1+v/z := by linarith only [hdiv]
        _ = (((a+p : ℕ) : ℝ)+(i : ℝ)+1)/((n : ℝ)-((a+p : ℕ) : ℝ)-i) := by
          change 1+v/z = (((a+p : ℕ) : ℝ)+(i : ℝ)+1)/z
          apply (eq_div_iff hzPos.ne').2
          rw [add_mul, one_mul, div_mul_cancel₀ _ hzPos.ne']
          dsimp [z, v]
          push_cast
          rw [haR, hnR]
          change (6*P^2-P-(3*P^2+P)-(i : ℝ))+(3*P+2*(i : ℝ)+1) =
            (3*P^2+P)+(i : ℝ)+1
          ring
  have hABmul : A < (199/100)*B := (div_lt_iff₀ hB).mp hAB
  have hBDmul : 100*D < B := (lt_div_iff₀ hD).mp hBD
  have hfinal : A+D < 2*B := by linarith only [hABmul, hBDmul]
  change (Nat.choose n a : ℝ)+(Nat.choose n (a+4*p) : ℝ) <
    2*(Nat.choose n (a+p) : ℝ) at hfinal
  exact_mod_cast hfinal


private theorem positive_endpoint_actual (p : ℤ) (hp5 : 5 ≤ p) (hpo : Odd p) :
    (original_return_pair p p).1 < (original_return_pair p p).2 := by
  let P : ℕ := p.toNat
  let N : ℕ := P*(6*P-1)
  have hP : (P : ℤ) = p := Int.toNat_of_nonneg (by omega)
  have hP5 : 5 ≤ P := by omega
  have hb : Nat.choose N (3*P^2)+Nat.choose N (3*P^2+4*P) <
      2*Nat.choose N (3*P^2+P) := positive_endpoint_binomial P hP5
  have hc := actual_odd_wrap_counts p p (by omega) hpo (by omega)
  have hhalf1 : p*((6*p-1)+1)/2 = 3*p^2 := by
    have hh : p*((6*p-1)+1) = 2*(3*p^2) := by ring
    omega
  have hhalf3 : p*((6*p-1)+3)/2 = 3*p^2+p := by
    have hh : p*((6*p-1)+3) = 2*(3*p^2+p) := by ring
    omega
  have hhalf9 : p*((6*p-1)+9)/2 = 3*p^2+4*p := by
    have hh : p*((6*p-1)+9) = 2*(3*p^2+4*p) := by ring
    omega
  have hN : (p*(6*p-1)).toNat = N := by
    have hh : p*(6*p-1) = (N : ℤ) := by
      simp only [N, Nat.cast_mul, Nat.cast_sub (show 1 ≤ 6*P by omega),
        Nat.cast_ofNat, Nat.cast_one, hP]
    exact (congrArg Int.toNat hh).trans (Int.toNat_natCast _)
  have hI1 : (3*p^2).toNat = 3*P^2 := by
    have hh : 3*p^2 = ((3*P^2 : ℕ) : ℤ) := by rw [← hP]; push_cast <;> ring
    exact (congrArg Int.toNat hh).trans (Int.toNat_natCast _)
  have hI3 : (3*p^2+p).toNat = 3*P^2+P := by
    have hh : 3*p^2+p = ((3*P^2+P : ℕ) : ℤ) := by rw [← hP]; push_cast <;> ring
    exact (congrArg Int.toNat hh).trans (Int.toNat_natCast _)
  have hI9 : (3*p^2+4*p).toNat = 3*P^2+4*P := by
    have hh : 3*p^2+4*p = ((3*P^2+4*P : ℕ) : ℤ) := by rw [← hP]; push_cast <;> ring
    exact (congrArg Int.toNat hh).trans (Int.toNat_natCast _)
  have hW19 : (original_return_pair p p).1 =
      2*(Nat.choose N (3*P^2)+Nat.choose N (3*P^2+4*P)) := by
    calc
      (original_return_pair p p).1 =
          2*(Nat.choose (p*(6*p-1)).toNat (p*((6*p-1)+1)/2).toNat +
            Nat.choose (p*(6*p-1)).toNat (p*((6*p-1)+9)/2).toNat) := hc.1
      _ = _ := by rw [hhalf1,hhalf9,hN,hI1,hI9]
  have hW33 : (original_return_pair p p).2 = 4*Nat.choose N (3*P^2+P) := by
    calc
      (original_return_pair p p).2 =
          4*Nat.choose (p*(6*p-1)).toNat (p*((6*p-1)+3)/2).toNat := hc.2
      _ = _ := by rw [hhalf3,hN,hI3]
  rw [hW19,hW33]
  omega

/-- For every odd integer p at least five, the original odd-wrap return
comparison is strictly positive throughout the cone t at least p. -/
theorem actual_positive_odd_wrap_cone (p t : ℤ) (hp5 : 5 ≤ p) (hpo : Odd p)
    (hpt : p ≤ t) : (original_return_pair p t).1 < (original_return_pair p t).2 := by
  let P : ℕ := p.toNat
  let S : ℕ := t.toNat
  have hP : (P : ℤ) = p := Int.toNat_of_nonneg (by omega)
  have hS : (S : ℤ) = t := Int.toNat_of_nonneg (by omega)
  have hP2 : 2 ≤ P := by omega
  have hb := positive_endpoint_actual p hp5 hpo
  have hbP : (original_return_pair p (P : ℤ)).1 <
      (original_return_pair p (P : ℤ)).2 := by simpa only [hP] using hb
  obtain ⟨T,hT,_⟩ := actual_odd_wrap_single_crossing p (by omega) hpo
  have hTP : T ≤ P := by
    by_contra h
    have hh := hT.2.1 P hP2 (by omega)
    omega
  by_cases hPS : P = S
  · have ht : t = p := by omega
    simpa only [ht] using hb
  · have hPSlt : P < S := by omega
    have hh := hT.2.2.2 S (by omega)
    simpa only [hS] using hh

end D5.S3.FiniteGroups.BajnokBeattyOddWrapPositiveCone
