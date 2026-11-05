/- GID: D5/S3/FiniteGroups/BajnokBeattySquareDisplacementEnvelope
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattySquareDisplacementEnvelope
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact first-wrap lattice counts admit a second-order envelope uniformly over every odd square displacement. -/

import D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianSecondOrder
import D5.S3.FiniteGroups.BajnokBeattySquareDisplacementProfile

set_option autoImplicit false

namespace D5.S3.FiniteGroups.BajnokBeattySquareDisplacementEnvelope

open BajnokBeattyOddWrapPositiveCone BajnokBeattyOddWrapGaussianEnvelope
open BajnokBeattyOddWrapGaussianUpperEnvelope BajnokBeattyOddWrapGaussianSecondOrder
open BajnokBeattyOddWrapReturnCounts BajnokBeattyAsymmetricGrowth
open BajnokBeattySquareDisplacementProfile
open NearSquareLatticeRigidity BajnokBeattyCayleyNecessity BajnokBeattyFirstReturnDefect
open Finset

/-- The n=3 upper truncation retains the fifth and seventh order terms.
The constant depends on the pointwise bound k/P; no q bound is used. -/
private theorem scaled_log_tail {z P k : ℝ}
    (hP5 : 5 ≤ P) (hk0 : 0 ≤ k) (hk5 : k < 5)
    (hz : 0 ≤ z) (hzk : z ≤ k/P) :
    let B := (3/5)*k^2+3*k^4/(25*(1-k^2/25))
    0 ≤ Real.log ((1+z)/(1-z))-2*z-(2/3)*z^3 ∧
      Real.log ((1+z)/(1-z))-2*z-(2/3)*z^3 ≤
        B/P^2*((2/3)*z^3) := by
  dsimp only
  have hP : 0 < P := by linarith
  have hP2 : 25 ≤ P^2 := by nlinarith [sq_nonneg (P-5)]
  have hk2 : k^2 < 25 := by
    have hh := mul_pos (sub_pos.mpr hk5) (show 0 < 5+k by linarith)
    nlinarith only [hh]
  have hzkP : z*P ≤ k := (le_div_iff₀ hP).mp hzk
  have h2 : z^2*P^2 ≤ k^2 := by
    have h := pow_le_pow_left₀ (mul_nonneg hz hP.le) hzkP 2
    nlinarith only [h]
  have hz2 : z^2 ≤ k^2/25 := by
    have hh := mul_le_mul_of_nonneg_left hP2 (sq_nonneg z)
    nlinarith only [h2,hh]
  have hz1 : z < 1 := by nlinarith [sq_nonneg (z-1)]
  have hd : 0 < 1-z^2 := by nlinarith
  have hd0 : 0 < 1-k^2/25 := by linarith
  have h4 : z^4*P^2 ≤ k^4/25 := by
    have h := mul_le_mul h2 hz2 (sq_nonneg z) (sq_nonneg k)
    nlinarith only [h]
  have hfrac : (z^4*P^2)/(1-z^2) ≤ (k^4/25)/(1-k^2/25) := by
    apply (div_le_div_iff₀ hd hd0).2
    have h₁ := mul_le_mul_of_nonneg_right h4 hd0.le
    have h₂ := mul_le_mul_of_nonneg_left
      (show 1-k^2/25 ≤ 1-z^2 by linarith) (show 0 ≤ k^4/25 by positivity)
    exact h₁.trans h₂
  have hcoef : (3/5)*(z^2*P^2)+3*((z^4*P^2)/(1-z^2)) ≤
      (3/5)*k^2+3*k^4/(25*(1-k^2/25)) := by
    have hid : (k^4/25)/(1-k^2/25) = k^4/(25*(1-k^2/25)) := by rw [div_div]
    rw [hid] at hfrac
    calc
      _ ≤ (3/5)*k^2+3*(k^4/(25*(1-k^2/25))) :=
        add_le_add (mul_le_mul_of_nonneg_left h2 (by norm_num))
          (mul_le_mul_of_nonneg_left hfrac (by norm_num))
      _ = _ := by ring
  have hlo := Real.sum_range_le_log_div hz hz1 2
  have hhi := Real.log_div_le_sum_range_add hz hz1 3
  norm_num [Finset.sum_range_succ] at hlo hhi
  have htail : (2/5)*z^5+2*z^7/(1-z^2) ≤
      ((3/5)*k^2+3*k^4/(25*(1-k^2/25)))/P^2*((2/3)*z^3) := by
    have h := mul_le_mul_of_nonneg_left hcoef
      (show 0 ≤ ((2/3)*z^3)/P^2 by positivity)
    have hid : ((2/3)*z^3)/P^2 *
        ((3/5)*(z^2*P^2)+3*((z^4*P^2)/(1-z^2))) =
        (2/5)*z^5+2*z^7/(1-z^2) := by
      field_simp [hP.ne', hd.ne'] <;> ring
    rw [hid] at h
    convert h using 1 <;> ring
  simp only [div_eq_mul_inv] at hlo hhi htail ⊢
  constructor <;> linarith only [hlo, hhi, htail]

theorem coefficient_bounds {v : ℝ} (hv : 9 ≤ v) :
    let C := 2*(v+1)/(3*(v-1)^2)
    let E := 4/(3*(v-1)^2)
    0 ≤ C ∧ C ≤ 5/48 ∧ 0 ≤ E ∧ E ≤ 1/48 ∧
      v^2*C ≤ (15/16)*v ∧ v*E ≤ (5/2)*(v^2*C) := by
  dsimp only
  have hv0 : 0 < v := by linarith
  have hvm : 0 < v-1 := by linarith
  have hd : 0 < 3*(v-1)^2 := by positivity
  have hC : 0 ≤ 2*(v+1)/(3*(v-1)^2) := by positivity
  have hE : 0 ≤ 4/(3*(v-1)^2) := by positivity
  have hf : 0 ≤ (v-9)*(5*v+3) := mul_nonneg (by linarith) (by linarith)
  have hg : 0 ≤ (v-9)*(13*v-5) := mul_nonneg (by linarith) (by linarith)
  refine ⟨hC, (div_le_iff₀ hd).2 ?_, hE, (div_le_iff₀ hd).2 ?_, ?_, ?_⟩
  · nlinarith only [hf]
  · nlinarith [sq_nonneg (v-9)]
  · rw [← mul_div_assoc]
    apply (div_le_iff₀ hd).2
    have h := mul_nonneg hv0.le hg
    nlinarith only [h]
  · rw [← mul_div_assoc, ← mul_div_assoc, ← mul_div_assoc]
    apply (div_le_div_iff₀ hd hd).2
    have hbase : 4*v ≤ (5/2)*(v^2*(2*(v+1))) := by
      nlinarith [sq_nonneg (v-9), mul_nonneg (sq_nonneg v) (show 0 ≤ v-9 by linarith)]
    have hh := mul_le_mul_of_nonneg_right hbase hd.le
    nlinarith only [hh]

/-- The finite inference. The hypotheses are exact moments and summed tails,
not assumptions of the desired envelope. In particular dy has no upper cutoff. -/
private theorem damped_blocks {P v s L M Tx Ty : ℝ}
    (hP5 : 5 ≤ P) (hv : 9 ≤ v) (hslo : (2/3 : ℝ) ≤ s) (hshi : s ≤ 5/7)
    (hL0 : 0 ≤ L-s) (hM0 : 0 ≤ M-v*s)
    (hLexact : L-s = (2*(v+1)/(3*(v-1)^2))*s^3/P^2 -
      (4/(3*(v-1)^2))*s^3/P^4+Tx)
    (hMexact : M-v*s = (v^2*(2*(v+1)/(3*(v-1)^2)))*s^3/P^2 -
      (v*(4/(3*(v-1)^2)))*s^3/P^4+Ty)
    (hTx0 : 0 ≤ Tx) (hTy0 : 0 ≤ Ty)
    (hTx : Tx ≤ (1107/6076)*(2*(v+1)/(3*(v-1)^2))*s^3/P^4)
    (hTy : Ty ≤ (336555/137788)*(v^2*(2*(v+1)/(3*(v-1)^2)))*s^3/P^4) :
    |Real.exp L+Real.exp (-M)-(Real.exp s+Real.exp (-v*s))-
      (2*(v+1)/(3*(v-1)^2))*s^3*(Real.exp s-v^2*Real.exp (-v*s))/P^2| ≤
        1/(5*P^4) := by
  let C := 2*(v+1)/(3*(v-1)^2)
  let E := 4/(3*(v-1)^2)
  let e := 1/P^2
  let a := C*s^3
  let A := v^2*C*s^3
  let dx := L-s
  let dy := M-v*s
  have hP : 0 < P := by linarith
  have he : 0 < e := by dsimp [e]; positivity
  have he25 : e ≤ 1/25 := by
    dsimp [e]
    apply (div_le_div_iff₀ (pow_pos hP 2) (by norm_num : (0:ℝ)<25)).2
    nlinarith [sq_nonneg (P-5)]
  have he2 : e^2 = 1/P^4 := by dsimp only [e]; field_simp [hP.ne'] <;> ring
  have hs0 : 0 ≤ s := by linarith
  have hs3 : s^3 ≤ 125/343 := by
    have h := pow_le_pow_left₀ hs0 hshi 3
    norm_num at h; exact h
  have hs6 : s^6 ≤ (125/343)^2 := by
    have h := pow_le_pow_left₀ (pow_nonneg hs0 3) hs3 2
    convert h using 1 <;> ring
  obtain ⟨hC0,hC,hE0,hE,hvC,hvE⟩ := coefficient_bounds hv
  change 0 ≤ C at hC0; change C ≤ 5/48 at hC
  change 0 ≤ E at hE0; change E ≤ 1/48 at hE
  change v^2*C ≤ (15/16)*v at hvC
  change v*E ≤ (5/2)*(v^2*C) at hvE
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hv0 : 0 < v := by linarith
  have hdx : dx = a*e-E*s^3*e^2+Tx := by
    rw [he2]
    dsimp only [dx,a,e,C,E]
    convert hLexact using 1 <;> ring
  have hdy : dy = A*e-v*E*s^3*e^2+Ty := by
    rw [he2]
    dsimp only [dy,A,e,C,E]
    convert hMexact using 1 <;> ring
  have htx : Tx ≤ (1107/6076)*a*e^2 := by
    rw [he2]
    dsimp only [a,C]
    convert hTx using 1 <;> ring
  have hty : Ty ≤ (5/2)*A*e^2 := by
    have h : Ty ≤ (336555/137788)*A*e^2 := by
      rw [he2]
      dsimp only [A,C]
      convert hTy using 1 <;> ring
    have hh := mul_nonneg hA (sq_nonneg e)
    nlinarith only [h,hh]
  have htxsmall : Tx ≤ (s^3/48)*e^2 := by
    have hcoef : (1107/6076)*C ≤ 1/48 := by linarith only [hC]
    have hh := mul_le_mul_of_nonneg_right hcoef
      (mul_nonneg (pow_nonneg hs0 3) (sq_nonneg e))
    have ht : Tx ≤ (1107/6076)*(C*s^3)*e^2 := htx
    nlinarith only [ht,hh]
  have hEsmall : E*s^3*e^2 ≤ (s^3/48)*e^2 := by
    have h := mul_le_mul_of_nonneg_right hE
      (mul_nonneg (pow_nonneg hs0 3) (sq_nonneg e))
    nlinarith only [h]
  -- Difference of two nonnegative quantities: use their maximum, not sum.
  have hdxerr : |dx-a*e| ≤ (s^3/48)*e^2 := by
    rw [hdx]
    apply abs_le.mpr
    constructor <;> nlinarith only [htxsmall,hEsmall,hTx0,
      mul_nonneg hE0 (mul_nonneg (pow_nonneg hs0 3) (sq_nonneg e))]
  have hdyerr : |dy-A*e| ≤ (5/2)*A*e^2 := by
    have hEc := mul_le_mul_of_nonneg_right hvE
      (mul_nonneg (pow_nonneg hs0 3) (sq_nonneg e))
    have hEc' : v*E*s^3*e^2 ≤ (5/2)*A*e^2 := by
      dsimp only [A]; nlinarith only [hEc]
    rw [hdy]
    apply abs_le.mpr
    constructor <;> nlinarith only [hEc',hty,hTy0,
      mul_nonneg hv0.le (mul_nonneg hE0
        (mul_nonneg (pow_nonneg hs0 3) (sq_nonneg e)))]
  have ha_bound : a ≤ (5/48)*(125/343) := by
    exact mul_le_mul hC hs3 (pow_nonneg hs0 3) (by norm_num)
  have hdx_bound : dx ≤ e/25 := by
    have het : a*e^2 ≤ ((5/48)*(125/343))*(e/25) := by
      have hh := mul_le_mul he25 ha_bound ha (by norm_num : (0:ℝ)≤1/25)
      have ht := mul_le_mul_of_nonneg_right hh he.le
      nlinarith only [ht]
    have hl := mul_le_mul_of_nonneg_right ha_bound he.le
    have hdrop : 0 ≤ E*s^3*e^2 := by positivity
    nlinarith only [hdx,htx,het,hl,hdrop,he.le]
  have hdx1 : dx ≤ 1 := by nlinarith only [hdx_bound,he25]
  have hdy_bound : dy ≤ (33/32)*v*s^3*e := by
    have heA := mul_le_mul_of_nonneg_right he25 (mul_nonneg hA he.le)
    have hAc := mul_le_mul_of_nonneg_right hvC
      (mul_nonneg (pow_nonneg hs0 3) he.le)
    have hdrop : 0 ≤ v*E*s^3*e^2 := by positivity
    have hAc' : A*e ≤ (15/16)*v*s^3*e := by
      dsimp only [A]; nlinarith only [hAc]
    nlinarith only [hdy,hty,heA,hAc',hdrop]
  have hdxsq : dx^2 ≤ e^2/625 := by
    have h := pow_le_pow_left₀ hL0 hdx_bound 2
    nlinarith only [h]
  have hdysq : dy^2 ≤ (1089/1024)*v^2*s^6*e^2 := by
    have h := pow_le_pow_left₀ hM0 hdy_bound 2
    convert h using 1 <;> ring
  have hexps : Real.exp s ≤ 9/4 :=
    ((Real.exp_lt_exp.mpr (by linarith : s < 3/4)).trans exp_three_quarters_lt).le
  have htail := real_rational_tail_on_ray hv hslo
  have hv2exp : v^2*Real.exp (-v*s) ≤ 9/10 := htail.2.2.le
  have hvexp : v*Real.exp (-v*s) ≤ 1/10 := by
    have hh := mul_nonneg (show 0 ≤ v-9 by linarith)
      (mul_nonneg hv0.le (Real.exp_pos (-v*s)).le)
    nlinarith only [hv2exp,hh]
  have hLexp : Real.exp L = Real.exp s*Real.exp dx := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [dx]; ring
  have hMexp : Real.exp (-M) = Real.exp (-v*s)*Real.exp (-dy) := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [dy]; ring
  have hxp : |Real.exp L-Real.exp s*(1+a*e)| ≤
      Real.exp s*((3/4)*dx^2+(s^3/48)*e^2) := by
    have hid : Real.exp L-Real.exp s*(1+a*e) =
        Real.exp s*((Real.exp dx-1-dx)+(dx-a*e)) := by
      rw [hLexp]; ring
    rw [hid,abs_mul,abs_of_pos (Real.exp_pos s)]
    exact mul_le_mul_of_nonneg_left
      ((abs_add_le _ _).trans (add_le_add
        (exp_positive_quadratic_remainder hL0 hdx1) hdxerr)) (Real.exp_pos s).le
  have hyp : |Real.exp (-M)-Real.exp (-v*s)*(1-A*e)| ≤
      Real.exp (-v*s)*(dy^2/2+(5/2)*A*e^2) := by
    have hid : Real.exp (-M)-Real.exp (-v*s)*(1-A*e) =
        Real.exp (-v*s)*((Real.exp (-dy)-1+dy)-(dy-A*e)) := by
      rw [hMexp]; ring
    rw [hid,abs_mul,abs_of_pos (Real.exp_pos (-v*s))]
    exact mul_le_mul_of_nonneg_left
      ((abs_sub _ _).trans (add_le_add
        (exp_negative_quadratic_remainder hM0) hdyerr)) (Real.exp_pos (-v*s)).le
  have hxblock : |Real.exp L-Real.exp s*(1+a*e)| ≤
      (271419/13720000)*e^2 := by
    have hi := add_le_add (mul_le_mul_of_nonneg_left hdxsq (by norm_num : (0:ℝ)≤3/4))
      (mul_le_mul_of_nonneg_right (show s^3/48 ≤ (125/343)/48 by linarith) (sq_nonneg e))
    have hc := mul_le_mul_of_nonneg_left hi (Real.exp_pos s).le
    have hec := mul_le_mul_of_nonneg_right hexps
      (show 0 ≤ (3/4)*(e^2/625)+((125/343)/48)*e^2 by positivity)
    nlinarith only [hxp,hc,hec]
  have hyblock : |Real.exp (-M)-Real.exp (-v*s)*(1-A*e)| ≤
      (71788125/481890304)*e^2 := by
    have hAc := mul_le_mul_of_nonneg_right hvC (pow_nonneg hs0 3)
    have hinside : dy^2/2+(5/2)*A*e^2 ≤
        ((1089/2048)*v^2*s^6+(75/32)*v*s^3)*e^2 := by
      have hh := mul_le_mul_of_nonneg_right hAc (sq_nonneg e)
      have hh' : A*e^2 ≤ (15/16)*v*s^3*e^2 := by
        dsimp only [A]; nlinarith only [hh]
      nlinarith only [hdysq,hh']
    have hw := mul_le_mul_of_nonneg_left hinside (Real.exp_pos (-v*s)).le
    have h₁ := mul_le_mul_of_nonneg_right hv2exp
      (show 0 ≤ (1089/2048)*s^6*e^2 by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hvexp
      (show 0 ≤ (75/32)*s^3*e^2 by positivity)
    have h₃ := mul_le_mul_of_nonneg_right hs6 (sq_nonneg e)
    have h₄ := mul_le_mul_of_nonneg_right hs3 (sq_nonneg e)
    nlinarith only [hyp,hw,h₁,h₂,h₃,h₄]
  have hid : Real.exp L+Real.exp (-M)-(Real.exp s+Real.exp (-v*s))-
      C*s^3*(Real.exp s-v^2*Real.exp (-v*s))/P^2 =
      (Real.exp L-Real.exp s*(1+a*e))+
        (Real.exp (-M)-Real.exp (-v*s)*(1-A*e)) := by
    dsimp [a,A,e]; ring
  change |Real.exp L+Real.exp (-M)-(Real.exp s+Real.exp (-v*s))-
      C*s^3*(Real.exp s-v^2*Real.exp (-v*s))/P^2| ≤ 1/(5*P^4)
  rw [hid]
  have hh := (abs_add_le _ _).trans (add_le_add hxblock hyblock)
  have hrat : (271419/13720000:ℝ)+(71788125/481890304) ≤ 1/5 := by norm_num
  have hm := mul_le_mul_of_nonneg_right hrat (sq_nonneg e)
  rw [he2] at hh hm
  calc
    _ ≤ (271419/13720000)*(1/P^4)+(71788125/481890304)*(1/P^4) := hh
    _ ≤ (1/5)*(1/P^4) := by nlinarith only [hm]
    _ = 1/(5*P^4) := by ring

/-- Exact finite-binomial inference. The integer half-offset is represented
by r and its exact natural identity, with no real binomial interpolation. -/
private theorem finite_binomial_envelope (p q n a r : ℕ)
    (hp5 : 5 ≤ p) (hq3 : 3 ≤ q)
    (hr : 2*r = (q-1)*p) (hna : n+p = 2*a)
    (hfit : a+(q+1)*r ≤ n) :
    let s : ℝ := (((q : ℝ)^2-1)*(p : ℝ)^2)/(2*((n : ℝ)+1))
    let v : ℝ := (q : ℝ)^2
    let C : ℝ := 2*(v+1)/(3*(v-1)^2)
    (2/3 : ℝ) ≤ s → s ≤ 5/7 →
    |((Nat.choose n a : ℝ)+Nat.choose n (a+(q+1)*r))/(Nat.choose n (a+r) : ℝ)-
      (Real.exp s+Real.exp (-v*s))-C*s^3*(Real.exp s-v^2*Real.exp (-v*s))/(p : ℝ)^2| ≤
        1/(5*(p : ℝ)^4) := by
  dsimp only
  let P : ℝ := p
  let Q : ℝ := q
  let R : ℝ := (n : ℝ)+1
  let v := Q^2
  let C := 2*(v+1)/(3*(v-1)^2)
  let E := 4/(3*(v-1)^2)
  let s := (Q^2-1)*P^2/(2*R)
  let A : ℝ := Nat.choose n a
  let B : ℝ := Nat.choose n (a+r)
  let D : ℝ := Nat.choose n (a+(q+1)*r)
  change (2/3 : ℝ) ≤ s → s ≤ 5/7 →
    |(A+D)/B-(Real.exp s+Real.exp (-v*s))-
      C*s^3*(Real.exp s-v^2*Real.exp (-v*s))/P^2| ≤ 1/(5*P^4)
  intro hslo hshi
  have hP5 : 5 ≤ P := by dsimp only [P]; exact_mod_cast hp5
  have hQ3 : 3 ≤ Q := by dsimp only [Q]; exact_mod_cast hq3
  have hP : 0 < P := by linarith
  have hQ : 0 < Q := by linarith
  have hQsq : 9 ≤ Q^2 := by nlinarith only [hQ3,sq_nonneg (Q-3)]
  have hv : 9 ≤ v := hQsq
  have hQm : 0 < Q^2-1 := by linarith only [hQsq]
  have hR : 0 < R := by dsimp [R]; positivity
  have hrR : (r : ℝ) = (Q-1)*P/2 := by
    have hh : 2*(r : ℝ) = (Q-1)*P := by
      have hc := congrArg (fun j : ℕ => (j : ℝ)) hr
      rw [Nat.cast_mul,Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ q)] at hc
      norm_num at hc
      exact hc
    linarith only [hh]
  have hnaR : (n : ℝ)+P = 2*(a : ℝ) := by dsimp only [P]; exact_mod_cast hna
  have hqrR : ((q*r : ℕ) : ℝ) = Q*(r : ℝ) := by push_cast; rfl
  have hBR : 2*((a+r : ℕ) : ℝ)-(n : ℝ) = Q*P := by
    push_cast
    nlinarith only [hrR,hnaR]
  have hfitB : a+r ≤ n := by
    have h : r ≤ (q+1)*r := by rw [add_mul,one_mul]; omega
    omega
  have hA : 0 < A := by dsimp [A]; exact_mod_cast Nat.choose_pos (by omega : a ≤ n)
  have hB : 0 < B := by dsimp [B]; exact_mod_cast Nat.choose_pos hfitB
  have hD : 0 < D := by dsimp [D]; exact_mod_cast Nat.choose_pos hfit
  have hsR : 2*s*R = (Q^2-1)*P^2 := by
    dsimp only [s]; field_simp [hR.ne'] <;> ring
  have hbandR : 7*(Q^2-1)*P^2 ≤ 10*R := by
    have hh := mul_le_mul_of_nonneg_right hshi hR.le
    nlinarith only [hsR,hh]
  have hqratio : 8*Q ≤ 3*(Q^2-1) := by
    have hh := mul_nonneg (show 0 ≤ Q-3 by linarith) (show 0 ≤ 3*Q+1 by linarith)
    nlinarith only [hh]
  have hq2ratio : 8*Q^2 ≤ 9*(Q^2-1) := by linarith only [hQsq]
  let x (i : ℕ) : ℝ := (P+2*(i : ℝ)+1)/R
  let y (i : ℕ) : ℝ := (Q*P+2*(i : ℝ)+1)/R
  have hxP (i : ℕ) (hi : i ∈ range r) : x i ≤ (15/28)/P := by
    have hiR : (i : ℝ)+1 ≤ (r : ℝ) := by exact_mod_cast Nat.succ_le_of_lt (mem_range.mp hi)
    have hnum : P+2*(i : ℝ)+1 ≤ Q*P := by nlinarith only [hiR,hrR]
    have hh := mul_le_mul_of_nonneg_right hqratio (pow_nonneg hP.le 2)
    have hm := mul_le_mul_of_nonneg_right hnum (show 0 ≤ 28*P by positivity)
    dsimp only [x]
    apply (div_le_div_iff₀ hR hP).2
    nlinarith only [hh,hm,hbandR]
  have hyP (i : ℕ) (hi : i ∈ range (q*r)) : y i ≤ (45/28)/P := by
    have hiR : (i : ℝ)+1 ≤ Q*(r : ℝ) := by
      rw [← hqrR]; exact_mod_cast Nat.succ_le_of_lt (mem_range.mp hi)
    have hnum : Q*P+2*(i : ℝ)+1 ≤ Q^2*P := by
      have hh := congrArg (fun z : ℝ => Q*z) hrR
      nlinarith only [hiR,hh]
    have hh := mul_le_mul_of_nonneg_right hq2ratio (pow_nonneg hP.le 2)
    have hm := mul_le_mul_of_nonneg_right hnum (show 0 ≤ 28*P by positivity)
    dsimp only [y]
    apply (div_le_div_iff₀ hR hP).2
    nlinarith only [hh,hm,hbandR]
  have hx (i : ℕ) (hi : i ∈ range r) : 0 ≤ x i ∧ x i < 1 := by
    have hsmall : (15/28 : ℝ)/P ≤ 3/28 := by
      apply (div_le_iff₀ hP).2; linarith only [hP5]
    exact ⟨by dsimp [x]; positivity, lt_of_le_of_lt ((hxP i hi).trans hsmall) (by norm_num)⟩
  have hy (i : ℕ) (hi : i ∈ range (q*r)) : 0 ≤ y i ∧ y i < 1 := by
    have hsmall : (45/28 : ℝ)/P ≤ 9/28 := by
      apply (div_le_iff₀ hP).2; linarith only [hP5]
    exact ⟨by dsimp [y]; positivity, lt_of_le_of_lt ((hyP i hi).trans hsmall) (by norm_num)⟩
  have hxrem (i : ℕ) (hi : i ∈ range r) :
      0 ≤ Real.log ((1+x i)/(1-x i))-2*x i-(2/3)*(x i)^3 ∧
      Real.log ((1+x i)/(1-x i))-2*x i-(2/3)*(x i)^3 ≤
        (1107/6076)/P^2*((2/3)*(x i)^3) := by
    have hh := scaled_log_tail hP5 (by norm_num : (0:ℝ)≤15/28)
      (by norm_num : (15/28:ℝ)<5) (hx i hi).1 (hxP i hi)
    norm_num at hh
    constructor <;> linarith only [hh.1, hh.2]
  have hyrem (i : ℕ) (hi : i ∈ range (q*r)) :
      0 ≤ Real.log ((1+y i)/(1-y i))-2*y i-(2/3)*(y i)^3 ∧
      Real.log ((1+y i)/(1-y i))-2*y i-(2/3)*(y i)^3 ≤
        (336555/137788)/P^2*((2/3)*(y i)^3) := by
    have hh := scaled_log_tail hP5 (by norm_num : (0:ℝ)≤45/28)
      (by norm_num : (45/28:ℝ)<5) (hy i hi).1 (hyP i hi)
    norm_num at hh
    constructor <;> linarith only [hh.1, hh.2]
  have hxp (i : ℕ) (hi : i ∈ range r) : 0 < (1+x i)/(1-x i) :=
    div_pos (by linarith [(hx i hi).1]) (by linarith [(hx i hi).2])
  have hyp (i : ℕ) (hi : i ∈ range (q*r)) : 0 < (1+y i)/(1-y i) :=
    div_pos (by linarith [(hy i hi).1]) (by linarith [(hy i hi).2])
  have hAB : A/B = ∏ i ∈ range r, (1+x i)/(1-x i) := by
    exact choose_ratio_centered_prod n a r P R hfitB rfl (by linarith only [hnaR])
  have hBD : B/D = ∏ i ∈ range (q*r), (1+y i)/(1-y i) := by
    have hh := choose_ratio_centered_prod n (a+r) (q*r) (Q*P) R
      (by convert hfit using 1 <;> ring) rfl hBR.symm
    simpa only [show a+r+q*r = a+(q+1)*r by ring] using hh
  have hxsum : 2*(∑ i ∈ range r, x i) = s := by
    dsimp only [x]
    rw [← sum_div, sum_linear, hrR]
    dsimp only [s]; field_simp [hR.ne'] <;> ring
  have hysum : 2*(∑ i ∈ range (q*r), y i) = v*s := by
    dsimp only [y]
    rw [← sum_div, sum_linear, hqrR, hrR]
    dsimp only [s,v]; field_simp [hR.ne'] <;> ring
  let U := (2/3)*(∑ i ∈ range r, (x i)^3)
  let V := (2/3)*(∑ i ∈ range (q*r), (y i)^3)
  have hU : U = C*s^3/P^2-E*s^3/P^4 := by
    dsimp only [U,x]
    simp_rw [div_pow]
    rw [← sum_div, sum_cubic, hrR]
    dsimp [C,E,v,s]
    field_simp [hR.ne',hP.ne',hQm.ne'] <;> ring
  have hV : V = v^2*C*s^3/P^2-v*E*s^3/P^4 := by
    dsimp only [V,y]
    simp_rw [div_pow]
    rw [← sum_div, sum_cubic, hqrR, hrR]
    dsimp [C,E,v,s]
    field_simp [hR.ne',hP.ne',hQm.ne'] <;> ring
  let L := Real.log (A/B)
  let M := Real.log (B/D)
  have hlogL : L = ∑ i ∈ range r, Real.log ((1+x i)/(1-x i)) := by
    dsimp [L]; rw [hAB,Real.log_prod (fun i hi => (hxp i hi).ne')]
  have hlogM : M = ∑ i ∈ range (q*r), Real.log ((1+y i)/(1-y i)) := by
    dsimp [M]; rw [hBD,Real.log_prod (fun i hi => (hyp i hi).ne')]
  let Tx := ∑ i ∈ range r, (Real.log ((1+x i)/(1-x i))-2*x i-(2/3)*(x i)^3)
  let Ty := ∑ i ∈ range (q*r), (Real.log ((1+y i)/(1-y i))-2*y i-(2/3)*(y i)^3)
  have hTx0 : 0 ≤ Tx := sum_nonneg (fun i hi => (hxrem i hi).1)
  have hTy0 : 0 ≤ Ty := sum_nonneg (fun i hi => (hyrem i hi).1)
  have hTx : Tx ≤ (1107/6076)/P^2*U := by
    calc
      _ ≤ ∑ i ∈ range r, (1107/6076)/P^2*((2/3)*(x i)^3) :=
        sum_le_sum (fun i hi => (hxrem i hi).2)
      _ = _ := by rw [← mul_sum,← mul_sum]
  have hTy : Ty ≤ (336555/137788)/P^2*V := by
    calc
      _ ≤ ∑ i ∈ range (q*r), (336555/137788)/P^2*((2/3)*(y i)^3) :=
        sum_le_sum (fun i hi => (hyrem i hi).2)
      _ = _ := by rw [← mul_sum,← mul_sum]
  have hLexact : L-s = C*s^3/P^2-E*s^3/P^4+Tx := by
    have hid : Tx = L-2*(∑ i ∈ range r, x i)-U := by
      dsimp [Tx,U]
      rw [sum_sub_distrib,sum_sub_distrib,← mul_sum,← mul_sum,← hlogL]
    rw [hxsum,hU] at hid
    linarith only [hid]
  have hMexact : M-v*s = v^2*C*s^3/P^2-v*E*s^3/P^4+Ty := by
    have hid : Ty = M-2*(∑ i ∈ range (q*r), y i)-V := by
      dsimp [Ty,V]
      rw [sum_sub_distrib,sum_sub_distrib,← mul_sum,← mul_sum,← hlogM]
    rw [hysum,hV] at hid
    linarith only [hid]
  have hL0 : 0 ≤ L-s := by
    have hh := sum_le_sum (fun i hi =>
      Real.sum_range_le_log_div (hx i hi).1 (hx i hi).2 1)
    norm_num [Finset.sum_range_succ] at hh
    rw [← mul_sum,← hlogL] at hh
    linarith only [hh,hxsum]
  have hM0 : 0 ≤ M-v*s := by
    have hh := sum_le_sum (fun i hi =>
      Real.sum_range_le_log_div (hy i hi).1 (hy i hi).2 1)
    norm_num [Finset.sum_range_succ] at hh
    rw [← mul_sum,← hlogM] at hh
    linarith only [hh,hysum]
  have hs0 : 0 ≤ s := by linarith
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hTx' : Tx ≤ (1107/6076)*C*s^3/P^4 := by
    have hUle : U ≤ C*s^3/P^2 := by
      rw [hU]; exact sub_le_self _ (by positivity)
    have hh := mul_le_mul_of_nonneg_left hUle
      (show 0 ≤ (1107/6076:ℝ)/P^2 by positivity)
    have hid : (1107/6076)/P^2*(C*s^3/P^2) = (1107/6076)*C*s^3/P^4 := by ring
    rw [hid] at hh
    exact hTx.trans hh
  have hTy' : Ty ≤ (336555/137788)*(v^2*C)*s^3/P^4 := by
    have hVle : V ≤ v^2*C*s^3/P^2 := by
      rw [hV]; exact sub_le_self _ (by positivity)
    have hh := mul_le_mul_of_nonneg_left hVle
      (show 0 ≤ (336555/137788:ℝ)/P^2 by positivity)
    have hid : (336555/137788)/P^2*(v^2*C*s^3/P^2) =
        (336555/137788)*(v^2*C)*s^3/P^4 := by ring
    rw [hid] at hh
    exact hTy.trans hh
  have hh := damped_blocks hP5 hv hslo hshi hL0 hM0
    hLexact hMexact hTx0 hTy0 hTx' hTy'
  have hexpL : Real.exp L = A/B := Real.exp_log (div_pos hA hB)
  have hexpM : Real.exp (-M) = D/B := by
    dsimp [M]; rw [Real.exp_neg,Real.exp_log (div_pos hB hD),inv_div]
  rw [hexpL,hexpM,← add_div] at hh
  exact hh

/-- Uniform finite-count second-order envelope on the complete signed domain.
Both lattices are COMPLETE integer spans of the displayed actual generators. -/
theorem actual_square_displacement_envelope (p q t : ℤ)
    (hp5 : 5 ≤ p) (hpo : Odd p) (hq3 : 3 ≤ q) (hqo : Odd q) (ht : q+1 ≤ 2*t) :
    let m : ℤ := 2*q*t-1
    let n : ℕ := (p*m).toNat
    let v1a : Plane := ![p*(m-1)/2,p*(m+1)/2]
    let v2a : Plane := ![p*(m-q^2)/2,-(p*(m+q^2)/2)]
    let v1q : Plane := ![p*(m-q)/2,p*(m+q)/2]
    let v2q : Plane := ![p*(m-q)/2,-(p*(m+q)/2)]
    let Ka := Submodule.span ℤ (Set.range ![v1a,v2a])
    let Kq := Submodule.span ℤ (Set.range ![v1q,v2q])
    let Fa : Plane →+ (Plane ⧸ Ka) := Ka.mkQ.toAddMonoidHom
    let Fq : Plane →+ (Plane ⧸ Kq) := Kq.mkQ.toAddMonoidHom
    let Wa := W Fa n
    let Wq := W Fq n
    let s : ℝ := (((q : ℝ)^2-1)*(p : ℝ)^2)/(2*((n : ℝ)+1))
    let nu : ℝ := (q : ℝ)^2
    let C : ℝ := 2*(nu+1)/(3*(nu-1)^2)
    let G : ℝ := Real.exp s+Real.exp (-nu*s)
    let H : ℝ := C*s^3*(Real.exp s-nu^2*Real.exp (-nu*s))
    (2/3 : ℝ) ≤ s → s ≤ 5/7 →
      |2*(Wa : ℝ)/(Wq : ℝ)-G-H/(p : ℝ)^2| ≤ 1/(5*(p : ℝ)^4) := by
  classical
  let m : ℤ := 2*q*t-1
  let n : ℕ := (p*m).toNat
  let v1a : Plane := ![p*(m-1)/2,p*(m+1)/2]
  let v2a : Plane := ![p*(m-q^2)/2,-(p*(m+q^2)/2)]
  let v1q : Plane := ![p*(m-q)/2,p*(m+q)/2]
  let v2q : Plane := ![p*(m-q)/2,-(p*(m+q)/2)]
  let Ka := Submodule.span ℤ (Set.range ![v1a,v2a])
  let Kq := Submodule.span ℤ (Set.range ![v1q,v2q])
  let Fa : Plane →+ (Plane ⧸ Ka) := Ka.mkQ.toAddMonoidHom
  let Fq : Plane →+ (Plane ⧸ Kq) := Kq.mkQ.toAddMonoidHom
  let P := p.toNat
  let Q := q.toNat
  let a := (q*p*t).toNat
  let r := (((q-1)*p)/2).toNat
  have hp : 0 < p := by omega
  have hq : 0 < q := by omega
  have ht0 : 0 < t := by omega
  have hqm : q^2 < m := by
    have hh := mul_le_mul_of_nonneg_left ht hq.le
    dsimp [m]; nlinarith only [hh,hq3]
  have hm : 0 < m := by nlinarith [sq_nonneg q]
  have hqmo : Odd m := ⟨q*t-1,by dsimp [m]; ring⟩
  have hq2o : Odd (q^2) := by simpa only [pow_two] using hqo.mul hqo
  have hq2 : 0 < q^2 := pow_pos hq 2
  have h1m : 1 < m := by nlinarith [sq_nonneg (q-3)]
  have hq_m : q < m := by nlinarith [sq_nonneg (q-3)]
  have hP : (P : ℤ) = p := Int.toNat_of_nonneg hp.le
  have hQ : (Q : ℤ) = q := Int.toNat_of_nonneg hq.le
  have hP5 : 5 ≤ P := by omega
  have hQ3 : 3 ≤ Q := by omega
  have hn : (n : ℤ) = p*m := Int.toNat_of_nonneg (mul_pos hp hm).le
  have ha : (a : ℤ) = q*p*t := Int.toNat_of_nonneg (by positivity)
  have hdiv : 2 ∣ (q-1)*p := by
    simpa only [mul_comm] using ((hqo.sub_odd odd_one).mul_left p).two_dvd
  have hr2 : 2*((q-1)*p/2) = (q-1)*p := by
    simpa only [mul_comm] using Int.ediv_mul_cancel hdiv
  have hr0 : 0 ≤ (q-1)*p/2 := by
    have hh : 0 ≤ (q-1)*p := mul_nonneg (by omega) hp.le
    nlinarith only [hr2,hh]
  have hr : (r : ℤ) = (q-1)*p/2 := Int.toNat_of_nonneg hr0
  have hr2' : 2*(r : ℤ) = (q-1)*p := by rw [hr]; exact hr2
  have hQr : ((Q-1 : ℕ) : ℤ) = q-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ Q)]; push_cast; rw [hQ]
  have hnr : 2*r = (Q-1)*P := by
    have hh : ((2*r : ℕ) : ℤ) = (((Q-1)*P : ℕ) : ℤ) := by
      simp only [Nat.cast_mul,Nat.cast_ofNat,hQr,hP]
      exact hr2'
    exact_mod_cast hh
  have hna : n+P = 2*a := by
    have hh : ((n+P : ℕ) : ℤ) = ((2*a : ℕ) : ℤ) := by
      push_cast; rw [hn,hP,ha]; dsimp [m]; ring
    exact_mod_cast hh
  have hfit : a+(Q+1)*r ≤ n := by
    have hh : ((a+(Q+1)*r : ℕ) : ℤ) ≤ (n : ℤ) := by
      push_cast; rw [ha,hQ,hn]
      have hgap := mul_pos hp (sub_pos.mpr hqm)
      have hrr := congrArg (fun z : ℤ => (q+1)*z) hr2'
      dsimp only [m] at hgap ⊢
      nlinarith only [hrr,hgap]
    exact_mod_cast hh
  have hhalf (b : ℤ) (hbo : Odd b) : 2*(p*(m+b)/2) = p*(m+b) := by
    simpa only [mul_comm] using Int.ediv_mul_cancel (((hqmo.add_odd hbo).mul_left p).two_dvd)
  have hi1 : (p*(m+1)/2).toNat = a := by
    have hh : p*(m+1)/2 = (a : ℤ) := by
      have hc := hhalf 1 odd_one
      rw [ha]; dsimp [m] at hc; nlinarith only [hc]
    rw [hh,Int.toNat_natCast]
  have hiq : (p*(m+q)/2).toNat = a+r := by
    have hh : p*(m+q)/2 = ((a+r : ℕ) : ℤ) := by
      have hc := hhalf q hqo
      push_cast; rw [ha]; dsimp [m] at hc; nlinarith only [hc,hr2']
    rw [hh,Int.toNat_natCast]
  have hiq2 : (p*(m+q^2)/2).toNat = a+(Q+1)*r := by
    have hh : p*(m+q^2)/2 = ((a+(Q+1)*r : ℕ) : ℤ) := by
      have hc := hhalf (q^2) hq2o
      have hrr := congrArg (fun z : ℤ => (q+1)*z) hr2'
      push_cast; rw [ha,hQ]; dsimp [m] at hc
      nlinarith only [hc,hrr]
    rw [hh,Int.toNat_natCast]
  obtain ⟨_,hv1a,hv2a,_⟩ := asymmetric_rank_one_actual_data p m 1 (q^2)
    hp hpo hqmo odd_one hq2o (by norm_num) h1m hq2 hqm
  obtain ⟨_,hv1q,hv2q,_⟩ := asymmetric_rank_one_actual_data p m q q
    hp hpo hqmo hqo hqo hq hq_m hq hq_m
  have hWa : W Fa n = 2*(Nat.choose n a+Nat.choose n (a+(Q+1)*r)) := by
    have hh := odd_boundary_count_of_sumDiff p m 1 (q^2) v1a v2a
      hp hpo hqmo odd_one hq2o (by norm_num) h1m hq2 hqm hv1a hv2a
    change W Fa n = 2*(Nat.choose n (p*(m+1)/2).toNat+
      Nat.choose n (p*(m+q^2)/2).toNat) at hh
    simpa only [hi1,hiq2] using hh
  have hWq : W Fq n = 4*Nat.choose n (a+r) := by
    have hh := odd_boundary_count_of_sumDiff p m q q v1q v2q
      hp hpo hqmo hqo hqo hq hq_m hq hq_m hv1q hv2q
    change W Fq n = 2*(Nat.choose n (p*(m+q)/2).toNat+
      Nat.choose n (p*(m+q)/2).toNat) at hh
    rw [hiq] at hh; omega
  -- Positivity comes from exact finite binomial positivity, before division.
  have hBr : a+r ≤ n := by
    have hh : r ≤ (Q+1)*r := by rw [add_mul,one_mul]; omega
    omega
  have hBpos : (0 : ℝ) < (Nat.choose n (a+r) : ℝ) := by
    exact_mod_cast Nat.choose_pos hBr
  have hWqpos : (0 : ℝ) < (W Fq n : ℝ) := by
    rw [hWq]
    exact_mod_cast Nat.mul_pos (by decide : 0 < 4) (Nat.choose_pos hBr)
  have hratio : 2*(W Fa n : ℝ)/(W Fq n : ℝ) =
      ((Nat.choose n a : ℝ)+Nat.choose n (a+(Q+1)*r))/(Nat.choose n (a+r) : ℝ) := by
    apply (div_eq_iff hWqpos.ne').2
    rw [hWa,hWq]; push_cast
    field_simp [hBpos.ne'] <;> ring
  have hPR : (P : ℝ) = (p : ℝ) := by exact_mod_cast hP
  have hQR : (Q : ℝ) = (q : ℝ) := by exact_mod_cast hQ
  have hh := finite_binomial_envelope P Q n a r hP5 hQ3 hnr hna hfit
  dsimp only at hh ⊢
  rw [hPR,hQR] at hh
  rw [hratio]
  exact hh

end D5.S3.FiniteGroups.BajnokBeattySquareDisplacementEnvelope
