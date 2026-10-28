/- GID: D5/S3/Zeros/LeeYang/FiolDoubleHubPhase
   generality: I
   mirror-B: D5/B/S3/Zeros/LeeYang/FiolDoubleHubPhase
   mirror-E: none(waiver:analytic-family-proof)
   anchors: []
   utility: none
   digest: All-parameter physical double-hub phase identities. -/
import D5.S3.Zeros.LeeYang.FiolDoubleHubReciprocal
import D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Order.Fin.InsertNth

open scoped BigOperators
open Polynomial Finset
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Zeros.LeeYang
open FiolDoubleHubEndpoint
namespace FiolDoubleHub
noncomputable def ep (x : ℝ) : ℂ := Complex.exp ((x:ℂ)*Complex.I)

private theorem ep_add (x y : ℝ) : ep (x+y) = ep x*ep y := by
  simp only [ep,Complex.ofReal_add,add_mul,Complex.exp_add]

theorem ep_pow (x : ℝ) (n : ℕ) : ep x^n = ep (x*n) := by
  rw [ep,← Complex.exp_nat_mul]
  unfold ep
  congr 1
  push_cast
  ring

private theorem ep_cos (x : ℝ) : ep x+ep (-x) = ((2*Real.cos x:ℝ):ℂ) := by
  simp only [ep,Complex.exp_ofReal_mul_I,Real.cos_neg,Real.sin_neg]
  push_cast
  ring

private theorem H_phase (r : ℕ) (theta : ℝ) :
    (H r).eval₂ Complex.ofRealHom (ep theta) =
      ep ((r:ℝ)*theta/2) * ((2*Real.cos ((r:ℝ)*theta/2):ℝ):ℂ) := by
  simp only [H,Polynomial.eval₂_add,Polynomial.eval₂_one,Polynomial.eval₂_pow,
    Polynomial.eval₂_X,ep_pow]
  rw [← ep_cos,mul_add,← ep_add,← ep_add]
  rw [show (r:ℝ)*theta/2+(r:ℝ)*theta/2 = theta*r by ring,
    show (r:ℝ)*theta/2+-((r:ℝ)*theta/2) = 0 by ring]
  simp [ep,add_comm]

private theorem S_phase (r : ℕ) (theta : ℝ) (hs : Real.sin (theta/2) ≠ 0) :
    (S r).eval₂ Complex.ofRealHom (ep theta) =
      ep (((r:ℝ)-1)*theta/2) *
        ((Real.sin ((r:ℝ)*theta/2)/Real.sin (theta/2):ℝ):ℂ) := by
  have hc := Real.sin_mul_sum_cos r theta 0
  have hss := Real.sin_mul_sum_sin r theta 0
  simp only [add_zero] at hc hss
  simp only [S,Polynomial.eval₂_finset_sum,Polynomial.eval₂_pow,Polynomial.eval₂_X]
  simp_rw [ep_pow]
  apply Complex.ext
  · simp only [← Complex.reCLM_apply,map_sum]
    simp only [Complex.reCLM_apply,ep,Complex.exp_ofReal_mul_I_re,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    rw [← mul_div_assoc]
    apply (eq_div_iff hs).mpr
    nlinarith [hc]
  · simp only [← Complex.imCLM_apply,map_sum]
    simp only [Complex.imCLM_apply,ep,Complex.exp_ofReal_mul_I_im,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_add]
    rw [← mul_div_assoc]
    apply (eq_div_iff hs).mpr
    nlinarith [hss]

private noncomputable def midEval (n : ℕ) (p : Polynomial ℝ) (theta : ℝ) : ℂ :=
  ep (-(n:ℝ)*theta/2)*p.eval₂ Complex.ofRealHom (ep theta)

private theorem midEval_add (n : ℕ) (p q : Polynomial ℝ) (theta : ℝ) :
    midEval n (p+q) theta = midEval n p theta+midEval n q theta := by
  simp only [midEval,Polynomial.eval₂_add,mul_add]

private theorem midEval_mul (n k : ℕ) (p q : Polynomial ℝ) (theta : ℝ) :
    midEval (n+k) (p*q) theta = midEval n p theta*midEval k q theta := by
  simp only [midEval,Polynomial.eval₂_mul]
  have he : ep (-((n+k:ℕ):ℝ)*theta/2) =
      ep (-(n:ℝ)*theta/2)*ep (-(k:ℝ)*theta/2) := by
    rw [← ep_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

private theorem midEval_C_mul (n : ℕ) (a : ℝ) (p : Polynomial ℝ) (theta : ℝ) :
    midEval n (Polynomial.C a*p) theta = (a:ℂ)*midEval n p theta := by
  simp only [midEval,Polynomial.eval₂_mul,Polynomial.eval₂_C]
  change ep (-(n:ℝ)*theta/2)*((a:ℂ)*p.eval₂ Complex.ofRealHom (ep theta)) =
    (a:ℂ)*(ep (-(n:ℝ)*theta/2)*p.eval₂ Complex.ofRealHom (ep theta))
  ring

private theorem midEval_pow (n r : ℕ) (p : Polynomial ℝ) (theta : ℝ) :
    midEval (n*r) (p^r) theta = (midEval n p theta)^r := by
  induction r with
  | zero => simp [midEval,ep]
  | succ r ih => rw [Nat.mul_succ,pow_succ,midEval_mul,ih,pow_succ]

private theorem midEval_H (r : ℕ) (theta : ℝ) :
    midEval r (H r) theta = ((2*Real.cos ((r:ℝ)*theta/2):ℝ):ℂ) := by
  unfold midEval
  rw [H_phase]
  have he : ep (-(r:ℝ)*theta/2)*ep ((r:ℝ)*theta/2) = 1 := by
    rw [← ep_add]
    rw [show -(r:ℝ)*theta/2+(r:ℝ)*theta/2=0 by ring]
    simp [ep]
  rw [← mul_assoc,he,one_mul]

private theorem midEval_S (r : ℕ) (hr : 1 ≤ r) (theta : ℝ)
    (hs : Real.sin (theta/2) ≠ 0) :
    midEval (r-1) (S r) theta =
      ((Real.sin ((r:ℝ)*theta/2)/Real.sin (theta/2):ℝ):ℂ) := by
  unfold midEval
  rw [S_phase r theta hs]
  have he : ep (-((r-1:ℕ):ℝ)*theta/2)*ep (((r:ℝ)-1)*theta/2) = 1 := by
    rw [← ep_add]
    rw [Nat.cast_sub hr]
    simp only [Nat.cast_one]
    rw [show -((r:ℝ)-1)*theta/2+((r:ℝ)-1)*theta/2=0 by ring]
    simp [ep]
  rw [← mul_assoc,he,one_mul]

noncomputable def realVal (d r : ℕ) (theta : ℝ) : ℝ :=
  if Odd d then Real.sin (((d+r:ℕ):ℝ)*theta/2)/Real.sin (theta/2)
  else 2*Real.cos (((d+r:ℕ):ℝ)*theta/2)

private theorem family_mid (d r : ℕ) (hd : 2 ≤ d) (theta : ℝ)
    (hs : Real.sin (theta/2) ≠ 0) :
    midEval (baseDegree d+r) (if Odd d then S (d+r) else H (d+r)) theta =
      ((realVal d r theta:ℝ):ℂ) := by
  by_cases ho : Odd d
  · simp only [baseDegree,ho,ite_true,realVal]
    rw [show d-1+r = d+r-1 by omega]
    exact midEval_S (d+r) (by omega) theta hs
  · simp only [baseDegree,ho,ite_false,realVal]
    exact midEval_H (d+r) theta

private theorem realVal_recurrence (d : ℕ) (theta : ℝ) :
    realVal d 2 theta = 2*Real.cos (theta/2)*realVal d 1 theta-realVal d 0 theta := by
  unfold realVal
  by_cases ho : Odd d
  · simp only [ho,ite_true,Nat.cast_add,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,add_zero]
    rw [show ((d:ℝ)+2)*theta/2 = (d:ℝ)*theta/2+2*(theta/2) by ring,
      show ((d:ℝ)+1)*theta/2 = (d:ℝ)*theta/2+theta/2 by ring]
    have hh := Real.sin_add_sin ((d:ℝ)*theta/2+2*(theta/2)) ((d:ℝ)*theta/2)
    rw [show ((d:ℝ)*theta/2+2*(theta/2)+(d:ℝ)*theta/2)/2 = (d:ℝ)*theta/2+theta/2 by ring,
      show ((d:ℝ)*theta/2+2*(theta/2)-(d:ℝ)*theta/2)/2 = theta/2 by ring] at hh
    rw [show Real.sin ((d:ℝ)*theta/2+2*(theta/2)) =
      2*Real.cos (theta/2)*Real.sin ((d:ℝ)*theta/2+theta/2)-Real.sin ((d:ℝ)*theta/2) by linarith [hh]]
    ring
  · simp only [ho,ite_false,Nat.cast_add,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,add_zero]
    rw [show ((d:ℝ)+2)*theta/2 = (d:ℝ)*theta/2+2*(theta/2) by ring,
      show ((d:ℝ)+1)*theta/2 = (d:ℝ)*theta/2+theta/2 by ring]
    have hh := Real.cos_add_cos ((d:ℝ)*theta/2+2*(theta/2)) ((d:ℝ)*theta/2)
    rw [show ((d:ℝ)*theta/2+2*(theta/2)+(d:ℝ)*theta/2)/2 = (d:ℝ)*theta/2+theta/2 by ring,
      show ((d:ℝ)*theta/2+2*(theta/2)-(d:ℝ)*theta/2)/2 = theta/2 by ring] at hh
    linarith [hh]

private theorem mid_eq_add {n : ℕ} {p q : Polynomial ℝ} {theta a b : ℝ}
    (hp : midEval n p theta = (a:ℂ)) (hq : midEval n q theta = (b:ℂ)) :
    midEval n (p+q) theta = ((a+b:ℝ):ℂ) := by
  rw [midEval_add,hp,hq,Complex.ofReal_add]

private theorem mid_eq_mul {n k : ℕ} {p q : Polynomial ℝ} {theta a b : ℝ}
    (hp : midEval n p theta = (a:ℂ)) (hq : midEval k q theta = (b:ℂ)) :
    midEval (n+k) (p*q) theta = ((a*b:ℝ):ℂ) := by
  rw [midEval_mul,hp,hq,Complex.ofReal_mul]

private theorem mid_eq_C_mul {n : ℕ} {p : Polynomial ℝ} {theta a : ℝ} (c : ℝ)
    (hp : midEval n p theta = (a:ℂ)) :
    midEval n (Polynomial.C c*p) theta = ((c*a:ℝ):ℂ) := by
  rw [midEval_C_mul,hp,Complex.ofReal_mul]

private theorem mid_eq_pow {n : ℕ} {p : Polynomial ℝ} {theta a : ℝ}
    (hp : midEval n p theta = (a:ℂ)) (r : ℕ) :
    midEval (n*r) (p^r) theta = ((a^r:ℝ):ℂ) := by
  rw [midEval_pow,hp,Complex.ofReal_pow]

private theorem Q_phase_raw (d : ℕ) (hd : 2 ≤ d) (theta : ℝ)
    (hs : Real.sin (theta/2) ≠ 0) :
    let x : ℝ := d
    let u := realVal d 0 theta
    let v := realVal d 1 theta
    let w := realVal d 2 theta
    let ell := 2*Real.cos (theta/2)
    let t := 2*Real.cos theta
    phaseValue d theta =
      ((t*(2*x^4*v^2+(3/2:ℝ)*x^2*(x^2-1)*u*w+
        4*x*(x-1)*(2*x-1)*ell*u*v+2*(x-1)*(2*x-3)*ell^2*u^2) +
        (2*Real.cos (3*theta/2))*(8*x*(2*x-1)*u*v+16*(x-1)*ell*u^2) +
        9*(2*Real.cos (2*theta))*u^2 : ℝ):ℂ) := by
  dsimp only
  let x : ℝ := d
  let u := realVal d 0 theta
  let v := realVal d 1 theta
  let w := realVal d 2 theta
  let ell := 2*Real.cos (theta/2)
  let t := 2*Real.cos theta
  have hu : midEval (baseDegree d) (U d) theta = (u:ℂ) := by
    simpa [U,u] using family_mid d 0 hd theta hs
  have hv : midEval (baseDegree d+1) (V d) theta = (v:ℂ) := by
    simpa [V,v] using family_mid d 1 hd theta hs
  have hw : midEval (baseDegree d+2) (W d) theta = (w:ℂ) := by
    simpa [W,w] using family_mid d 2 hd theta hs
  have hl : midEval 1 (1+Polynomial.X) theta = (ell:ℂ) := by
    simpa [H,ell] using midEval_H 1 theta
  have h1 : midEval (2*baseDegree d+2) (Polynomial.C (2*x^4)*V d^2) theta =
      ((2*x^4*v^2:ℝ):ℂ) := by
    simpa only [show (baseDegree d+1)*2=2*baseDegree d+2 by omega] using mid_eq_C_mul (2*x^4) (mid_eq_pow hv 2)
  have h2 : midEval (2*baseDegree d+2)
      (Polynomial.C ((3/2:ℝ)*x^2*(x^2-1))*U d*W d) theta =
      (((3/2:ℝ)*x^2*(x^2-1)*u*w:ℝ):ℂ) := by
    convert mid_eq_C_mul ((3/2:ℝ)*x^2*(x^2-1)) (mid_eq_mul hu hw) using 1 <;>
      first | ring | omega
  have h3 : midEval (2*baseDegree d+2)
      (Polynomial.C (4*x*(x-1)*(2*x-1))*(1+Polynomial.X)*U d*V d) theta =
      ((4*x*(x-1)*(2*x-1)*ell*u*v:ℝ):ℂ) := by
    convert mid_eq_C_mul (4*x*(x-1)*(2*x-1)) (mid_eq_mul (mid_eq_mul hl hu) hv) using 1 <;>
      first | ring | omega
  have h4 : midEval (2*baseDegree d+2)
      (Polynomial.C (2*(x-1)*(2*x-3))*(1+Polynomial.X)^2*U d^2) theta =
      ((2*(x-1)*(2*x-3)*ell^2*u^2:ℝ):ℂ) := by
    convert mid_eq_C_mul (2*(x-1)*(2*x-3)) (mid_eq_mul (mid_eq_pow hl 2) (mid_eq_pow hu 2)) using 1 <;>
      first | ring | omega
  have h5 : midEval (2*baseDegree d+1)
      (Polynomial.C (8*x*(2*x-1))*U d*V d) theta = ((8*x*(2*x-1)*u*v:ℝ):ℂ) := by
    convert mid_eq_C_mul (8*x*(2*x-1)) (mid_eq_mul hu hv) using 1 <;>
      first | ring | omega
  have h6 : midEval (2*baseDegree d+1)
      (Polynomial.C (16*(x-1))*(1+Polynomial.X)*U d^2) theta =
      ((16*(x-1)*ell*u^2:ℝ):ℂ) := by
    convert mid_eq_C_mul (16*(x-1)) (mid_eq_mul hl (mid_eq_pow hu 2)) using 1 <;>
      first | ring | omega
  have h7 : midEval (2*baseDegree d+4) (Polynomial.C 9*H 4*U d^2) theta =
      ((9*(2*Real.cos (2*theta))*u^2:ℝ):ℂ) := by
    convert mid_eq_C_mul 9 (mid_eq_mul (midEval_H 4 theta) (mid_eq_pow hu 2)) using 1 <;>
      first | ring | omega | norm_num
  have ht1 := mid_eq_mul (midEval_H 2 theta) (mid_eq_add (mid_eq_add (mid_eq_add h1 h2) h3) h4)
  have ht2 := mid_eq_mul (midEval_H 3 theta) (mid_eq_add h5 h6)
  rw [show 2+(2*baseDegree d+2)=2*baseDegree d+4 by omega] at ht1
  rw [show 3+(2*baseDegree d+1)=2*baseDegree d+4 by omega] at ht2
  norm_num only [Nat.cast_ofNat] at ht1 ht2
  rw [show (2:ℝ)*theta/2=theta by ring] at ht1
  have hh := mid_eq_add (mid_eq_add ht1 ht2) h7
  have hn : 2*N d = 2*baseDegree d+4 := by
    unfold N baseDegree; split_ifs <;> omega
  have he : phaseValue d theta = midEval (2*baseDegree d+4) (Q d) theta := by
    rw [← hn]
    unfold phaseValue midEval ep
    congr 2
    push_cast
    ring
  rw [he]
  simpa only [Q,x,u,v,w,ell,t] using hh

noncomputable def fValue (d t : ℝ) : ℝ :=
  (4*d^2+6*d-1)*t^2-((3*d^4-19*d^2+8*d+8)/2)*t-(32*d-14)

theorem Q_phase_reduced (d : ℕ) (hd : 2 ≤ d) (theta : ℝ)
    (hs : Real.sin (theta/2) ≠ 0) :
    let x : ℝ := d
    let u := realVal d 0 theta
    let v := realVal d 1 theta
    let ell := 2*Real.cos (theta/2)
    let t := 2*Real.cos theta
    phaseValue d theta =
      ((2*x^4*t*v^2 + ell*(((3/2:ℝ)*x^2*(x^2-1)+
        4*x*(x-1)*(2*x-1)+8*x*(2*x-1))*t-8*x*(2*x-1))*u*v+
        fValue x t*u^2 : ℝ):ℂ) := by
  have hc3 : 2*Real.cos (3*theta/2) =
      (2*Real.cos (theta/2))*(2*Real.cos theta-1) := by
    rw [show 3*theta/2 = 3*(theta/2) by ring,Real.cos_three_mul]
    rw [show theta = 2*(theta/2) by ring,Real.cos_two_mul]
    ring
  have hc4 : 2*Real.cos (2*theta) = (2*Real.cos theta)^2-2 := by
    rw [Real.cos_two_mul]; ring
  have hell : (2*Real.cos (theta/2))^2 = 2*Real.cos theta+2 := by
    nth_rw 2 [show theta = 2*(theta/2) by ring]
    rw [Real.cos_two_mul]
    ring
  have hraw := Q_phase_raw d hd theta hs
  dsimp only at hraw ⊢
  rw [realVal_recurrence,hc3,hc4] at hraw
  rw [hraw]
  congr 1
  unfold fValue
  have hh := congrArg (fun a : ℝ =>
    ((2*((d:ℝ)-1)*(2*d-3))*(2*Real.cos theta)+
      16*((d:ℝ)-1)*(2*Real.cos theta-1))*(realVal d 0 theta)^2*a) hell
  linear_combination hh


end FiolDoubleHub


namespace FiolDoubleHub
private theorem grid_half_sin_ne (d k : ℝ) (hd : 0 < d) (hk : 0 < k) (hkd : k ≤ d) :
    Real.sin ((k*Real.pi/d)/2) ≠ 0 := by
  have hangle : 0 < k*Real.pi/d := div_pos (mul_pos hk Real.pi_pos) hd
  have hbound : k*Real.pi/d ≤ Real.pi := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [Real.pi_pos]
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))

theorem odd_a_values (d j : ℕ) (hd : 2 ≤ d) (ho : Odd d)
    (hj : 1 ≤ j) (hjd : 2*j < d) :
    let a := 2*Real.pi*(j:ℝ)/(d:ℝ)
    realVal d 0 a = 0 ∧ realVal d 1 a = (-1:ℝ)^j := by
  dsimp only
  let a := 2*Real.pi*(j:ℝ)/(d:ℝ)
  have hdp : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hdn : (d:ℝ) ≠ 0 := ne_of_gt hdp
  have hjp : (0:ℝ) < 2*(j:ℝ) := by exact_mod_cast (by omega : 0 < 2*j)
  have hjle : 2*(j:ℝ) ≤ d := by exact_mod_cast (by omega : 2*j ≤ d)
  have hs : Real.sin (a/2) ≠ 0 := by
    convert grid_half_sin_ne (d:ℝ) (2*(j:ℝ)) hdp hjp hjle using 1 <;> congr 1 <;> dsimp [a] <;> ring
  have h1 : (d:ℝ)*a/2 = (j:ℝ)*Real.pi := by dsimp [a]; field_simp <;> ring
  have h2 : ((d:ℝ)+1)*a/2 = a/2+(j:ℝ)*Real.pi := by dsimp [a]; field_simp <;> ring
  change realVal d 0 a = 0 ∧ realVal d 1 a = _
  simp only [realVal,ho,ite_true,Nat.cast_add,Nat.cast_zero,Nat.cast_one,add_zero]
  rw [h1,h2,Real.sin_nat_mul_pi,zero_div,Real.sin_add_nat_mul_pi]
  constructor
  · rfl
  · field_simp

theorem odd_b_values (d j : ℕ) (hd : 2 ≤ d) (ho : Odd d)
    (hj : 1 ≤ j) (hjd : 2*j ≤ d+1) :
    let b := 2*Real.pi*(j:ℝ)/((d:ℝ)+1)
    realVal d 1 b = 0 ∧ realVal d 0 b = (-1:ℝ)^(j+1) := by
  dsimp only
  let b := 2*Real.pi*(j:ℝ)/((d:ℝ)+1)
  have hdp : (0:ℝ) < (d:ℝ)+1 := by positivity
  have hdn : (d:ℝ)+1 ≠ 0 := ne_of_gt hdp
  have hjp : (0:ℝ) < 2*(j:ℝ) := by exact_mod_cast (by omega : 0 < 2*j)
  have hjle : 2*(j:ℝ) ≤ (d:ℝ)+1 := by exact_mod_cast hjd
  have hs : Real.sin (b/2) ≠ 0 := by
    convert grid_half_sin_ne ((d:ℝ)+1) (2*(j:ℝ)) hdp hjp hjle using 1 <;> congr 1 <;> dsimp [b] <;> ring
  have h1 : ((d:ℝ)+1)*b/2 = (j:ℝ)*Real.pi := by dsimp [b]; field_simp <;> ring
  have h2 : (d:ℝ)*b/2 = (j:ℝ)*Real.pi-b/2 := by dsimp [b]; field_simp <;> ring
  change realVal d 1 b = 0 ∧ realVal d 0 b = _
  simp only [realVal,ho,ite_true,Nat.cast_add,Nat.cast_zero,Nat.cast_one,add_zero]
  rw [h1,h2,Real.sin_nat_mul_pi,zero_div,Real.sin_nat_mul_pi_sub,pow_succ]
  constructor
  · rfl
  · field_simp

private theorem even_a_values (d j : ℕ) (hd : 2 ≤ d) (ho : ¬ Odd d)
    (hj : 1 ≤ j) (hjd : 2*j ≤ d) :
    let a := (2*(j:ℝ)-1)*Real.pi/(d:ℝ)
    realVal d 0 a = 0 ∧ (realVal d 1 a)^2 = 2-2*Real.cos a := by
  dsimp only
  let a := (2*(j:ℝ)-1)*Real.pi/(d:ℝ)
  have hdp : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hdn : (d:ℝ) ≠ 0 := ne_of_gt hdp
  have h1 : (d:ℝ)*a/2 = (j:ℝ)*Real.pi-Real.pi/2 := by dsimp [a]; field_simp <;> ring
  have h2 : ((d:ℝ)+1)*a/2 = (a/2-Real.pi/2)+(j:ℝ)*Real.pi := by dsimp [a]; field_simp <;> ring
  have hcos : Real.cos a = 1-2*(Real.sin (a/2))^2 := by
    convert Real.cos_two_mul_eq_one_sub (a/2) using 1 <;> congr 1 <;> ring
  change realVal d 0 a = 0 ∧ (realVal d 1 a)^2 = _
  simp only [realVal,ho,ite_false,Nat.cast_add,Nat.cast_zero,Nat.cast_one,add_zero]
  rw [h1,h2,Real.cos_nat_mul_pi_sub,Real.cos_pi_div_two,mul_zero,mul_zero,
    Real.cos_add_nat_mul_pi,Real.cos_sub_pi_div_two]
  constructor
  · rfl
  · have he : ((-1:ℝ)^j)^2 = 1 := by
      rw [← pow_mul,Nat.mul_comm]; exact (even_two_mul j).neg_one_pow
    rw [mul_pow,mul_pow,he,hcos]
    ring

private theorem even_b_values (d j : ℕ) (hd : 2 ≤ d) (ho : ¬ Odd d)
    (hj : 1 ≤ j) (hjd : 2*j ≤ d+2) :
    let b := (2*(j:ℝ)-1)*Real.pi/((d:ℝ)+1)
    realVal d 1 b = 0 ∧ (realVal d 0 b)^2 = 2-2*Real.cos b := by
  dsimp only
  let b := (2*(j:ℝ)-1)*Real.pi/((d:ℝ)+1)
  have hdn : (d:ℝ)+1 ≠ 0 := by positivity
  have h1 : ((d:ℝ)+1)*b/2 = (j:ℝ)*Real.pi-Real.pi/2 := by dsimp [b]; field_simp <;> ring
  have h2 : (d:ℝ)*b/2 = (j:ℝ)*Real.pi-(b/2+Real.pi/2) := by dsimp [b]; field_simp <;> ring
  have hcos : Real.cos b = 1-2*(Real.sin (b/2))^2 := by
    convert Real.cos_two_mul_eq_one_sub (b/2) using 1 <;> congr 1 <;> ring
  change realVal d 1 b = 0 ∧ (realVal d 0 b)^2 = _
  simp only [realVal,ho,ite_false,Nat.cast_add,Nat.cast_zero,Nat.cast_one,add_zero]
  rw [h1,h2,Real.cos_nat_mul_pi_sub,Real.cos_pi_div_two,mul_zero,mul_zero,
    Real.cos_nat_mul_pi_sub,Real.cos_add_pi_div_two]
  constructor
  · rfl
  · have he : ((-1:ℝ)^j)^2 = 1 := by
      rw [← pow_mul,Nat.mul_comm]; exact (even_two_mul j).neg_one_pow
    rw [mul_pow,mul_pow,he,hcos]
    ring

theorem odd_a_phase (d j : ℕ) (hd : 2 ≤ d) (ho : Odd d)
    (hj : 1 ≤ j) (hjd : 2*j < d) :
    let a := 2*Real.pi*(j:ℝ)/(d:ℝ)
    phaseValue d a = ((2*(d:ℝ)^4*(2*Real.cos a):ℝ):ℂ) := by
  dsimp only
  let a := 2*Real.pi*(j:ℝ)/(d:ℝ)
  have hv := odd_a_values d j hd ho hj hjd
  change realVal d 0 a = 0 ∧ realVal d 1 a = _ at hv
  have hs : Real.sin (a/2) ≠ 0 := by
    convert grid_half_sin_ne (d:ℝ) (2*(j:ℝ)) (by exact_mod_cast (by omega : 0 < d))
      (by exact_mod_cast (by omega : 0 < 2*j)) (by exact_mod_cast (by omega : 2*j ≤ d)) using 1 <;>
      congr 1 <;> dsimp [a] <;> ring
  have hv2 : (realVal d 1 a)^2 = 1 := by
    rw [hv.2,← pow_mul,Nat.mul_comm]; exact (even_two_mul j).neg_one_pow
  have hh := Q_phase_reduced d hd a hs
  dsimp only at hh
  simpa [a,hv.1,hv2] using hh

theorem odd_b_phase (d j : ℕ) (hd : 2 ≤ d) (ho : Odd d)
    (hj : 1 ≤ j) (hjd : 2*j ≤ d+1) :
    let b := 2*Real.pi*(j:ℝ)/((d:ℝ)+1)
    phaseValue d b = ((fValue (d:ℝ) (2*Real.cos b):ℝ):ℂ) := by
  dsimp only
  let b := 2*Real.pi*(j:ℝ)/((d:ℝ)+1)
  have hv := odd_b_values d j hd ho hj hjd
  change realVal d 1 b = 0 ∧ realVal d 0 b = _ at hv
  have hs : Real.sin (b/2) ≠ 0 := by
    convert grid_half_sin_ne ((d:ℝ)+1) (2*(j:ℝ)) (by positivity)
      (by exact_mod_cast (by omega : 0 < 2*j)) (by exact_mod_cast hjd) using 1 <;>
      congr 1 <;> dsimp [b] <;> ring
  have hv2 : (realVal d 0 b)^2 = 1 := by
    rw [hv.2,← pow_mul,Nat.mul_comm]; exact (even_two_mul (j+1)).neg_one_pow
  have hh := Q_phase_reduced d hd b hs
  dsimp only at hh
  simpa [b,hv.1,hv2] using hh

theorem even_a_phase (d j : ℕ) (hd : 2 ≤ d) (ho : ¬ Odd d)
    (hj : 1 ≤ j) (hjd : 2*j ≤ d) :
    let a := (2*(j:ℝ)-1)*Real.pi/(d:ℝ)
    phaseValue d a = ((2*(d:ℝ)^4*(2*Real.cos a)*(2-2*Real.cos a):ℝ):ℂ) := by
  dsimp only
  let a := (2*(j:ℝ)-1)*Real.pi/(d:ℝ)
  have hv := even_a_values d j hd ho hj hjd
  change realVal d 0 a = 0 ∧ (realVal d 1 a)^2 = _ at hv
  have hs : Real.sin (a/2) ≠ 0 := by
    have hjp : (0:ℝ) < 2*(j:ℝ)-1 := by
      have hjj : (1:ℝ) ≤ j := by exact_mod_cast hj
      linarith
    have hjle : 2*(j:ℝ)-1 ≤ d := by
      have hjj : 2*(j:ℝ) ≤ d := by exact_mod_cast hjd
      linarith
    exact grid_half_sin_ne (d:ℝ) (2*(j:ℝ)-1)
      (by exact_mod_cast (by omega : 0 < d)) hjp hjle
  have hh := Q_phase_reduced d hd a hs
  dsimp only at hh
  simpa [a,hv.1,hv.2] using hh

theorem even_b_phase (d j : ℕ) (hd : 2 ≤ d) (ho : ¬ Odd d)
    (hj : 1 ≤ j) (hjd : 2*j ≤ d+2) :
    let b := (2*(j:ℝ)-1)*Real.pi/((d:ℝ)+1)
    phaseValue d b = (((2-2*Real.cos b)*fValue (d:ℝ) (2*Real.cos b):ℝ):ℂ) := by
  dsimp only
  let b := (2*(j:ℝ)-1)*Real.pi/((d:ℝ)+1)
  have hv := even_b_values d j hd ho hj hjd
  change realVal d 1 b = 0 ∧ (realVal d 0 b)^2 = _ at hv
  have hs : Real.sin (b/2) ≠ 0 := by
    have hjp : (0:ℝ) < 2*(j:ℝ)-1 := by
      have hjj : (1:ℝ) ≤ j := by exact_mod_cast hj
      linarith
    have hjle : 2*(j:ℝ)-1 ≤ (d:ℝ)+1 := by
      have hjj : 2*(j:ℝ) ≤ (d:ℝ)+2 := by exact_mod_cast hjd
      linarith
    exact grid_half_sin_ne ((d:ℝ)+1) (2*(j:ℝ)-1) (by positivity) hjp hjle
  have hh := Q_phase_reduced d hd b hs
  dsimp only at hh
  rw [hv.1,hv.2] at hh
  simpa [b,mul_comm] using hh

end FiolDoubleHub

end D5.S3.Zeros.LeeYang
