/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/DoublePairCubic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/DoublePairCubic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete double-pair cubic and unbounded endpoint brackets. -/
import D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionDeterminants

/-! Source: four-prime-double-pair-completion, PR9 revision
6d491f77b35dec808fc777b69939c56cdae5dc02. All eight fixed cubic brackets,
the two small positive evaluations, and all unbounded polynomial brackets
are retained. Exponent roots are distinct from spectral roots. -/
set_option autoImplicit false
noncomputable section
open Matrix
namespace D5.S3.Combinatorics.SpectralGraph.DoublePairCubic
open PairedIdealIntersectionObstructions PairedIdealIntersectionDeterminants

def Q {R : Type*} [CommRing R] (a b : R) : Matrix (Fin 3) (Fin 3) R :=
  !![(a+1)*(b+1)^2+a, 2*a*b, a*b^2;
     a, (2*a+1)*b+a+1, 0;
     a, 0, a+1]

def p {R : Type*} [CommRing R] (a b x : R) : R :=
  (Matrix.scalar (Fin 3) x-Q a b).det

/-- The full three-dimensional invariant subspace of the tensor. -/
def cubicValue {R : Type*} (h : Fin 3 → R) (q : Fin 2 × Fin 2) : R :=
  if q=(0,0) then h 0 else if q=(1,1) then h 2 else h 1

theorem cubic_action {R : Type*} [CommRing R] (a b : R) (h : Fin 3 → R) :
    tensorK a b b*ᵥcubicValue h=cubicValue (Q a b*ᵥh) := by
  ext ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [cubicValue,tensorK,E,F,kroneckerMap_apply,mulVec,dotProduct,
      Fintype.sum_prod_type,Fin.sum_univ_succ,Q] <;> ring

theorem cubic_nonzero {R : Type*} [Zero R] (h : Fin 3 → R) (hh : h≠0) :
    cubicValue h≠0 := by
  intro hz
  apply hh
  ext i
  fin_cases i
  · simpa [cubicValue] using congrFun hz (0,0)
  · simpa [cubicValue] using congrFun hz (0,1)
  · simpa [cubicValue] using congrFun hz (1,1)

def P2 {R : Type*} [CommRing R] (a b : R) : R :=
  (2*a+1)*b^3-(a-1)*(4*a^2+6*a+1)*b^2-(a-1)*(4*a^2-3)*b-(a-1)^2*(2*a-1)

def P3 {R : Type*} [CommRing R] (a b : R) : R :=
  (a+2)*(2*a+1)*b^3-a*(a-2)*(4*a+5)*b^2-
    2*(a-2)*(2*a^2-2*a-3)*b-2*(a-2)^2*(a-1)

theorem endpoint_two {R : Type*} [CommRing R] (a b : R) : p a b 2=P2 a b := by
  unfold p Q P2
  norm_num [Matrix.scalar,Matrix.sub_apply,Matrix.diagonal_apply,Matrix.det_fin_three]
  ring

theorem endpoint_three {R : Type*} [CommRing R] (a b : R) : p a b 3=P3 a b := by
  unfold p Q P3
  norm_num [Matrix.scalar,Matrix.sub_apply,Matrix.diagonal_apply,Matrix.det_fin_three]
  ring

/-- The scalar and full invariant cubic factors of the genuine four-cell tensor. -/
theorem factorization {R : Type*} [CommRing R] (a b x : R) :
    (tensorK a b b-x • 1).det=(x-(a+b+1))*p a b x := by
  rw [det_tensorK_sub_scalar]
  unfold p Q
  norm_num [Matrix.scalar,Matrix.sub_apply,Matrix.diagonal_apply,Matrix.det_fin_three]
  ring

private def f (A B C D x : ℝ) := A*x^3-B*x^2-C*x-D

private theorem comparison (A B C D x y : ℝ) :
    x^3*f A B C D y-y^3*f A B C D x =
      (y-x)*(B*x^2*y^2+C*x*y*(x+y)+D*(x^2+x*y+y^2)) := by
  unfold f; ring

private theorem root_above (A B C D x l : ℝ)
    (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hx : 0<x) (hl : 0<l)
    (hr : f A B C D x=0) (hf : f A B C D l<0) : l<x := by
  by_contra! hxl
  have hh := comparison A B C D x l
  have hn : 0 ≤ (l-x)*(B*x^2*l^2+C*x*l*(x+l)+D*(x^2+x*l+l^2)) := by
    have hdiff : 0≤l-x := by linarith
    positivity
  rw [hr,mul_zero,sub_zero] at hh
  have hneg : x^3*f A B C D l<0 := mul_neg_of_pos_of_neg (pow_pos hx _) hf
  linarith

private theorem root_below (A B C D x u : ℝ)
    (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hx : 0<x) (hu : 0<u)
    (hr : f A B C D x=0) (hf : 0<f A B C D u) : x<u := by
  by_contra! hux
  have hh := comparison A B C D u x
  have hn : 0 ≤ (x-u)*(B*u^2*x^2+C*u*x*(u+x)+D*(u^2+u*x+x^2)) := by
    have hdiff : 0≤x-u := by linarith
    positivity
  rw [hr,mul_zero,zero_sub] at hh
  have hpos : 0<x^3*f A B C D u := mul_pos (pow_pos hx _) hf
  linarith

/-- The complete endpoint-two exponent bracket. -/
theorem two_bracket (a : ℝ) (ha : 2≤a) :
    P2 a (2*a^2-2)<0 ∧ 0<P2 a (2*a^2-1) := by
  let u:=a-2
  have hu : 0≤u := by dsimp [u]; linarith
  have h1 : -P2 a (2*a^2-2)=4*u^5+36*u^4+124*u^3+201*u^2+154*u+45 := by
    dsimp [P2,u]; ring
  have h2 : P2 a (2*a^2-1)=4*u^5+48*u^4+220*u^3+483*u^2+504*u+200 := by
    dsimp [P2,u]; ring
  have hp : 0 < -P2 a (2*a^2-2) := by rw [h1]; positivity
  exact ⟨by linarith,by rw [h2]; positivity⟩

/-- No positive integer tail hits endpoint two, with no bound on its size. -/
theorem two_nonzero (a b : ℕ) (ha : 2≤a) (hb : 0<b) : P2 (a:ℝ) (b:ℝ)≠0 := by
  intro hr
  have haR : (2:ℝ)≤a := by exact_mod_cast ha
  have ha0 : (0:ℝ)<a := by positivity
  have hb0 : (0:ℝ)<b := by positivity
  have hB : 0≤((a:ℝ)-1)*(4*(a:ℝ)^2+6*(a:ℝ)+1) :=
    mul_nonneg (by linarith) (by positivity)
  have hC : 0≤((a:ℝ)-1)*(4*(a:ℝ)^2-3) :=
    mul_nonneg (by linarith) (by nlinarith)
  have hD : 0≤((a:ℝ)-1)^2*(2*(a:ℝ)-1) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  obtain ⟨hl,hu⟩ := two_bracket (a:ℝ) haR
  have hlo := root_above (2*(a:ℝ)+1) _ _ _ (b:ℝ) (2*(a:ℝ)^2-2)
    hB hC hD hb0 (by nlinarith) hr hl
  have hhi := root_below (2*(a:ℝ)+1) _ _ _ (b:ℝ) (2*(a:ℝ)^2-1)
    hB hC hD hb0 (by nlinarith) hr hu
  have hlI : 2*(a:ℤ)^2-2<b := by exact_mod_cast hlo
  have huI : (b:ℤ)<2*(a:ℤ)^2-1 := by exact_mod_cast hhi
  omega

/-- The complete unbounded endpoint-three bracket starts at a=13. -/
theorem three_large_bracket (a : ℝ) (ha : 13≤a) :
    P3 a (2*a-6)<0 ∧ 0<P3 a (2*a-5) := by
  let u:=a-13
  have hu : 0≤u := by dsimp [u]; linarith
  have h1 : -P3 a (2*a-6)=4*u^4+250*u^3+5388*u^2+48806*u+159264 := by
    dsimp [P3,u]; ring
  have h2 : P3 a (2*a-5)=4*u^4+146*u^3+1839*u^2+8839*u+10452 := by
    dsimp [P3,u]; ring
  have hp : 0 < -P3 a (2*a-6) := by rw [h1]; positivity
  exact ⟨by linarith,by rw [h2]; positivity⟩

def H (a : ℕ) : ℕ :=
  if a=5 then 5 else if a=6 then 7 else if a=7 then 9 else if a=8 then 11 else
  if a=9 then 13 else if a=10 then 15 else if a=11 then 17 else if a=12 then 18 else 2*a-6

/-- The eight complete fixed brackets, followed by the symbolic infinite tail. -/
theorem three_bracket (a : ℕ) (ha : 5≤a) :
    P3 (a:ℝ) (H a)<0 ∧ 0<P3 (a:ℝ) ((H a:ℝ)+1) := by
  by_cases ha13 : 13≤a
  · have hcast : (H a:ℝ)=2*(a:ℝ)-6 := by
      simp only [H,if_neg (by omega : a≠5),if_neg (by omega : a≠6),
        if_neg (by omega : a≠7),if_neg (by omega : a≠8),if_neg (by omega : a≠9),
        if_neg (by omega : a≠10),if_neg (by omega : a≠11),if_neg (by omega : a≠12)]
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    have he : 2*(a:ℝ)-6+1=2*(a:ℝ)-5 := by ring
    simpa only [hcast,he] using three_large_bracket (a:ℝ) (by exact_mod_cast ha13)
  have ha12 : a≤12 := by omega
  interval_cases a <;> norm_num [P3,H]

/-- The entire endpoint-three exclusion in the ordered double-pair domain. -/
theorem three_nonzero (a b : ℕ) (ha : 2≤a) (hab : a≤b) : P3 (a:ℝ) (b:ℝ)≠0 := by
  intro hr
  have haR : (2:ℝ)≤a := by exact_mod_cast ha
  have hb0 : (0:ℝ)<b := by exact_mod_cast (show 0<b by omega)
  by_cases ha2 : a=2
  · subst a
    have hp : 0<P3 (2:ℝ) (b:ℝ) := by
      dsimp [P3]
      norm_num
      positivity
    exact hp.ne' hr
  have ha3 : 3≤a := by omega
  have ha3R : (3:ℝ)≤a := by exact_mod_cast ha3
  have hB : 0≤(a:ℝ)*((a:ℝ)-2)*(4*(a:ℝ)+5) := by positivity
  have hC : 0≤2*((a:ℝ)-2)*(2*(a:ℝ)^2-2*(a:ℝ)-3) :=
    mul_nonneg (by positivity) (by nlinarith)
  have hD : 0≤2*((a:ℝ)-2)^2*((a:ℝ)-1) :=
    mul_nonneg (by positivity) (by linarith)
  by_cases ha5 : 5≤a
  · obtain ⟨hl,hu⟩ := three_bracket a ha5
    have hH : (0:ℝ)<H a := by
      have : 0<H a := by unfold H; split_ifs <;> omega
      positivity
    have hlo := root_above (((a:ℝ)+2)*(2*(a:ℝ)+1)) _ _ _ (b:ℝ) (H a) hB hC hD hb0 hH hr hl
    have hhi := root_below (((a:ℝ)+2)*(2*(a:ℝ)+1)) _ _ _ (b:ℝ) ((H a:ℝ)+1) hB hC hD hb0 (by linarith) hr hu
    have hlI : (H a:ℤ)<b := by exact_mod_cast hlo
    have huI : (b:ℤ)<(H a:ℤ)+1 := by exact_mod_cast hhi
    omega
  · have hsmall : a=3 ∨ a=4 := by omega
    have hpos : 0<P3 (a:ℝ) (a:ℝ) := by rcases hsmall with rfl | rfl <;> norm_num [P3]
    have hhi := root_below (((a:ℝ)+2)*(2*(a:ℝ)+1)) _ _ _ (b:ℝ) (a:ℝ) hB hC hD hb0 (by positivity) hr hpos
    have habR : (a:ℝ)≤b := by exact_mod_cast hab
    linarith

/-- The full positive four-endpoint identity, including b=a and a=2. -/
theorem four_positive (a b : ℝ) (ha : 2≤a) (hab : a≤b) : 0<p a b 4 := by
  let u:=a-2
  let d:=b-a
  have hu : 0≤u := by dsimp [u]; linarith
  have hd : 0≤d := by dsimp [d]; linarith
  have he : p a b 4 =
      4*d^3*u^2+24*d^3*u+35*d^3+
      8*d^2*u^3+80*d^2*u^2+246*d^2*u+233*d^2+
      4*d*u^4+68*d*u^3+367*d*u^2+759*d*u+503*d+
      12*u^4+130*u^3+489*u^2+717*u+353 := by
    dsimp [p,Q,u,d]
    norm_num [Matrix.scalar,Matrix.sub_apply,Matrix.diagonal_apply,Matrix.det_fin_three]
    ring
  rw [he]
  positivity

end D5.S3.Combinatorics.SpectralGraph.DoublePairCubic
