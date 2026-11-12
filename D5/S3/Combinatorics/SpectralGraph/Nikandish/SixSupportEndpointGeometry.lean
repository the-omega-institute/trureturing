/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointGeometry
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full real feasibility geometry of both six-cell endpoint surfaces. -/
import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportEndpointSmallGaps

/-! Sources: the selected S.ep1geometry and S.ep2geometry notes, with the
original full-source bindings in scientific03. The polynomial h is the
literal six-cell characteristic quotient. Exponent-root simplicity is
separate from spectral multiplicity, and real feasibility is separate
from integer-point existence. No endpoint surface is assumed empty. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Polynomial
namespace D5.S3.Combinatorics.SpectralGraph.SixSupportEndpointGeometry
open SixSupportClassificationAlgebra

def R1 (a b : ℝ) : ℝ :=
  -b^3+(2*a^2-a-1)*b^2-3*(a-1)*b-(a-1)^2

def R2 (a b : ℝ) : ℝ :=
  -(a+2)*b^3+2*a*(a-2)*b^2-(a+6)*(a-2)*b-2*(a-2)^2

private def L1 (a b : ℝ) : ℝ := a-2*b^2+3*b-1
private def L2 (a b : ℝ) : ℝ := a*b+2*a-2*b^2+6*b-4
private def R1d (a b : ℝ) : ℝ := -3*b^2+2*(2*a^2-a-1)*b-3*(a-1)
private def R2d (a b : ℝ) : ℝ := -3*(a+2)*b^2+4*a*(a-2)*b-(a+6)*(a-2)
private def S1 (a b : ℝ) : ℝ := ((-4*b+3)*R1 a b+L1 a b*R1d a b)/2
private def S2 (a b : ℝ) : ℝ := ((a-4*b+6)*R2 a b+L2 a b*R2d a b)/2
private def T1 (a b : ℝ) : ℝ :=
  b^2*(4*b-4*a^2+2*a-1)+(5*a^2+a-6)*b+(a-1)*(a^2-3)
private def U1 (a b : ℝ) : ℝ := a^2+b^2-1

private def B1 (a b : ℝ) : ℝ :=
  a^3-4*a^2*b^2+2*a^2*b-a^2+2*a*b^2+a*b-3*a+b^3-b^2-3*b+3
private def D1 (a b : ℝ) : ℝ := (a-1)*(b-1)*(2*a*b+3*a+3*b-3)
private def E1 (a b : ℝ) : ℝ := (a-1)*(b-1)*(a+b-1)*(a*b+a+b-1)

private def T2 (a b : ℝ) : ℝ :=
  let m:=a-8
  let d:=b-a
  m^4+49*m^3+758*m^2+4748*m+10488+
    d*(5*m^3+150*m^2+1400*m+4144)+d^2*(8*m^2+151*m+682)+d^3*(4*m+40)

private def U2 (a b : ℝ) : ℝ :=
  let m:=a-8
  let d:=b-a
  2*m^3+51*m^2+428*m+1180+d*(3*m^2+51*m+214)+d^2*(m+10)

/-- The literal endpoint-two polynomial in the third exponent, represented
in the shifted variable c-b without deleting any coefficient. -/
def twoPolynomial (a b : ℝ) : ℝ[X] :=
  (C (U2 a b)*X^3+C (T2 a b)*X^2+C (S2 a b)*X+C (L2 a b*R2 a b)).comp (X-C b)

/-- The actual endpoint-one polynomial in the third exponent. -/
def onePolynomial (a b : ℝ) : ℝ[X] :=
  C (U1 a b)*X^3+C (B1 a b)*X^2+C (D1 a b)*X+C (E1 a b)

private theorem one_eval (a b c : ℝ) : (onePolynomial a b).eval c=h a b c 1 := by
  rw [SixSupportEndpointSmallGaps.endpoint_identity]
  simp [onePolynomial,U1,B1,D1,E1,SixSupportEndpointSmallGaps.cubic]

private theorem one_deriv (a b c : ℝ) :
    (onePolynomial a b).derivative.eval c=3*U1 a b*c^2+2*B1 a b*c+D1 a b := by
  simp [onePolynomial]
  ring

private theorem strict_root {f : ℝ → ℝ} (l u : ℝ) (hlu : l<u)
    (hf : Continuous f) (hl : f l<0) (hu : 0<f u) :
    ∃ x,l<x ∧ x<u ∧ f x=0 := by
  obtain ⟨x,hx,hf0⟩:=intermediate_value_Icc hlu.le hf.continuousOn
    (show (0 : ℝ)∈Set.Icc (f l) (f u) from ⟨hl.le,hu.le⟩)
  refine ⟨x,lt_of_le_of_ne hx.1 ?_,lt_of_le_of_ne hx.2 ?_,hf0⟩
  · intro he
    have hz : f l=0:=by simpa [he] using hf0
    linarith
  · intro he
    have hz : f u=0:=by simpa [he] using hf0
    linarith

private theorem far_positive (A B D E b : ℝ) (hA : 0<A) (hb : 0≤b) :
    ∃ M,b<M ∧ 0<A*M^3+B*M^2+D*M+E := by
  let z:=|B|+|D|+|E|+1
  let M:=b+2+z/A
  have hz : 0<z:=by dsimp [z];positivity
  have hM : 2<M:=by dsimp [M];have h:=div_pos hz hA;linarith
  have hbM : b<M:=by dsimp [M];have h:=div_pos hz hA;linarith
  have hrel : A*M=A*(b+2)+z:=by dsimp [M];field_simp [hA.ne'] <;> ring
  have hlead : 0<A*M-|B|-|D|-|E|:=by
    have h:=mul_pos hA (show 0<b+2 by linarith)
    dsimp [z] at hrel
    linarith
  have hP:=mul_pos hlead (sq_pos_of_pos (show 0<M by linarith))
  have hB : 0≤B+|B|:=by have h:=neg_abs_le B;linarith
  have hD : 0≤D+|D|:=by have h:=neg_abs_le D;linarith
  have hE : 0≤E+|E|:=by have h:=neg_abs_le E;linarith
  have hM0 : 0≤M:=by linarith
  have hM1 : 0≤M-1:=by linarith
  have hM2 : 0≤M^2-1:=by nlinarith
  have hrest : 0≤(B+|B|)*M^2+(D+|D|)*M+|D| *M*(M-1)+
      (E+|E|)+|E| *(M^2-1):=by positivity
  refine ⟨M,hbM,?_⟩
  calc
    0 < (A*M-|B|-|D|-|E|)*M^2+
        ((B+|B|)*M^2+(D+|D|)*M+|D| *M*(M-1)+(E+|E|)+|E| *(M^2-1)) :=
      add_pos_of_pos_of_nonneg hP hrest
    _ = A*M^3+B*M^2+D*M+E:=by ring

private theorem exterior_root (A B D E b : ℝ) (hA : 0<A) (hE : 0<E)
    (hb : 0<b) (hneg : A*b^3+B*b^2+D*b+E<0) :
    ∃ c,b<c ∧ A*c^3+B*c^2+D*c+E=0 ∧
      3*A*c^2+2*B*c+D≠0 ∧
      ∀ t,b<t → A*t^3+B*t^2+D*t+E=0 → t=c := by
  let f : ℝ → ℝ:=fun x=>A*x^3+B*x^2+D*x+E
  obtain ⟨r,hr0,hrb,hr⟩:=strict_root 0 b hb (f:=fun x=>-f x)
    (by fun_prop) (by dsimp [f];linarith) (by dsimp [f];linarith)
  have hr' : A*r^3+B*r^2+D*r+E=0:=by dsimp [f] at hr;linarith
  obtain ⟨M,hbM,hM⟩:=far_positive A B D E b hA hb.le
  obtain ⟨c,hbc,hcM,hc⟩:=strict_root b M hbM (f:=f) (by fun_prop) hneg hM
  change A*c^3+B*c^2+D*c+E=0 at hc
  have hc0 : 0<c:=lt_trans hb hbc
  have hsimple : 3*A*c^2+2*B*c+D≠0:=by
    intro hd
    have hEeq : E=c^2*(2*A*c+B):=by linear_combination hc-c*hd
    have hcoef : 0<2*A*c+B:=by
      by_contra hn
      have hnon:=mul_nonpos_of_nonneg_of_nonpos (sq_nonneg c) (le_of_not_gt hn)
      rw [←hEeq] at hnon
      linarith
    have hpositive : 0<A*(b+2*c)+B:=by nlinarith [mul_pos hA hb]
    have heq : A*b^3+B*b^2+D*b+E=(b-c)^2*(A*(b+2*c)+B):=by
      linear_combination hc+(b-c)*hd
    have hn:=mul_nonneg (sq_nonneg (b-c)) hpositive.le
    rw [←heq] at hn
    linarith
  refine ⟨c,hbc,hc,hsimple,?_⟩
  intro t hbt ht
  by_contra htc
  exact SixSupportEndpointSmallGaps.no_three_positive A B D E r c t hA hE
    hr0 hc0 (lt_trans hb hbt) (by linarith) (by linarith) (Ne.symm htc) hr' hc ht

private theorem derivative_negative (b R Rd P : ℝ) (hb : 0<b) (hR : R≤0)
    (hP : 0<P) (he : b*(b*Rd-2*R)= -P) : Rd<0 := by
  by_contra hn
  have hd : 0≤Rd:=le_of_not_gt hn
  have hin : 0≤b*Rd-2*R:=by nlinarith [mul_nonneg hb.le hd]
  have hnon:=mul_nonneg hb.le hin
  rw [he] at hnon
  linarith

private theorem positive_shift_root (U T S C : ℝ) (hU : 0<U) (hT : 0<T)
    (hC : C<0) :
    ∃ v,0<v ∧ U*v^3+T*v^2+S*v+C=0 ∧ 0<3*U*v^2+2*T*v+S ∧
      ∀ w,0<w → U*w^3+T*w^2+S*w+C=0 → w=v := by
  obtain ⟨M,hM,hpos⟩:=far_positive U T S C 0 hU le_rfl
  obtain ⟨v,hv,hvM,hroot⟩:=strict_root 0 M hM
    (f:=fun x=>U*x^3+T*x^2+S*x+C) (by fun_prop) (by simpa using hC) hpos
  have hd : 0<3*U*v^2+2*T*v+S:=by
    have he : v*(3*U*v^2+2*T*v+S)=2*U*v^3+T*v^2-C:=by linear_combination hroot
    have hright : 0<2*U*v^3+T*v^2-C:=by
      have hn : 0≤2*U*v^3+T*v^2:=by positivity
      linarith
    by_contra hn
    have hnon:=mul_nonpos_of_nonneg_of_nonpos hv.le (le_of_not_gt hn)
    rw [he] at hnon
    linarith
  have hnotwo (x y : ℝ) (hx : 0<x) (hy : 0<y) (hxy : x<y)
      (hxr : U*x^3+T*x^2+S*x+C=0) (hyr : U*y^3+T*y^2+S*y+C=0) : False:=by
    have hcoef : 0<U*x*y*(x+y)+T*x*y-C:=by
      have hn : 0≤U*x*y*(x+y)+T*x*y:=by positivity
      linarith
    have hp:=mul_pos (sub_pos.mpr hxy) hcoef
    have hz : (y-x)*(U*x*y*(x+y)+T*x*y-C)=0:=by
      linear_combination x*hyr-y*hxr
    linarith
  refine ⟨v,hv,hroot,hd,?_⟩
  intro w hw hwr
  rcases lt_trichotomy w v with h|h|h
  · exact False.elim (hnotwo w v hw hv h hwr hroot)
  · exact h
  · exact False.elim (hnotwo v w hv hw h hroot hwr)

private theorem cross_one (a x y : ℝ) (ha : 8≤a) (hx : a≤x) (hy : a≤y) :
    0<x^2*y^2-3*(a-1)*x*y-(a-1)^2*(x+y) := by
  let m:=a-8;let u:=x-a;let v:=y-a
  have hm : 0≤m:=by dsimp [m];linarith
  have hu : 0≤u:=by dsimp [u];linarith
  have hv : 0≤v:=by dsimp [v];linarith
  have he : x^2*y^2-3*(a-1)*x*y-(a-1)^2*(x+y)=
      (8+m+u)^2*(8+m+v)^2-3*(7+m)*(8+m+u)*(8+m+v)-
        (7+m)^2*(16+2*m+u+v):=by dsimp [m,u,v];ring
  rw [he]
  ring_nf
  positivity

private theorem cross_two (a x y : ℝ) (ha : 8≤a) (hx : a≤x) (hy : a≤y) :
    0<(a+2)*x^2*y^2-(a+6)*(a-2)*x*y-2*(a-2)^2*(x+y) := by
  let m:=a-8;let u:=x-a;let v:=y-a
  have hm : 0≤m:=by dsimp [m];linarith
  have hu : 0≤u:=by dsimp [u];linarith
  have hv : 0≤v:=by dsimp [v];linarith
  have he : (a+2)*x^2*y^2-(a+6)*(a-2)*x*y-2*(a-2)^2*(x+y)=
      (10+m)*(8+m+u)^2*(8+m+v)^2-(14+m)*(6+m)*(8+m+u)*(8+m+v)-
        2*(6+m)^2*(16+2*m+u+v):=by dsimp [m,u,v];ring
  rw [he]
  ring_nf
  positivity

private theorem anti_one (a : ℝ) (ha : 8≤a) :
    StrictAntiOn (fun b=>R1 a b/b^2) (Set.Ici a) := by
  intro x hx y hy hxy
  have hx0 : 0<x:=by change a≤x at hx;linarith
  have hy0 : 0<y:=by change a≤y at hy;linarith
  apply (div_lt_div_iff₀ (sq_pos_of_pos hy0) (sq_pos_of_pos hx0)).mpr
  have hpos:=mul_pos (sub_pos.mpr hxy) (cross_one a x y ha hx hy)
  have he : R1 a x*y^2-R1 a y*x^2=
      (y-x)*(x^2*y^2-3*(a-1)*x*y-(a-1)^2*(x+y)):=by dsimp [R1];ring
  rw [←he] at hpos
  linarith

private theorem anti_two (a : ℝ) (ha : 8≤a) :
    StrictAntiOn (fun b=>R2 a b/b^2) (Set.Ici a) := by
  intro x hx y hy hxy
  have hx0 : 0<x:=by change a≤x at hx;linarith
  have hy0 : 0<y:=by change a≤y at hy;linarith
  apply (div_lt_div_iff₀ (sq_pos_of_pos hy0) (sq_pos_of_pos hx0)).mpr
  have hpos:=mul_pos (sub_pos.mpr hxy) (cross_two a x y ha hx hy)
  have he : R2 a x*y^2-R2 a y*x^2=
      (y-x)*((a+2)*x^2*y^2-(a+6)*(a-2)*x*y-2*(a-2)^2*(x+y)):=by dsimp [R2];ring
  rw [←he] at hpos
  linarith

private theorem threshold {R : ℝ → ℝ} (a l u : ℝ) (ha : 0<a) (hal : a≤l)
    (hlu : l<u) (hc : Continuous R)
    (hanti : StrictAntiOn (fun b=>R b/b^2) (Set.Ici a))
    (hl : 0<R l) (hu : R u<0) :
    ∃ beta,l<beta ∧ beta<u ∧ R beta=0 ∧
      (∀ b,a≤b → (0<R b ↔ b<beta)) ∧
      (∀ b,a≤b → (R b=0 ↔ b=beta)) := by
  obtain ⟨beta,hlb,hbu,hR⟩:=strict_root l u hlu (f:=fun b=>-R b)
    (by fun_prop) (by linarith) (by linarith)
  have hR0 : R beta=0:=by linarith
  have hab : a≤beta:=le_trans hal hlb.le
  have hbeta0 : 0<beta:=lt_of_lt_of_le ha hab
  refine ⟨beta,hlb,hbu,hR0,?_,?_⟩
  · intro b hb
    have hb0 : 0<b:=lt_of_lt_of_le ha hb
    constructor
    · intro hp
      have hpdiv:=div_pos hp (sq_pos_of_pos hb0)
      by_contra hn
      have hle : beta≤b:=le_of_not_gt hn
      rcases lt_or_eq_of_le hle with hh|hh
      · have hneg:=hanti hab hb hh
        simp only [hR0,zero_div] at hneg
        linarith
      · subst b
        linarith
    · intro hlt
      have hp:=hanti hb hab hlt
      simp only [hR0,zero_div] at hp
      have h:= (lt_div_iff₀ (sq_pos_of_pos hb0)).mp hp
      simpa using h
  · intro b hb
    constructor
    · intro hz
      exact hanti.injOn hb hab (by simp [hz,hR0])
    · rintro rfl
      exact hR0

/-- The unique full endpoint-one middle threshold, with the original strict
unit-width bracket and exact signs throughout the unbounded real domain. -/
theorem threshold_one (a : ℝ) (ha : 8≤a) :
    ∃ gamma,2*a^2-a-2<gamma ∧ gamma<2*a^2-a-1 ∧ R1 a gamma=0 ∧
      (∀ b,a≤b → (0<R1 a b ↔ b<gamma)) ∧
      (∀ b,a≤b → (R1 a b=0 ↔ b=gamma)) := by
  have ha0 : 0<a:=by linarith
  have hal : a≤2*a^2-a-2:=by nlinarith
  have hl : 0<R1 a (2*a^2-a-2):=by
    let m:=a-8
    have hm : 0≤m:=by dsimp [m];linarith
    have he : R1 a (2*a^2-a-2)=4*m^4+118*m^3+1297*m^2+6297*m+11397:=by dsimp [R1,m];ring
    rw [he];positivity
  have hu : R1 a (2*a^2-a-1)<0:=by
    have he : R1 a (2*a^2-a-1)= -2*(a-1)^2*(3*a+2):=by dsimp [R1];ring
    rw [he]
    have h:=mul_pos (sq_pos_of_pos (show 0<a-1 by linarith)) (show 0<3*a+2 by linarith)
    nlinarith
  exact threshold a _ _ ha0 hal (by linarith) (by unfold R1;fun_prop) (anti_one a ha) hl hu

/-- The unique full endpoint-two middle threshold, with the exact original
domain and signs. Its root is a middle-exponent threshold, not a spectrum. -/
theorem threshold_two (a : ℝ) (ha : 8≤a) :
    ∃ beta,a<beta ∧ beta<2*a-2 ∧ R2 a beta=0 ∧
      (∀ b,a≤b → (0<R2 a b ↔ b<beta)) ∧
      (∀ b,a≤b → (R2 a b=0 ↔ b=beta)) := by
  have ha0 : 0<a:=by linarith
  have hl : 0<R2 a a:=by
    let m:=a-8
    have hm : 0≤m:=by dsimp [m];linarith
    have he : R2 a a=(7+m)*(10+m)*(m^2+8*m+4):=by dsimp [R2,m];ring
    rw [he];positivity
  have hu : R2 a (2*a-2)<0:=by
    let m:=a-8
    have hm : 0≤m:=by dsimp [m];linarith
    have he : R2 a (2*a-2)= -2*(13*m^3+284*m^2+2056*m+4936):=by dsimp [R2,m];ring
    rw [he]
    have h : 0<13*m^3+284*m^2+2056*m+4936:=by positivity
    linarith
  exact threshold a a _ ha0 le_rfl (by linarith) (by unfold R2;fun_prop) (anti_two a ha) hl hu

private theorem l1_negative (a b : ℝ) (ha : 8≤a) (hab : a≤b) : L1 a b<0 := by
  let m:=a-8;let d:=b-a
  have hm : 0≤m:=by dsimp [m];linarith
  have hd : 0≤d:=by dsimp [d];linarith
  have he : -L1 a b=2*m^2+4*m*d+28*m+2*d^2+29*d+97:=by dsimp [L1,m,d];ring
  have hpos : 0<2*m^2+4*m*d+28*m+2*d^2+29*d+97:=by positivity
  linarith

private theorem one_shift (a b v : ℝ) :
    h a b (b+v) 1=L1 a b*R1 a b+S1 a b*v+T1 a b*v^2+U1 a b*v^3 := by
  simp [h,quintic,L1,R1,S1,R1d,T1,U1]
  ring

private theorem one_nonpositive (a b c : ℝ) (ha : 8≤a) (hab : a≤b)
    (hbc : b<c) (hR : R1 a b≤0) : 0<h a b c 1 := by
  have hb0 : 0<b:=by linarith
  have hL:=l1_negative a b ha hab
  have hRd : R1d a b<0:=derivative_negative b (R1 a b) (R1d a b)
    (b^4-3*(a-1)*b^2-2*(a-1)^2*b) hb0 hR
    (by convert cross_one a b b ha hab hab using 1 <;>ring)
    (by dsimp [R1,R1d];ring)
  have hS : 0<S1 a b:=by
    have hnon:=mul_nonneg_of_nonpos_of_nonpos (show -4*b+3≤0 by linarith) hR
    have hpos:=mul_pos_of_neg_of_neg hL hRd
    dsimp [S1]
    linarith
  have hbLarge : a^2<b:=by
    obtain ⟨gamma,hl,hu,hz,hpos,hzero⟩:=threshold_one a ha
    by_contra hn
    have hbg : b<gamma:=by nlinarith [le_of_not_gt hn]
    have hp:=(hpos b hab).mpr hbg
    linarith
  have hT : 0<T1 a b:=by
    have ha1 : 0<a-1:=by linarith
    have hfirst : 0<4*b-4*a^2+2*a-1:=by linarith
    have hsecond : 0<5*a^2+a-6:=by nlinarith
    have hthird : 0<a^2-3:=by nlinarith
    unfold T1
    positivity
  have hU : 0<U1 a b:=by dsimp [U1];nlinarith
  have hC:=mul_nonneg_of_nonpos_of_nonpos hL.le hR
  have hv : 0<c-b:=by linarith
  have hpos : 0<L1 a b*R1 a b+S1 a b*(c-b)+T1 a b*(c-b)^2+U1 a b*(c-b)^3:=by positivity
  have he:=one_shift a b (c-b)
  rw [show b+(c-b)=c by ring] at he
  rw [he]
  exact hpos

/-- Complete real endpoint-one feasibility, uniqueness and simplicity in
the third exponent. The polynomial is the actual quotient evaluated at one;
no integer-point or spectral-multiplicity conclusion is asserted. -/
theorem geometry_one (a b : ℝ) (ha : 8≤a) (hab : a≤b) :
    ((∃ c,b<c ∧ h a b c 1=0) ↔ 0<R1 a b) ∧
    (∀ c,b<c → h a b c 1=0 →
      (onePolynomial a b).derivative.eval c≠0 ∧
        ∀ d,b<d → h a b d 1=0 → d=c) := by
  have hA : 0<U1 a b:=by dsimp [U1];nlinarith
  have hE : 0<E1 a b:=by
    have ha1 : 0<a-1:=by linarith
    have hb1 : 0<b-1:=by linarith
    have hs : 0<a+b-1:=by linarith
    have ht : 0<a*b+a+b-1:=by nlinarith [mul_pos (show 0<a by linarith) (show 0<b by linarith)]
    unfold E1
    positivity
  have hb0 : 0<b:=by linarith
  have hL:=l1_negative a b ha hab
  have hbuild (hp : 0<R1 a b) :
      ∃ c,b<c ∧ h a b c 1=0 ∧ (onePolynomial a b).derivative.eval c≠0 ∧
        ∀ d,b<d → h a b d 1=0 → d=c:=by
    have hneg : U1 a b*b^3+B1 a b*b^2+D1 a b*b+E1 a b<0:=by
      have hn:=mul_neg_of_neg_of_pos hL hp
      have he : U1 a b*b^3+B1 a b*b^2+D1 a b*b+E1 a b=L1 a b*R1 a b:=by
        dsimp [U1,B1,D1,E1,L1,R1];ring
      rwa [he]
    obtain ⟨c,hbc,hc,hs,hu⟩:=exterior_root (U1 a b) (B1 a b) (D1 a b) (E1 a b) b hA hE hb0 hneg
    have hce : h a b c 1=0:=by rw [←one_eval];simpa [onePolynomial] using hc
    refine ⟨c,hbc,hce,?_,?_⟩
    · rwa [one_deriv]
    · intro d hbd hd
      apply hu d hbd
      rw [←one_eval] at hd
      simpa [onePolynomial] using hd
  have hnecessary (c : ℝ) (hbc : b<c) (hc : h a b c 1=0) : 0<R1 a b:=by
    by_contra hn
    have hp:=one_nonpositive a b c ha hab hbc (le_of_not_gt hn)
    linarith
  refine ⟨⟨?_,?_⟩,?_⟩
  · rintro ⟨c,hbc,hc⟩
    exact hnecessary c hbc hc
  · intro hp
    obtain ⟨c,hbc,hc,_,_⟩:=hbuild hp
    exact ⟨c,hbc,hc⟩
  · intro c hbc hc
    obtain ⟨r,hbr,hr,hs,hu⟩:=hbuild (hnecessary c hbc hc)
    have hcr:=hu c hbc hc
    subst c
    exact ⟨hs,hu⟩

private theorem l2_negative (a b : ℝ) (ha : 8≤a) (hab : a≤b) : L2 a b<0 := by
  let m:=a-8;let d:=b-a
  have hm : 0≤m:=by dsimp [m];linarith
  have hd : 0≤d:=by dsimp [d];linarith
  have he : -L2 a b=m^2+3*m*d+8*m+2*d^2+18*d+4:=by dsimp [L2,m,d];ring
  have hp : 0<m^2+3*m*d+8*m+2*d^2+18*d+4:=by positivity
  linarith

private theorem two_shift (a b v : ℝ) :
    h a b (b+v) 2=L2 a b*R2 a b+S2 a b*v+T2 a b*v^2+U2 a b*v^3 := by
  simp [h,quintic,L2,R2,S2,R2d,T2,U2]
  ring

private theorem two_eval (a b c : ℝ) : (twoPolynomial a b).eval c=h a b c 2 := by
  simp only [twoPolynomial,eval_comp,eval_add,eval_mul,eval_C,eval_pow,eval_X,eval_sub]
  have he:=two_shift a b (c-b)
  rw [show b+(c-b)=c by ring] at he
  linear_combination -he

private theorem two_deriv (a b c : ℝ) :
    (twoPolynomial a b).derivative.eval c=3*U2 a b*(c-b)^2+2*T2 a b*(c-b)+S2 a b := by
  rw [twoPolynomial,Polynomial.derivative_comp]
  simp only [Polynomial.derivative_add,Polynomial.derivative_mul,Polynomial.derivative_C,
    Polynomial.derivative_X,Polynomial.derivative_pow,Polynomial.derivative_sub,
    eval_comp,eval_mul,eval_add,eval_pow,eval_X,eval_C,eval_sub]
  norm_num
  ring

private theorem two_positive_coefficients (a b : ℝ) (ha : 8≤a) (hab : a≤b) :
    0<T2 a b ∧ 0<U2 a b := by
  have hm : 0≤a-8:=by linarith
  have hd : 0≤b-a:=by linarith
  constructor
  · unfold T2
    positivity
  · unfold U2
    positivity

private theorem two_nonpositive (a b c : ℝ) (ha : 8≤a) (hab : a≤b)
    (hbc : b<c) (hR : R2 a b≤0) : 0<h a b c 2 := by
  have hb0 : 0<b:=by linarith
  have hL:=l2_negative a b ha hab
  have hRd : R2d a b<0:=derivative_negative b (R2 a b) (R2d a b)
    ((a+2)*b^4-(a+6)*(a-2)*b^2-4*(a-2)^2*b) hb0 hR
    (by convert cross_two a b b ha hab hab using 1 <;>ring)
    (by dsimp [R2,R2d];ring)
  have hS : 0<S2 a b:=by
    have hnon:=mul_nonneg_of_nonpos_of_nonpos (show a-4*b+6≤0 by linarith) hR
    have hpos:=mul_pos_of_neg_of_neg hL hRd
    dsimp [S2]
    linarith
  obtain ⟨hT,hU⟩:=two_positive_coefficients a b ha hab
  have hC:=mul_nonneg_of_nonpos_of_nonpos hL.le hR
  have hv : 0<c-b:=by linarith
  have hp : 0<L2 a b*R2 a b+S2 a b*(c-b)+T2 a b*(c-b)^2+U2 a b*(c-b)^3:=by positivity
  have he:=two_shift a b (c-b)
  rw [show b+(c-b)=c by ring] at he
  rw [he]
  exact hp

/-- Complete real endpoint-two feasibility, uniqueness and simple exponent
root for every a at least eight and every b at least a. -/
theorem geometry_two (a b : ℝ) (ha : 8≤a) (hab : a≤b) :
    ((∃ c,b<c ∧ h a b c 2=0) ↔ 0<R2 a b) ∧
    (∀ c,b<c → h a b c 2=0 →
      (twoPolynomial a b).derivative.eval c≠0 ∧
        ∀ d,b<d → h a b d 2=0 → d=c) := by
  have hL:=l2_negative a b ha hab
  obtain ⟨hT,hU⟩:=two_positive_coefficients a b ha hab
  have hbuild (hp : 0<R2 a b) :
      ∃ c,b<c ∧ h a b c 2=0 ∧ (twoPolynomial a b).derivative.eval c≠0 ∧
        ∀ d,b<d → h a b d 2=0 → d=c:=by
    have hC:=mul_neg_of_neg_of_pos hL hp
    obtain ⟨v,hv,hr,hd,hu⟩:=positive_shift_root (U2 a b) (T2 a b) (S2 a b)
      (L2 a b*R2 a b) hU hT hC
    refine ⟨b+v,by linarith,?_,?_,?_⟩
    · rw [two_shift]
      linear_combination hr
    · rw [two_deriv,show b+v-b=v by ring]
      exact hd.ne'
    · intro d hbd hd0
      have hw : U2 a b*(d-b)^3+T2 a b*(d-b)^2+S2 a b*(d-b)+L2 a b*R2 a b=0:=by
        have he:=two_shift a b (d-b)
        rw [show b+(d-b)=d by ring,hd0] at he
        linear_combination -he
      have huniq:=hu (d-b) (by linarith) hw
      linarith
  have hnecessary (c : ℝ) (hbc : b<c) (hc : h a b c 2=0) : 0<R2 a b:=by
    by_contra hn
    have hp:=two_nonpositive a b c ha hab hbc (le_of_not_gt hn)
    linarith
  refine ⟨⟨?_,?_⟩,?_⟩
  · rintro ⟨c,hbc,hc⟩
    exact hnecessary c hbc hc
  · intro hp
    obtain ⟨c,hbc,hc,_,_⟩:=hbuild hp
    exact ⟨c,hbc,hc⟩
  · intro c hbc hc
    obtain ⟨r,hbr,hr,hs,hu⟩:=hbuild (hnecessary c hbc hc)
    have hcr:=hu c hbc hc
    subst c
    exact ⟨hs,hu⟩

private def sumAux (a b : ℝ) : ℝ :=
  -b^2+(a^2+a-2)*b+4*a^4-a^3-5*a^2-a+3

private theorem sumAux_positive (a b : ℝ) (ha : 8≤a) (hab : a≤b)
    (hb : b<2*a^2-a-1) : 0<sumAux a b := by
  let M:=2*a^2-a-1
  let m:=a-8
  have hm : 0≤m:=by dsimp [m];linarith
  have hwidth : 0<M-a:=by dsimp [M];nlinarith
  have hleft : 0<sumAux a a:=by
    have he : sumAux a a=4*m^4+128*m^3+1531*m^2+8109*m+16043:=by dsimp [sumAux,m];ring
    rw [he]
    positivity
  have hright : 0<sumAux a M:=by
    have he : sumAux a M=2*m^4+68*m^3+856*m^2+4734*m+9716:=by dsimp [sumAux,M,m];ring
    rw [he]
    positivity
  have hbm : 0<M-b:=by dsimp [M];linarith
  have hba : 0≤b-a:=by linarith
  have hpositive : 0<(M-b)*sumAux a a+(b-a)*sumAux a M+(M-a)*(b-a)*(M-b):=by positivity
  have he : (M-a)*sumAux a b=
      (M-b)*sumAux a a+(b-a)*sumAux a M+(M-a)*(b-a)*(M-b):=by dsimp [sumAux];ring
  rw [←he] at hpositive
  by_contra hn
  have hnon:=mul_nonpos_of_nonneg_of_nonpos hwidth.le (le_of_not_gt hn)
  linarith

/-- The full original real sum cutoff, including the diagonal c=b.
This is a positivity theorem on the exact six-cell characteristic quotient,
with no finite exponent base or parity assumption. -/
theorem sum_cutoff (a b c : ℝ) (ha : 8≤a) (hab : a≤b) (hbc : b≤c)
    (hsum : 4*a^2-2*a≤b+c) : 0<h a b c 1 := by
  have hb0 : 0<b:=by linarith
  have hc0 : 0<c:=by linarith
  have hA : 0<U1 a b:=by dsimp [U1];nlinarith
  obtain ⟨gamma,hgl,hgu,hg0,hgpos,hgzero⟩:=threshold_one a ha
  by_cases hp : 0<R1 a b
  · have hbM : b<2*a^2-a-1:=lt_trans ((hgpos b hab).mp hp) hgu
    have haux:=sumAux_positive a b ha hab hbM
    have hid : U1 a b*(4*a^2-2*a-b)+B1 a b=sumAux a b:=by dsimp [U1,B1,sumAux];ring
    have hleading : 0<U1 a b*c+B1 a b:=by
      have hmul:=mul_nonneg hA.le (show 0≤c-(4*a^2-2*a-b) by linarith)
      nlinarith
    have ha1 : 0<a-1:=by linarith
    have hb1 : 0<b-1:=by linarith
    have hsum1 : 0<a+b-1:=by linarith
    have hprod : 0<a*b+a+b-1:=by nlinarith [mul_pos (show 0<a by linarith) hb0]
    have hD : 0<D1 a b:=by
      have hfactor : 0<2*a*b+3*a+3*b-3:=by nlinarith [mul_pos (show 0<a by linarith) hb0]
      unfold D1
      positivity
    have hE : 0<E1 a b:=by unfold E1;positivity
    have hpos : 0<c^2*(U1 a b*c+B1 a b)+D1 a b*c+E1 a b:=by positivity
    have he : (onePolynomial a b).eval c=c^2*(U1 a b*c+B1 a b)+D1 a b*c+E1 a b:=by
      simp [onePolynomial]
      ring
    rw [←one_eval,he]
    exact hpos
  · have hR : R1 a b≤0:=le_of_not_gt hp
    rcases lt_or_eq_of_le hbc with hlt|heq
    · exact one_nonpositive a b c ha hab hlt hR
    · subst c
      have hgb : gamma<b:=by nlinarith
      have hnorm:=anti_one a ha (show a≤gamma by nlinarith) hab hgb
      simp only [hg0,zero_div] at hnorm
      have hneg : R1 a b<0:=by
        have h:=(div_lt_iff₀ (sq_pos_of_pos hb0)).mp hnorm
        simpa using h
      have hL:=l1_negative a b ha hab
      have hpos:=mul_pos_of_neg_of_neg hL hneg
      have he : h a b b 1=L1 a b*R1 a b:=by simpa using one_shift a b 0
      rw [he]
      exact hpos

end D5.S3.Combinatorics.SpectralGraph.SixSupportEndpointGeometry
