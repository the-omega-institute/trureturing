/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualOuter/PalindromicArithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-corrected-window-arithmetic)
   mirror-E: none(waiver:private-consumed-corrected-window-arithmetic)
   anchors: [mathlib/module/Mathlib.Tactic.Ring.RingNF]
   utility: none
   digest: Corrected palindromic W identities and the paid X window. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter.Source

/-! Corrected palindromic W identities and the paid X window. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter
open private A B L H K SU SV SW
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter.Source

set_option maxHeartbeats 2400000 in
private theorem palin_windows (x q r1 t r2 : ℤ)
    (hx : 4≤x) (hq : 4≤q) (hr1 : 0≤r1) (ht : 1≤t)
    (hr : r1≤r2 ∧ t≤r2 ∧ r2≤t+r1 ∧ r2<q)
    (hE : 0≤L x (q*x)-B x (q*x)+K x (q*x) (q*x)-(q-r1)*L x (q*x) ∧
      L x (q*x)-B x (q*x)+K x (q*x) (q*x)-(q-r1)*L x (q*x)<L x (q*x))
    (hF : 0≤L x (q*x)-B x (q*x)+A x (q*x) (q*x)-(q-t)*L x (q*x) ∧
      L x (q*x)-B x (q*x)+A x (q*x) (q*x)-(q-t)*L x (q*x)<L x (q*x))
    (hqd : q=4 ∨ q=8 ∨ 16≤q) (hxd : x=4 ∨ 8≤x)
    (hex : x=4 → q=8 → r1=1 ∧ t=2 ∧ r2=3) :
    let y:=q*x
    let D:=L x y-B x y
    let Dp:=SV x y-SU x y
    let s1:=q-r1
    let s2:=q-r2
    let E:=D+K x y y-s1*L x y
    let ep0:=Dp+SW x y y-s1*SV x y
    let Ep:=if ep0<0 then ep0+A x y y else ep0
    let F:=D+A x y y-s2*L x y+(if x=4 ∧ q=8 then A x y y-K x y y else 0)
    let Fp:=Dp+2*A x y y-s2*SV x y+(if x=4 ∧ q=8 then 2*A x y y-SW x y y else 0)
    (0≤2*D ∧ 2*D≤L x y-1) ∧
    (0≤2*Dp ∧ 2*Dp≤SV x y-1) ∧
    (0≤2*E ∧ 2*E≤K x y y-1) ∧
    (0≤2*Ep ∧ 2*Ep≤SW x y y-1) ∧
    (0≤2*F ∧ 2*F≤A x y y-1) ∧
    (0≤2*Fp ∧ 2*Fp≤A x y y-1) := by
  let y:=q*x
  let D:=L x y-B x y
  let Dp:=SV x y-SU x y
  let s1:=q-r1
  let s2:=q-r2
  let E:=D+K x y y-s1*L x y
  let ep0:=Dp+SW x y y-s1*SV x y
  let F0:=D+A x y y-s2*L x y
  let Fp0:=Dp+2*A x y y-s2*SV x y
  have hy : 4*x≤y := by dsimp [y]; nlinarith only [mul_nonneg (show 0≤q-4 by omega) (show 0≤x by omega)]
  have hL : 1≤L x y := by
    have hx0 : 0≤x := by omega
    have hy0 : 0≤y := by omega
    have hp : 0≤L x y-1 := by dsimp [L]; ring_nf; positivity
    omega
  have hs : 1≤s2 ∧ s2≤s1 ∧ s1≤q := by dsimp [s1,s2]; omega
  have ee : 0≤E ∧ E≤L x y-1 := by
    have he : 0≤E ∧ E<L x y := by simpa [E,D,s1,y] using hE
    exact ⟨he.1,by omega⟩
  have fe : 0≤D+A x y y-(q-t)*L x y ∧ D+A x y y-(q-t)*L x y≤L x y-1 := by
    have hf : 0≤D+A x y y-(q-t)*L x y ∧ D+A x y y-(q-t)*L x y<L x y := by
      simpa [D,y] using hF
    exact ⟨hf.1,by omega⟩
  have hf0 : 0≤F0 := by
    have hm:=mul_nonneg (show 0≤r2-t by omega) (show 0≤L x y by omega)
    dsimp [F0,s2]
    nlinarith only [fe.1,hm]
  have fpid : Fp0=2*F0+(s2-1)*y+s2 := by dsimp [Fp0,F0,Dp,D,SV,SU,L,B]; ring
  have hfp : 0≤Fp0 ∧ F0≤Fp0 := by
    have hm:=mul_nonneg (show 0≤s2-1 by omega) (show 0≤y by omega)
    omega
  -- These are the corrected identities; in particular the -y is retained.
  have epid : ep0=2*E-H y y+s1*(y+1)-y := by
    dsimp [ep0,E,Dp,D,SW,SV,SU,K,H,L,B]; ring
  have epslack : SW x y y-1-2*ep0=2*K x y y+H y y-1-4*E-2*s1*(y+1)+2*y := by
    rw [epid]; dsimp [SW]; ring
  have epshift : ep0+A x y y=2*E+(A x y y-H y y-y)+s1*(y+1) := by rw [epid]; ring
  let u:=x-4
  let w:=q-4
  have hu : 0≤u := by dsimp [u]; omega
  have hw : 0≤w := by dsimp [w]; omega
  have ex : x=u+4 := by dsimp [u]; ring
  have eq : q=w+4 := by dsimp [w]; ring
  have d0 : 0≤D := by dsimp [D,L,B,y]; rw [ex,eq]; ring_nf; positivity
  have d1 : 0≤L x y-1-2*D := by dsimp [D,L,B,y]; rw [ex,eq]; ring_nf; positivity
  have dp0 : 0≤Dp := by dsimp [Dp,SV,SU,L,B,y]; rw [ex,eq]; ring_nf; positivity
  have dp1 : 0≤SV x y-1-2*Dp := by dsimp [Dp,SV,SU,L,B,y]; rw [ex,eq]; ring_nf; positivity
  have kl : 0<K x y y-2*L x y := by dsimp [K,H,L,y]; rw [ex,eq]; ring_nf; positivity
  have wb : 0<2*K x y y+H y y-1-4*L x y-2*q*(y+1)+2*y := by
    dsimp [K,H,L,y]; rw [ex,eq]; ring_nf; positivity
  have amin_identity : A x y y-H y y-y=x+(x-2)*y+(x-1)*y^2 := by
    dsimp [A,H]
    ring
  have amin : 0<A x y y-H y y-y := by
    rw [amin_identity]
    have hxp : 0<x := by omega
    have hx2 : 0≤x-2 := by omega
    have hx1 : 0≤x-1 := by omega
    have hy0 : 0≤y := by omega
    positivity
  have ash : 0<SW x y y-1-2*A x y y := by dsimp [SW,K,H,A,y]; rw [ex,eq]; ring_nf; positivity
  have epwin :
      let Ep:=if ep0<0 then ep0+A x y y else ep0
      0≤2*Ep ∧ 2*Ep≤SW x y y-1 := by
    have hm:=mul_le_mul_of_nonneg_right hs.2.2 (show 0≤y+1 by omega)
    have hn:=mul_nonneg (show 0≤s1 by omega) (show 0≤y+1 by omega)
    dsimp only
    split_ifs with hn0
    · constructor <;> nlinarith only [epshift,amin,ee.1,hn,ash,hn0]
    · constructor <;> nlinarith only [epslack,ee.2,hm,wb,hn0]
  have xwin :
      let F:=F0+(if x=4 ∧ q=8 then A x y y-K x y y else 0)
      let Fp:=Fp0+(if x=4 ∧ q=8 then 2*A x y y-SW x y y else 0)
      (0≤2*F ∧ 2*F≤A x y y-1) ∧ (0≤2*Fp ∧ 2*Fp≤A x y y-1) := by
    rcases hqd with h4|h8|h16
    · clear eq hw w
      subst q
      have er1 : r1=0 := by
        have e00 : 0<D+K x y y-4*L x y := by dsimp [D,K,H,L,B,y]; rw [ex]; ring_nf; positivity
        by_contra hn
        have hm:=mul_le_mul_of_nonneg_right (show 1≤r1 by omega) (show 0≤L x y by omega)
        dsimp [E,s1] at ee
        nlinarith only [ee.2,e00,hm]
      have et : t=1 := by
        have ff : 0<D+A x y y-3*L x y := by dsimp [D,A,L,B,y]; rw [ex]; ring_nf; positivity
        by_contra hn
        have hm:=mul_le_mul_of_nonneg_right (show 2≤t by omega) (show 0≤L x y by omega)
        nlinarith only [fe.2,ff,hm]
      have er2 : r2=1 := by omega
      subst r1; subst t; subst r2
      have c0 : 0≤F0 := hf0
      have c1 : 0≤A x y y-1-2*F0 := by dsimp [F0,s2,D,A,L,B,y]; rw [ex]; ring_nf; positivity
      have c2 : 0≤Fp0 := hfp.1
      have c3 : 0≤A x y y-1-2*Fp0 := by dsimp [Fp0,s2,Dp,A,SV,SU,L,B,y]; rw [ex]; ring_nf; positivity
      simp only [show ¬(x=4 ∧ (4:ℤ)=8) by omega,ite_false,add_zero]
      exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩
    · clear eq hw w
      subst q
      clear ex hu u
      rcases hxd with hx4|hx8
      · obtain ⟨er1,et,er2⟩:=hex hx4 rfl
        subst x; subst r1; subst t; subst r2
        norm_num [F0,Fp0,s2,D,Dp,A,B,L,H,K,SU,SV,SW,y]
      · let v:=x-8
        have hv : 0≤v := by dsimp [v]; omega
        have ex8 : x=v+8 := by dsimp [v]; ring
        have er1 : r1=0 := by
          have e00 : 0<D+K x y y-8*L x y := by dsimp [D,K,H,L,B,y]; rw [ex8]; ring_nf; positivity
          by_contra hn
          have hm:=mul_le_mul_of_nonneg_right (show 1≤r1 by omega) (show 0≤L x y by omega)
          dsimp [E,s1] at ee
          nlinarith only [ee.2,e00,hm]
        have et : t=1 := by
          have ff : 0<D+A x y y-7*L x y := by dsimp [D,A,L,B,y]; rw [ex8]; ring_nf; positivity
          by_contra hn
          have hm:=mul_le_mul_of_nonneg_right (show 2≤t by omega) (show 0≤L x y by omega)
          nlinarith only [fe.2,ff,hm]
        have er2 : r2=1 := by omega
        subst r1; subst t; subst r2
        have c3 : 0≤A x y y-1-2*Fp0 := by dsimp [Fp0,s2,Dp,A,SV,SU,L,B,y]; rw [ex8]; ring_nf; positivity
        simp only [show ¬(x=4 ∧ (8:ℤ)=8) by omega,ite_false,add_zero]
        exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩
    · have hne : ¬(x=4 ∧ q=8) := by omega
      simp only [if_neg hne,add_zero]
      have hm:=mul_le_mul_of_nonneg_right hr.2.2.1 (show 0≤L x y by omega)
      have fcap : F0<(q-1)*(y+1)+2*L x y := by
        have eidentity : D+K x y y-q*L x y=D-(q-1)*(y+1) := by dsimp [D,K,H,L,B,y]; ring
        dsimp [E,s1] at ee
        dsimp [F0,s2]
        nlinarith only [ee.2,fe.2,hm,eidentity,d0]
      have ts : 2*Fp0<8*L x y+6*(q-1)*y+6*q-4 := by
        have hys:=mul_le_mul_of_nonneg_right hs.1 (show 0≤y by omega)
        have hqs:=mul_le_mul_of_nonneg_right (show s2≤q by omega) (show 0≤y by omega)
        nlinarith only [fpid,fcap,hqs,hs.1,hs.2.1,hs.2.2]
      let v:=q-16
      have hv : 0≤v := by dsimp [v]; omega
      have eq16 : q=v+16 := by dsimp [v]; ring
      have slack : 0<A x y y-1-(8*L x y+6*(q-1)*y+6*q-4) := by
        dsimp [A,L,y]; rw [ex,eq16]; ring_nf; positivity
      exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩
  change (0≤2*D ∧ 2*D≤L x y-1) ∧
    (0≤2*Dp ∧ 2*Dp≤SV x y-1) ∧
    (0≤2*E ∧ 2*E≤K x y y-1) ∧
    (0≤2*(if ep0<0 then ep0+A x y y else ep0) ∧
      2*(if ep0<0 then ep0+A x y y else ep0)≤SW x y y-1) ∧
    (0≤2*(F0+(if x=4 ∧ q=8 then A x y y-K x y y else 0)) ∧
      2*(F0+(if x=4 ∧ q=8 then A x y y-K x y y else 0))≤A x y y-1) ∧
    (0≤2*(Fp0+(if x=4 ∧ q=8 then 2*A x y y-SW x y y else 0)) ∧
      2*(Fp0+(if x=4 ∧ q=8 then 2*A x y y-SW x y y else 0))≤A x y y-1)
  exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩,⟨by omega,by omega⟩,epwin,xwin.1,xwin.2⟩

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter
