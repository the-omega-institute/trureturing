/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakEqualSecond/Paid
   generality: I
   mirror-B: none(waiver:private-consumed-paid-windows)
   mirror-E: none(waiver:private-consumed-paid-windows)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Simultaneous paid-packet windows including both small-gap dyadic boundaries. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualSecond.Arithmetic

/-! The fresh occurrence is in the fourth positive bank. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualSecond
open private A B L K H SU SV SW window
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualSecond.Arithmetic
private def paidQ (r : ℤ) : ℤ := if r=1 then 1 else 0
private def paidW (r : ℤ) : ℤ := if r=1 then 2 else r

set_option maxHeartbeats 2400000 in
private theorem paid_margins (x r m : ℤ) (hx : 4≤x) (hr : 1≤r) (hm : 2≤m) :
    let y:=2*r*x
    let z:=m*y
    0<m*B x y-A x y z ∧ 0<m*SU x y-2*A x y z ∧
    0<L x y z-A x y z ∧ 0<SV x y z-2*A x y z ∧
    0<L x y z-1-2*(L x y z-A x y z) ∧
    0<SV x y z-1-2*(SV x y z-2*A x y z) := by
  dsimp only
  let u:=x-4
  let v:=r-1
  let t:=m-2
  have hu : 0≤u := by dsimp [u];omega
  have hv : 0≤v := by dsimp [v];omega
  have ht : 0≤t := by dsimp [t];omega
  have ex : x=u+4 := by dsimp [u];ring
  have er : r=v+1 := by dsimp [v];ring
  have em : m=t+2 := by dsimp [t];ring
  have p0 : 0 < m*B x (2*r*x)-A x (2*r*x) (m*(2*r*x)) := by
    dsimp [A,B,L,K,H,SU,SV,SW]
    simp only [ex,er,em]
    ring_nf
    positivity
  have p1 : 0 < m*SU x (2*r*x)-2*A x (2*r*x) (m*(2*r*x)) := by
    dsimp [A,B,L,K,H,SU,SV,SW]
    simp only [ex,er,em]
    ring_nf
    positivity
  have p2 : 0 < L x (2*r*x) (m*(2*r*x))-A x (2*r*x) (m*(2*r*x)) := by
    dsimp [A,B,L,K,H,SU,SV,SW]
    simp only [ex,er,em]
    ring_nf
    positivity
  have p3 : 0 < SV x (2*r*x) (m*(2*r*x))-2*A x (2*r*x) (m*(2*r*x)) := by
    dsimp [A,B,L,K,H,SU,SV,SW]
    simp only [ex,er,em]
    ring_nf
    positivity
  have p4 : 0 < L x (2*r*x) (m*(2*r*x))-1-2*(L x (2*r*x) (m*(2*r*x))-A x (2*r*x) (m*(2*r*x))) := by
    dsimp [A,B,L,K,H,SU,SV,SW]
    simp only [ex,er,em]
    ring_nf
    positivity
  have p5 : 0 < SV x (2*r*x) (m*(2*r*x))-1-2*(SV x (2*r*x) (m*(2*r*x))-2*A x (2*r*x) (m*(2*r*x))) := by
    dsimp [A,B,L,K,H,SU,SV,SW]
    simp only [ex,er,em]
    ring_nf
    positivity
  exact ⟨p0,p1,p2,p3,p4,p5⟩

private theorem paid_first (x r m : ℤ) (hx : 4≤x) (hr : 1≤r) (hm : 2≤m)
    (hsmall : 4*m≤2*r*x ∨ r=1 ∧ m≤x) :
    let y:=2*r*x
    let z:=m*y
    window (m*B x y-A x y z) (B x y) ∧
    window (m*SU x y-2*A x y z) (SU x y) := by
  dsimp only
  obtain ⟨hlo,hlon,_,_,_,_⟩:=paid_margins x r m hx hr hm
  have hslack : 0<B x (2*r*x)-1-2*(m*B x (2*r*x)-A x (2*r*x) (m*(2*r*x))) := by
    rcases hsmall with hs|⟨rfl,hs⟩
    · let y:=2*r*x
      let C:=1+x+x*y
      have hyx : 2*x≤y := by dsimp [y];nlinarith
      have hC : 0<C := by dsimp [C];positivity
      have hCy : 0<C-y+x := by
        have hp:=mul_nonneg (by omega : 0≤x-1) (by omega : 0≤y)
        dsimp [C];nlinarith only [hp,hx]
      have hp:=mul_nonneg (by dsimp [y];omega : 0≤y-4*m) hC.le
      have hq:=mul_nonneg (by omega : 0≤2*m) hCy.le
      have he : B x y-1-2*(m*B x y-A x y (m*y))=
          (y-4*m)*C+2*m*(C-y+x)+2*C := by dsimp [A,B,C];ring
      change 0<B x y-1-2*(m*B x y-A x y (m*y))
      rw [he]
      nlinarith only [hp,hq,hC]
    · have he : B x (2*1*x)-1-2*(m*B x (2*1*x)-A x (2*1*x) (m*(2*1*x)))=
          4*(x-m)*x^2+4*(x-m)*x+2*(x-m)+2*x^2+2*x+2 := by dsimp [A,B];ring
      rw [he]
      positivity
  have he : SU x (2*r*x)-1-2*(m*SU x (2*r*x)-2*A x (2*r*x) (m*(2*r*x)))=
      2*(B x (2*r*x)-1-2*(m*B x (2*r*x)-A x (2*r*x) (m*(2*r*x))))+2*m := by
    dsimp [SU];ring
  unfold window
  exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩

set_option maxHeartbeats 2400000 in
private theorem paid_third (x r m : ℤ) (hx : 4≤x) (hr : 1≤r) (hm : 2≤m) :
    let y:=2*r*x
    let z:=m*y
    let q:=paidQ r
    let w:=paidW r
    window ((q+1)*K y z-A x y z-w*L x y z) (K y z) ∧
    window ((q+1)*SW y z-2*A x y z-w*SV x y z) (SW y z) := by
  dsimp only
  let u:=x-4
  let t:=m-2
  have hu : 0≤u := by dsimp [u];omega
  have ht : 0≤t := by dsimp [t];omega
  have ex : x=u+4 := by dsimp [u];ring
  have em : m=t+2 := by dsimp [t];ring
  by_cases hr1 : r=1
  · subst r
    simp only [paidQ,paidW,ite_true]
    have p0 : 0 < (1+1)*K (2*1*x) (m*(2*1*x))-A x (2*1*x) (m*(2*1*x))-2*L x (2*1*x) (m*(2*1*x)) := by
      dsimp [A,B,L,K,H,SU,SV,SW]
      simp only [ex,em]
      ring_nf
      positivity
    have p1 : 0 < K (2*1*x) (m*(2*1*x))-1-2*((1+1)*K (2*1*x) (m*(2*1*x))-A x (2*1*x) (m*(2*1*x))-2*L x (2*1*x) (m*(2*1*x))) := by
      dsimp [A,B,L,K,H,SU,SV,SW]
      simp only [ex,em]
      ring_nf
      positivity
    have p2 : 0 < (1+1)*SW (2*1*x) (m*(2*1*x))-2*A x (2*1*x) (m*(2*1*x))-2*SV x (2*1*x) (m*(2*1*x)) := by
      dsimp [A,B,L,K,H,SU,SV,SW]
      simp only [ex,em]
      ring_nf
      positivity
    have p3 : 0 < SW (2*1*x) (m*(2*1*x))-1-2*((1+1)*SW (2*1*x) (m*(2*1*x))-2*A x (2*1*x) (m*(2*1*x))-2*SV x (2*1*x) (m*(2*1*x))) := by
      dsimp [A,B,L,K,H,SU,SV,SW]
      simp only [ex,em]
      ring_nf
      positivity
    exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩
  · have hr2 : 2≤r := by omega
    simp only [paidQ,paidW,if_neg hr1]
    let v:=r-2
    have hv : 0≤v := by dsimp [v];omega
    have er : r=v+2 := by dsimp [v];ring
    have p0 : 0 < (0+1)*K (2*r*x) (m*(2*r*x))-A x (2*r*x) (m*(2*r*x))-r*L x (2*r*x) (m*(2*r*x)) := by
      dsimp [A,B,L,K,H,SU,SV,SW]
      simp only [ex,em,er]
      ring_nf
      positivity
    have p1 : 0 < K (2*r*x) (m*(2*r*x))-1-2*((0+1)*K (2*r*x) (m*(2*r*x))-A x (2*r*x) (m*(2*r*x))-r*L x (2*r*x) (m*(2*r*x))) := by
      dsimp [A,B,L,K,H,SU,SV,SW]
      simp only [ex,em,er]
      ring_nf
      positivity
    have p2 : 0 < (0+1)*SW (2*r*x) (m*(2*r*x))-2*A x (2*r*x) (m*(2*r*x))-r*SV x (2*r*x) (m*(2*r*x)) := by
      dsimp [A,B,L,K,H,SU,SV,SW]
      simp only [ex,em,er]
      ring_nf
      positivity
    have p3 : 0 < SW (2*r*x) (m*(2*r*x))-1-2*((0+1)*SW (2*r*x) (m*(2*r*x))-2*A x (2*r*x) (m*(2*r*x))-r*SV x (2*r*x) (m*(2*r*x))) := by
      dsimp [A,B,L,K,H,SU,SV,SW]
      simp only [ex,em,er]
      ring_nf
      positivity
    exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualSecond
