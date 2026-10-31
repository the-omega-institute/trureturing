/- GID: D5/S3/Combinatorics/Circle/FourNegative/AscendingD2/Arithmetic
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/AscendingD2/Arithmetic
   mirror-E: none(waiver:private-consumed-strip-bounds)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Uniform two-coordinate seam and peak inequalities for all ascending d-two chambers. -/
import D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Source

/-! Polynomial strip margins for the explicit masks, including the three small-a regimes. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.AscendingD2

private abbrev Coeff := ℤ × ℤ × ℤ
private def oldMass (R T Z : ℤ) (m : Coeff) : ℤ :=
  m.1*(4*R*T+4*R+5)+m.2.1*((4*R+5)*Z+1)+m.2.2*(5*T*Z+T+1)
private def newMass (R T Z : ℤ) (m : Coeff) : ℤ :=
  m.1*(8*R*T+8*R+9)+m.2.1*((8*R+9)*Z+1)+m.2.2*(9*T*Z+T+1)
private def margins (R T Z : ℤ) (p q r : Coeff) : Prop :=
  let A := 1+R+R*T+R*T*Z
  let C := 2*R*T*Z-1
  let N := 4*R*T*Z-1
  let x := -3*R*T*Z+R*(T+1)+2
  let w := -4*R*T*Z+5*T*Z+T+2
  let v := -4*R*T*Z+(4*R+5)*Z+2
  let u := -4*R*T*Z+4*R*T+4*R+6
  let xn := -7*R*T*Z+R*(T+1)+2
  let wn := -8*R*T*Z+9*T*Z+T+2
  let vn := -8*R*T*Z+(8*R+9)*Z+2
  let un := -8*R*T*Z+8*R*T+8*R+10
  let P := 2*oldMass R T Z p
  let Q := 2*oldMass R T Z q
  let S := 2*oldMass R T Z r
  let Pn := 2*A+2*newMass R T Z p
  let Qn := 2*newMass R T Z q
  let Sn := 2*newMass R T Z r
  0≤A ∧ A≤N ∧ P≤2*C ∧ 0≤P+x ∧ P+x+Q≤2*C ∧ 0≤P+x+Q+w ∧
    P+x+Q+w+S≤2*C ∧ 0≤P+x+Q+w+S+v ∧ 0≤-u ∧ -u≤2*C ∧
    Pn≤2*N ∧ 0≤Pn+xn ∧ Pn+xn+Qn≤2*N ∧ 0≤Pn+xn+Qn+wn ∧
    Pn+xn+Qn+wn+Sn≤2*N ∧ 0≤Pn+xn+Qn+wn+Sn+vn ∧ 0≤-un ∧ -un≤2*N

set_option maxHeartbeats 2000000 in
private theorem large_margins (r s t : ℤ) (hr : 1≤r) (hs : 1≤s) (ht : 1≤t) :
    margins (16*r) (32*r*s) (64*r*s*t)
      (0,0,5*r) (0,(8*r+1)*s,3*r-1) ((16*r*s+1)*t,(8*r-1)*s-1,0) := by
  obtain ⟨r0,hr0,rfl⟩ : ∃ r0 : ℤ, 0≤r0 ∧ r=r0+1 := ⟨r-1,by omega,by omega⟩
  obtain ⟨s0,hs0,rfl⟩ : ∃ s0 : ℤ, 0≤s0 ∧ s=s0+1 := ⟨s-1,by omega,by omega⟩
  obtain ⟨t0,ht0,rfl⟩ : ∃ t0 : ℤ, 0≤t0 ∧ t=t0+1 := ⟨t-1,by omega,by omega⟩
  dsimp [margins,oldMass,newMass]
  repeat' constructor
  all_goals apply sub_nonneg.mp
  all_goals ring_nf
  all_goals positivity

set_option maxHeartbeats 1500000 in
private theorem small_margins (r u v : ℤ) (hr : r=1 ∨ r=2) (hu : 1≤u) (hv : 1≤v) :
    margins (4*r) (16*u) (32*u*v)
      (0,u,r) (0,4*u,r-1) ((8*u+1)*v,3*u-1,0) := by
  obtain ⟨u0,hu0,rfl⟩ : ∃ u0 : ℤ, 0≤u0 ∧ u=u0+1 := ⟨u-1,by omega,by omega⟩
  obtain ⟨v0,hv0,rfl⟩ : ∃ v0 : ℤ, 0≤v0 ∧ v=v0+1 := ⟨v-1,by omega,by omega⟩
  rcases hr with rfl|rfl <;> dsimp [margins,oldMass,newMass]
  all_goals repeat' constructor
  all_goals apply sub_nonneg.mp
  all_goals ring_nf
  all_goals positivity

set_option maxHeartbeats 1000000 in
private theorem tail_margins (z : ℤ) (hz : 1≤z) :
    margins 4 8 (128*z) (8*z,0,1) (z,2,0) (32*z,1,0) := by
  obtain ⟨z0,hz0,rfl⟩ : ∃ z0 : ℤ, 0≤z0 ∧ z=z0+1 := ⟨z-1,by omega,by omega⟩
  dsimp [margins,oldMass,newMass]
  repeat' constructor
  all_goals apply sub_nonneg.mp
  all_goals ring_nf
  all_goals positivity

end D5.S3.Combinatorics.Circle.FourNegative.AscendingD2
