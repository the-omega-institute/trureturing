/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakEqualSecond/Arithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-window-arithmetic)
   mirror-E: none(waiver:private-consumed-window-arithmetic)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Exact rounded allocations and paired windows on the equal-second third-peak face. -/
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native
import D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoFloors

/-! Integer windows for literal dyadic bank allocations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualSecond
private def A (x y z : ℤ) : ℤ := 1+x+x*y+x*y*z
private def B (x y : ℤ) : ℤ := 1+y+x*y+x*y*y
private def L (x y z : ℤ) : ℤ := 1+z+y*z+x*y*z
private def K (y z : ℤ) : ℤ := 1+y+y*z+y*y*z
private def H (y z : ℤ) : ℤ := 1+y+y*z
private def SU (x y : ℤ) : ℤ := 2*B x y-1
private def SV (x y z : ℤ) : ℤ := 2*L x y z-1-z
private def SW (y z : ℤ) : ℤ := 2*K y z-H y z
private def window (e t : ℤ) : Prop := 0≤e ∧ 2*e≤t-1

set_option maxHeartbeats 2400000 in
private theorem large_margins (x r m : ℤ) (hx : 4≤x) (hr : 1≤r) (hm : 8≤m) :
    let y := 2*r*x
    let z := m*y
    0<B x y ∧ 0<SU x y ∧ A x y z>1+2*SU x y ∧
    2*SU x y*A x y z>B x y*(3*A x y z+1+2*SU x y) ∧
    m*B x y>A x y z ∧ L x y z>A x y z ∧
    3*A x y z>2*L x y z+1 ∧ 3*A x y z>SV x y z ∧
    SV x y z>2*A x y z ∧ A x y z>H y z ∧
    2*L x y z>A x y z+H y z := by
  dsimp only
  let u:=x-4
  let v:=r-1
  let t:=m-8
  have hu : 0≤u := by dsimp [u];omega
  have hv : 0≤v := by dsimp [v];omega
  have ht : 0≤t := by dsimp [t];omega
  have ex : x=u+4 := by dsimp [u];ring
  have er : r=v+1 := by dsimp [v];ring
  have em : m=t+8 := by dsimp [t];ring
  have p0 : 0 < B x (2*r*x) := by
    dsimp [A,B,L,K,H,SU,SV,SW]
    simp only [ex,er,em]
    ring_nf
    positivity
  have p1 : 0 < SU x (2*r*x) := by
    dsimp [A,B,L,K,H,SU,SV,SW]
    simp only [ex,er,em]
    ring_nf
    positivity
  have p2 : 0 < A x (2*r*x) (m*(2*r*x))-1-2*SU x (2*r*x) := by
    dsimp [A,B,L,K,H,SU,SV,SW]
    simp only [ex,er,em]
    ring_nf
    positivity
  have p3 : 0 < 2*SU x (2*r*x)*A x (2*r*x) (m*(2*r*x))-B x (2*r*x)*(3*A x (2*r*x) (m*(2*r*x))+1+2*SU x (2*r*x)) := by
    dsimp [A,B,L,K,H,SU,SV,SW]
    simp only [ex,er,em]
    ring_nf
    positivity
  have p4 : 0 < m*B x (2*r*x)-A x (2*r*x) (m*(2*r*x)) := by
    dsimp [A,B,L,K,H,SU,SV,SW]
    simp only [ex,er,em]
    ring_nf
    positivity
  have p5 : 0 < L x (2*r*x) (m*(2*r*x))-A x (2*r*x) (m*(2*r*x)) := by
    dsimp [A,B,L,K,H,SU,SV,SW]
    simp only [ex,er,em]
    ring_nf
    positivity
  have p6 : 0 < 3*A x (2*r*x) (m*(2*r*x))-2*L x (2*r*x) (m*(2*r*x))-1 := by
    dsimp [A,B,L,K,H,SU,SV,SW]
    simp only [ex,er,em]
    ring_nf
    positivity
  have p7 : 0 < 3*A x (2*r*x) (m*(2*r*x))-SV x (2*r*x) (m*(2*r*x)) := by
    dsimp [A,B,L,K,H,SU,SV,SW]
    simp only [ex,er,em]
    ring_nf
    positivity
  have p8 : 0 < SV x (2*r*x) (m*(2*r*x))-2*A x (2*r*x) (m*(2*r*x)) := by
    dsimp [A,B,L,K,H,SU,SV,SW]
    simp only [ex,er,em]
    ring_nf
    positivity
  have p9 : 0 < A x (2*r*x) (m*(2*r*x))-H (2*r*x) (m*(2*r*x)) := by
    dsimp [A,B,L,K,H,SU,SV,SW]
    simp only [ex,er,em]
    ring_nf
    positivity
  have p10 : 0 < 2*L x (2*r*x) (m*(2*r*x))-A x (2*r*x) (m*(2*r*x))-H (2*r*x) (m*(2*r*x)) := by
    dsimp [A,B,L,K,H,SU,SV,SW]
    simp only [ex,er,em]
    ring_nf
    positivity
  exact ⟨p0,p1,by omega,by omega,by omega,by omega,by omega,by omega,by omega,by omega,by omega⟩

open private floor_bounds from D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoFloors

private def roundedV (x y z : ℤ) : ℤ := (3*A x y z+2*SU x y)/(2*SU x y)

set_option maxHeartbeats 1200000 in
private theorem rounding_bounds (x r m : ℤ) (hx : 4≤x) (hr : 1≤r) (hm : 8≤m) :
    let y := 2*r*x
    let z := m*y
    let v := roundedV x y z
    1≤v ∧ v<m ∧ v*B x y<A x y z ∧ v*SU x y<2*A x y z ∧
    3*A x y z+1≤2*v*SU x y := by
  dsimp only
  let y:=2*r*x
  let z:=m*y
  let AA:=A x y z
  let BB:=B x y
  let UU:=SU x y
  let v:=roundedV x y z
  obtain ⟨hB,hU,hA,hprod,hmB,hLA,h3L,h3V,hVA,hAH,hLAH⟩ := large_margins x r m hx hr hm
  change 0<BB at hB
  change 0<UU at hU
  change AA>1+2*UU at hA
  change 2*UU*AA>BB*(3*AA+1+2*UU) at hprod
  change m*BB>AA at hmB
  have hf:=floor_bounds (3*AA+2*UU) (2*UU) (by omega)
  change 2*UU*v≤3*AA+2*UU ∧ 3*AA+2*UU<2*UU*(v+1) at hf
  have hvlo : 3*AA+1≤2*v*UU := by nlinarith only [hf.2]
  have hvpos : 1≤v := by nlinarith only [hvlo,hA,hU]
  have hvU : v*UU<2*AA := by nlinarith only [hf.1,hA]
  have hvB : v*BB<AA := by
    have hp:=mul_nonneg (by nlinarith only [hf.1] : 0≤3*AA+2*UU-2*UU*v) hB.le
    apply (mul_lt_mul_iff_of_pos_left (show 0<2*UU by omega)).mp
    nlinarith only [hp,hprod,hB]
  have hvm : v<m := by nlinarith only [hvB,hmB,hB]
  exact ⟨hvpos,hvm,hvB,hvU,hvlo⟩

private theorem outer_windows (x r m : ℤ) (hx : 4≤x) (hr : 1≤r) (hm : 8≤m) :
    let y:=2*r*x
    let z:=m*y
    let v:=roundedV x y z
    window (L x y z-v*B x y) (L x y z) ∧
    window (SV x y z-v*SU x y) (SV x y z) ∧
    window (A x y z-v*B x y) (A x y z) ∧
    window (2*A x y z-v*SU x y) (A x y z) := by
  dsimp only
  obtain ⟨hB,hU,hA,hprod,hmB,hLA,h3L,h3V,hVA,hAH,hLAH⟩ := large_margins x r m hx hr hm
  obtain ⟨hv,hvm,hvB,hvU,hvlo⟩ := rounding_bounds x r m hx hr hm
  have hdiff : 2*B x (2*r*x)-SU x (2*r*x)=1 := by dsimp [SU];ring
  have hcharge : 2*roundedV x (2*r*x) (m*(2*r*x))*B x (2*r*x)-
      roundedV x (2*r*x) (m*(2*r*x))*SU x (2*r*x)=roundedV x (2*r*x) (m*(2*r*x)) := by
    dsimp [SU];ring
  unfold window
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩
  all_goals nlinarith only [hvB,hvU,hvlo,hLA,h3L,h3V,hVA,hcharge,hv]

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualSecond
