/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakEqualSecond/Rounded
   generality: I
   mirror-B: none(waiver:private-consumed-rounded-windows)
   mirror-E: none(waiver:private-consumed-rounded-windows)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Paired middle windows for adjacent, quadruple and floor-selected physical masks. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualSecond.Arithmetic

/-! The W mask is selected in the same realization as the V rounding. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualSecond
open private A B L K H SU SV SW window roundedV large_margins rounding_bounds outer_windows
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualSecond.Arithmetic
open private floor_bounds from D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoFloors

set_option maxHeartbeats 2400000 in
private theorem adjacent_margins (x m : ℤ) (hx : 4≤x) (hm : 8≤m) :
    let y:=2*x
    let z:=m*y
    A x y z>K y z-L x y z ∧ A x y z>SW y z-2*SV x y z ∧
    SW y z>SV x y z+A x y z ∧
    2*SU x y*(K y z-L x y z)>B x y*(3*A x y z+1+2*SU x y) := by
  dsimp only
  let u:=x-4
  let t:=m-8
  have hu : 0≤u := by dsimp [u];omega
  have ht : 0≤t := by dsimp [t];omega
  have ex : x=u+4 := by dsimp [u];ring
  have em : m=t+8 := by dsimp [t];ring
  have p0 : 0 < A x (2*x) (m*(2*x))-K (2*x) (m*(2*x))+L x (2*x) (m*(2*x)) := by
    dsimp [A,B,L,K,H,SU,SV,SW]
    simp only [ex,em]
    ring_nf
    positivity
  have p1 : 0 < A x (2*x) (m*(2*x))-SW (2*x) (m*(2*x))+2*SV x (2*x) (m*(2*x)) := by
    dsimp [A,B,L,K,H,SU,SV,SW]
    simp only [ex,em]
    ring_nf
    positivity
  have p2 : 0 < SW (2*x) (m*(2*x))-SV x (2*x) (m*(2*x))-A x (2*x) (m*(2*x)) := by
    dsimp [A,B,L,K,H,SU,SV,SW]
    simp only [ex,em]
    ring_nf
    positivity
  have p3 : 0 < 2*SU x (2*x)*(K (2*x) (m*(2*x))-L x (2*x) (m*(2*x)))-B x (2*x)*(3*A x (2*x) (m*(2*x))+1+2*SU x (2*x)) := by
    dsimp [A,B,L,K,H,SU,SV,SW]
    simp only [ex,em]
    ring_nf
    positivity
  exact ⟨by omega,by omega,by omega,by omega⟩

private theorem adjacent_middle (x m : ℤ) (hx : 4≤x) (hm : 8≤m) :
    let y:=2*x
    let z:=m*y
    let v:=roundedV x y z
    window (K y z-L x y z-v*B x y) (K y z) ∧
    window (SW y z-SV x y z+A x y z-v*SU x y) (SW y z) := by
  dsimp only
  obtain ⟨hB,hU,hA,hprod,hmB,hLA,h3L,h3V,hVA,hAH,hLAH⟩ := large_margins x 1 m hx (by omega) hm
  obtain ⟨hv,hvm,hvB,hvU,hvlo⟩ := rounding_bounds x 1 m hx (by omega) hm
  obtain ⟨hAK,hAS,hSA,hprodK⟩ := adjacent_margins x m hx hm
  simp only [mul_one,one_mul] at *
  have hf:=floor_bounds (3*A x (2*x) (m*(2*x))+2*SU x (2*x)) (2*SU x (2*x)) (by omega)
  change 2*SU x (2*x)*roundedV x (2*x) (m*(2*x))≤_ ∧ _<_ at hf
  have hvK : roundedV x (2*x) (m*(2*x))*B x (2*x)<K (2*x) (m*(2*x))-L x (2*x) (m*(2*x)) := by
    have hp:=mul_nonneg (by nlinarith only [hf.1] :
      0≤3*A x (2*x) (m*(2*x))+2*SU x (2*x)-2*SU x (2*x)*roundedV x (2*x) (m*(2*x))) hB.le
    apply (mul_lt_mul_iff_of_pos_left (show 0<2*SU x (2*x) by omega)).mp
    nlinarith only [hp,hprodK,hB]
  have hVB : 0<roundedV x (2*x) (m*(2*x))*B x (2*x) := mul_pos (by omega) hB
  unfold window
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  all_goals nlinarith only [hvK,hAK,hLA,hAS,hSA,hvlo,hvU,hVB]

set_option maxHeartbeats 2400000 in
private theorem quadruple_margins (x m : ℤ) (hx : 4≤x) (hm : 8≤m) :
    let y:=4*x
    let z:=m*y
    K y z-2*L x y z>A x y z ∧ K y z<4*L x y z ∧
    H y z>4*z+4 := by
  dsimp only
  let u:=x-4
  let t:=m-8
  have hu : 0≤u := by dsimp [u];omega
  have ht : 0≤t := by dsimp [t];omega
  have ex : x=u+4 := by dsimp [u];ring
  have em : m=t+8 := by dsimp [t];ring
  have p0 : 0 < K (4*x) (m*(4*x))-2*L x (4*x) (m*(4*x))-A x (4*x) (m*(4*x)) := by
    dsimp [A,B,L,K,H,SU,SV,SW]
    simp only [ex,em]
    ring_nf
    positivity
  have p1 : 0 < 4*L x (4*x) (m*(4*x))-K (4*x) (m*(4*x)) := by
    dsimp [A,B,L,K,H,SU,SV,SW]
    simp only [ex,em]
    ring_nf
    positivity
  have p2 : 0 < H (4*x) (m*(4*x))-4*(m*(4*x))-4 := by
    dsimp [A,B,L,K,H,SU,SV,SW]
    simp only [ex,em]
    ring_nf
    positivity
  exact ⟨by omega,by omega,by omega⟩

private theorem quadruple_middle (x m : ℤ) (hx : 4≤x) (hm : 8≤m) :
    let y:=4*x
    let z:=m*y
    let v:=roundedV x y z
    window (K y z-2*L x y z-v*B x y) (K y z) ∧
    window (SW y z-2*SV x y z+A x y z-v*SU x y) (SW y z) := by
  dsimp only
  obtain ⟨hB,hU,hA,hprod,hmB,hLA,h3L,h3V,hVA,hAH,hLAH⟩ := large_margins x 2 m hx (by omega) hm
  obtain ⟨hv,hvm,hvB,hvU,hvlo⟩ := rounding_bounds x 2 m hx (by omega) hm
  obtain ⟨hRA,hK4,hH4⟩ := quadruple_margins x m hx hm
  norm_num only [show (2:ℤ)*2=4 by norm_num] at *
  have he : SW (4*x) (m*(4*x))-2*SV x (4*x) (m*(4*x)) =
      2*(K (4*x) (m*(4*x))-2*L x (4*x) (m*(4*x)))-H (4*x) (m*(4*x))+2+2*(m*(4*x)) := by
    dsimp [SW,SV];ring
  have he' : SW (4*x) (m*(4*x))-4*SV x (4*x) (m*(4*x)) =
      2*(K (4*x) (m*(4*x))-4*L x (4*x) (m*(4*x)))-H (4*x) (m*(4*x))+4+4*(m*(4*x)) := by
    dsimp [SW,SV];ring
  have hVB : 0<roundedV x (4*x) (m*(4*x))*B x (4*x) := mul_pos (by omega) hB
  have hz : 0<m*(4*x)+1 := by positivity
  unfold window
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · nlinarith only [hRA,hvB]
  · nlinarith only [hK4,hVB]
  · nlinarith only [he,hRA,hAH,hvU,hz]
  · nlinarith only [he',hK4,hH4,hvlo,hA,hU]

set_option maxHeartbeats 2400000 in
private theorem separated_margins (x r m : ℤ) (hx : 4≤x) (hr : 4≤r) (hm : 8≤m) :
    let y:=2*r*x
    let z:=m*y
    4*L x y z<K y z ∧ 2*K y z<y*L x y z := by
  dsimp only
  let u:=x-4
  let t:=m-8
  let v:=r-4
  have hu : 0≤u := by dsimp [u];omega
  have ht : 0≤t := by dsimp [t];omega
  have hv : 0≤v := by dsimp [v];omega
  have ex : x=u+4 := by dsimp [u];ring
  have em : m=t+8 := by dsimp [t];ring
  have er : r=v+4 := by dsimp [v];ring
  have p0 : 0 < K (2*r*x) (m*(2*r*x))-4*L x (2*r*x) (m*(2*r*x)) := by
    dsimp [A,B,L,K,H,SU,SV,SW]
    simp only [ex,em,er]
    ring_nf
    positivity
  have p1 : 0 < (2*r*x)*L x (2*r*x) (m*(2*r*x))-2*K (2*r*x) (m*(2*r*x)) := by
    dsimp [A,B,L,K,H,SU,SV,SW]
    simp only [ex,em,er]
    ring_nf
    positivity
  exact ⟨by omega,by omega⟩

private def roundedW (x y z : ℤ) : ℤ := K y z/L x y z-1

private theorem separated_middle (x r m : ℤ) (hx : 4≤x) (hr : 4≤r) (hm : 8≤m) :
    let y:=2*r*x
    let z:=m*y
    let v:=roundedV x y z
    let w:=roundedW x y z
    0≤w ∧ 2*w≤y-2 ∧
    window (K y z-w*L x y z-v*B x y) (K y z) ∧
    window (SW y z-w*SV x y z+A x y z-v*SU x y) (SW y z) := by
  dsimp only
  let y:=2*r*x
  let z:=m*y
  let AA:=A x y z
  let BB:=B x y
  let LL:=L x y z
  let KK:=K y z
  let HH:=H y z
  let UU:=SU x y
  let VV:=SV x y z
  let WW:=SW y z
  let v:=roundedV x y z
  let w:=roundedW x y z
  obtain ⟨hB,hU,hA,hprod,hmB,hLA,h3L,h3V,hVA,hAH,hLAH⟩ := large_margins x r m hx (by omega) hm
  obtain ⟨hv,hvm,hvB,hvU,hvlo⟩ := rounding_bounds x r m hx (by omega) hm
  obtain ⟨hK4,hyL⟩ := separated_margins x r m hx hr hm
  change 0<BB at hB
  change 0<UU at hU
  change AA>1+2*UU at hA
  change LL>AA at hLA
  change AA>HH at hAH
  change 2*LL>AA+HH at hLAH
  change 1≤v at hv
  change v*BB<AA at hvB
  change v*UU<2*AA at hvU
  change 3*AA+1≤2*v*UU at hvlo
  change 4*LL<KK at hK4
  change 2*KK<y*LL at hyL
  have hL : 0<LL := by omega
  have hf:=floor_bounds KK LL hL
  have hw0 : 3≤w := by
    change 3≤KK/LL-1
    nlinarith only [hf.2,hK4,hL]
  have hwy : 2*w≤y-2 := by
    have hh : 2*(KK/LL)<y := by
      apply (mul_lt_mul_iff_of_pos_right hL).mp
      nlinarith only [hf.1,hyL]
    change 2*(KK/LL-1)≤y-2
    omega
  have hRlo : LL≤KK-w*LL := by dsimp [w,roundedW,KK,LL] at *;nlinarith only [hf.1]
  have hRhi : KK-w*LL<2*LL := by dsimp [w,roundedW,KK,LL] at *;nlinarith only [hf.2]
  have hVB : 0<v*BB := mul_pos (by omega) hB
  have hz : 0<z+1 := by dsimp [z,y];positivity
  have hcharge : 2*w*(z+1)<HH := by
    have hh:=mul_nonneg (by omega : 0≤y-2-2*w) hz.le
    have he : HH=(y-2)*(z+1)+3+2*z := by dsimp [HH,H];ring
    nlinarith only [hh,he,hz]
  have he : WW-w*VV=2*(KK-w*LL)-HH+w*(z+1) := by dsimp [WW,VV,KK,LL,HH,SW,SV];ring
  have heW : WW=2*KK-HH := rfl
  have hwz : 0≤w*(z+1) := mul_nonneg (by omega) hz.le
  change 0≤w ∧ 2*w≤y-2 ∧ window (KK-w*LL-v*BB) KK ∧ window (WW-w*VV+AA-v*UU) WW
  unfold window
  refine ⟨by omega,hwy,⟨by omega,by omega⟩,⟨?_,?_⟩⟩
  · nlinarith only [he,hRlo,hvU,hLAH,hwz]
  · nlinarith only [he,heW,hRhi,hcharge,hvlo,hK4,hA,hU]

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualSecond
