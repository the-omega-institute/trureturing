/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakCSecond/PolynomialsCorner
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:physical-dependent-source-registration-at-endpoint)
   anchors: [mathlib/module/Mathlib.Data.Int.Basic]
   utility: none
   digest: Nine tight-quotient identities for the full unbounded small-corner C4 chart. -/
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.Polynomials
import Batteries.Tactic.OpenPrivate
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond
open private UniformBounds uniformBounds_mk
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.Polynomials

set_option maxHeartbeats 1600000 in
private theorem small_corner_old_first_lower (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 4
  let y : ℤ := 8
  let z : ℤ := 16
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 1+J
  let s : ℤ := 11*g
  let D : ℤ := y*z+y+1
  let A : ℤ := x*D+1
  let B : ℤ := x*t*(y+1)+t+1
  let L : ℤ := x*z*t+z*t+z+1
  let M : ℤ := t*y*z+D
  let Mn : ℤ := 2*M-D
  0 ≤ t*A-2*s*M := by
  dsimp only
  calc
    0 ≤ 3262 +
        3258*J := by positivity
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private theorem small_corner_old_first_peak (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 4
  let y : ℤ := 8
  let z : ℤ := 16
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 1+J
  let s : ℤ := 11*g
  let D : ℤ := y*z+y+1
  let A : ℤ := x*D+1
  let B : ℤ := x*t*(y+1)+t+1
  let L : ℤ := x*z*t+z*t+z+1
  let M : ℤ := t*y*z+D
  let Mn : ℤ := 2*M-D
  0 ≤ A-1-(t*A-2*s*M) := by
  dsimp only
  calc
    0 ≤ 1122 +
        1126*J := by positivity
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private theorem small_corner_new_first_lower (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 4
  let y : ℤ := 8
  let z : ℤ := 16
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 1+J
  let s : ℤ := 11*g
  let D : ℤ := y*z+y+1
  let A : ℤ := x*D+1
  let B : ℤ := x*t*(y+1)+t+1
  let L : ℤ := x*z*t+z*t+z+1
  let M : ℤ := t*y*z+D
  let Mn : ℤ := 2*M-D
  0 ≤ 2*(t-1)*A-2*s*Mn := by
  dsimp only
  calc
    0 ≤ 768 +
        762*J := by positivity
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private theorem small_corner_new_first_peak (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 4
  let y : ℤ := 8
  let z : ℤ := 16
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 1+J
  let s : ℤ := 11*g
  let D : ℤ := y*z+y+1
  let A : ℤ := x*D+1
  let B : ℤ := x*t*(y+1)+t+1
  let L : ℤ := x*z*t+z*t+z+1
  let M : ℤ := t*y*z+D
  let Mn : ℤ := 2*M-D
  0 ≤ A-1-(2*(t-1)*A-2*s*Mn) := by
  dsimp only
  calc
    0 ≤ 3616 +
        3622*J := by positivity
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private theorem small_corner_tight_old_bank (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 4
  let y : ℤ := 8
  let z : ℤ := 16
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 1+J
  let s : ℤ := 11*g
  let D : ℤ := y*z+y+1
  let A : ℤ := x*D+1
  let B : ℤ := x*t*(y+1)+t+1
  let L : ℤ := x*z*t+z*t+z+1
  let M : ℤ := t*y*z+D
  let Mn : ℤ := 2*M-D
  0 ≤ B-H*M-1 := by
  dsimp only
  calc
    0 ≤ 507 +
        503*J := by positivity
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private theorem small_corner_tight_r_capacity (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 4
  let y : ℤ := 8
  let z : ℤ := 16
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 1+J
  let s : ℤ := 11*g
  let D : ℤ := y*z+y+1
  let A : ℤ := x*D+1
  let B : ℤ := x*t*(y+1)+t+1
  let L : ℤ := x*z*t+z*t+z+1
  let M : ℤ := t*y*z+D
  let Mn : ℤ := 2*M-D
  0 ≤ H*Mn-B := by
  dsimp only
  calc
    0 ≤ 4 +
        9*J := by positivity
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private theorem small_corner_bit_divisor_capacity (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 4
  let y : ℤ := 8
  let z : ℤ := 16
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 1+J
  let s : ℤ := 11*g
  let D : ℤ := y*z+y+1
  let A : ℤ := x*D+1
  let B : ℤ := x*t*(y+1)+t+1
  let L : ℤ := x*z*t+z*t+z+1
  let M : ℤ := t*y*z+D
  let Mn : ℤ := 2*M-D
  0 ≤ g-H := by
  dsimp only
  calc
    0 ≤ (0 : ℤ) := by positivity
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private theorem small_corner_third_tight_lower (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 4
  let y : ℤ := 8
  let z : ℤ := 16
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 1+J
  let s : ℤ := 11*g
  let D : ℤ := y*z+y+1
  let A : ℤ := x*D+1
  let B : ℤ := x*t*(y+1)+t+1
  let L : ℤ := x*z*t+z*t+z+1
  let M : ℤ := t*y*z+D
  let Mn : ℤ := 2*M-D
  0 ≤ L-B-H*M := by
  dsimp only
  calc
    0 ≤ 323 +
        247*J := by positivity
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private theorem small_corner_third_upper (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 4
  let y : ℤ := 8
  let z : ℤ := 16
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 1+J
  let s : ℤ := 11*g
  let D : ℤ := y*z+y+1
  let A : ℤ := x*D+1
  let B : ℤ := x*t*(y+1)+t+1
  let L : ℤ := x*z*t+z*t+z+1
  let M : ℤ := t*y*z+D
  let Mn : ℤ := 2*M-D
  0 ≤ 2*B-L-1 := by
  dsimp only
  calc
    0 ≤ 184 +
        256*J := by positivity
    _ = _ := by ring

private theorem chart_small_corner (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 4
  let y : ℤ := 8
  let z : ℤ := 16
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 1+J
  let s : ℤ := 11*g
  let D : ℤ := y*z+y+1
  let A : ℤ := x*D+1
  let B : ℤ := x*t*(y+1)+t+1
  let L : ℤ := x*z*t+z*t+z+1
  let M : ℤ := t*y*z+D
  let Mn : ℤ := 2*M-D
  UniformBounds x y z t H g s := by
  dsimp only
  apply uniformBounds_mk
  · exact small_corner_old_first_lower Y T J E hY hT hJ hE
  · exact small_corner_old_first_peak Y T J E hY hT hJ hE
  · exact small_corner_new_first_lower Y T J E hY hT hJ hE
  · exact small_corner_new_first_peak Y T J E hY hT hJ hE
  · exact small_corner_tight_old_bank Y T J E hY hT hJ hE
  · exact small_corner_tight_r_capacity Y T J E hY hT hJ hE
  · exact small_corner_bit_divisor_capacity Y T J E hY hT hJ hE
  · left
    exact ⟨by ring, small_corner_third_tight_lower Y T J E hY hT hJ hE,
      small_corner_third_upper Y T J E hY hT hJ hE⟩

end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond
