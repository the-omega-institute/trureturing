/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakEqualFirstTwoPlusTwo/Arithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:physical-dependent-source-registration-at-endpoint)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Unbounded polynomial slack and integer window bounds for the equal-first-two plus-two family. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo.Parameters

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo
open private A B L K SU SV SW E H1 H2 J1 J2 D T window firstTwo windows from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo.Parameters

-- Independent certificate 1: high_u0_old1.
private theorem cert01 (x t : ℤ) (hx : 8≤x) (ht : 8*x≤t) :
    0 < 4*t^2*x + 4*t^2 - 7*t*x^2 + t*x + 5*t - 2*x^2 - 2*x := by
  let p := x-8
  let q := t-8*x
  have hp : 0≤p := by dsimp [p]; omega
  have hq : 0≤q := by dsimp [q]; omega
  have he : 4*t^2*x + 4*t^2 - 7*t*x^2 + t*x + 5*t - 2*x^2 - 2*x =
      200*p^3 + 57*p^2*q + 5062*p^2 + 4*p*q^2 + 977*p*q + 42630*p + 36*q^2 + 4173*q + 119472 := by dsimp [p,q]; ring
  rw [he]
  positivity

-- Independent certificate 2: high_u0_old1upper.
private theorem cert02 (x t : ℤ) (hx : 8≤x) (ht : 8*x≤t) :
    0 < 7*t*x^2 - t*x - t + 2*x^2 + 2*x := by
  let p := x-8
  let q := t-8*x
  have hp : 0≤p := by dsimp [p]; omega
  have hq : 0≤q := by dsimp [q]; omega
  have he : 7*t*x^2 - t*x - t + 2*x^2 + 2*x =
      56*p^3 + 7*p^2*q + 1338*p^2 + 111*p*q + 10650*p + 439*q + 28240 := by dsimp [p,q]; ring
  rw [he]
  positivity

-- Independent certificate 3: high_u0_old2.
private theorem cert03 (x t : ℤ) (hx : 8≤x) (ht : 8*x≤t) :
    0 < 4*t^2*x - 4*t^2 - 7*t*x^2 + 9*t*x - 3*t - 2*x^2 := by
  let p := x-8
  let q := t-8*x
  have hp : 0≤p := by dsimp [p]; omega
  have hq : 0≤q := by dsimp [q]; omega
  have he : 4*t^2*x - 4*t^2 - 7*t*x^2 + 9*t*x - 3*t - 2*x^2 =
      200*p^3 + 57*p^2*q + 4614*p^2 + 4*p*q^2 + 857*p*q + 35400*p + 28*q^2 + 3205*q + 90304 := by dsimp [p,q]; ring
  rw [he]
  positivity

-- Independent certificate 4: high_u0_old2upper.
private theorem cert04 (x t : ℤ) (hx : 8≤x) (ht : 8*x≤t) :
    0 < 4*t^2 + 7*t*x^2 - 5*t*x + 3*t + 2*x^2 + x := by
  let p := x-8
  let q := t-8*x
  have hp : 0≤p := by dsimp [p]; omega
  have hq : 0≤q := by dsimp [q]; omega
  have he : 4*t^2 + 7*t*x^2 - 5*t*x + 3*t + 2*x^2 + x =
      56*p^3 + 7*p^2*q + 1562*p^2 + 171*p*q + 14265*p + 4*q^2 + 923*q + 42824 := by dsimp [p,q]; ring
  rw [he]
  positivity

-- Independent certificate 5: high_u0_new1.
private theorem cert05 (x t : ℤ) (hx : 8≤x) (ht : 8*x≤t) :
    0 < 8*t^2*x + 8*t^2 - 14*t*x^2 + 2*t*x + 6*t - 4*x^2 - 4*x - 2 := by
  let p := x-8
  let q := t-8*x
  have hp : 0≤p := by dsimp [p]; omega
  have hq : 0≤q := by dsimp [q]; omega
  have he : 8*t^2*x + 8*t^2 - 14*t*x^2 + 2*t*x + 6*t - 4*x^2 - 4*x - 2 =
      400*p^3 + 114*p^2*q + 10124*p^2 + 8*p*q^2 + 1954*p*q + 85228*p + 72*q^2 + 8342*q + 238686 := by dsimp [p,q]; ring
  rw [he]
  positivity

-- Independent certificate 6: high_u0_new1upper.
private theorem cert06 (x t : ℤ) (hx : 8≤x) (ht : 8*x≤t) :
    0 < 14*t*x^2 - 2*t*x - 2*t + 4*x^2 + 4*x + 2 := by
  let p := x-8
  let q := t-8*x
  have hp : 0≤p := by dsimp [p]; omega
  have hq : 0≤q := by dsimp [q]; omega
  have he : 14*t*x^2 - 2*t*x - 2*t + 4*x^2 + 4*x + 2 =
      112*p^3 + 14*p^2*q + 2676*p^2 + 222*p*q + 21300*p + 878*q + 56482 := by dsimp [p,q]; ring
  rw [he]
  positivity

-- Independent certificate 7: high_u0_new2.
private theorem cert07 (x t : ℤ) (hx : 8≤x) (ht : 8*x≤t) :
    0 < 8*t^2*x - 8*t^2 - 14*t*x^2 + 10*t*x - 2*t - 4*x^2 - 2*x - 2 := by
  let p := x-8
  let q := t-8*x
  have hp : 0≤p := by dsimp [p]; omega
  have hq : 0≤q := by dsimp [q]; omega
  have he : 8*t^2*x - 8*t^2 - 14*t*x^2 + 10*t*x - 2*t - 4*x^2 - 2*x - 2 =
      400*p^3 + 114*p^2*q + 9164*p^2 + 8*p*q^2 + 1706*p*q + 69806*p + 56*q^2 + 6350*q + 176750 := by dsimp [p,q]; ring
  rw [he]
  positivity

-- Independent certificate 8: high_u0_new2upper.
private theorem cert08 (x t : ℤ) (hx : 8≤x) (ht : 8*x≤t) :
    0 < 8*t^2 + 14*t*x^2 - 6*t*x + 2*t + 4*x^2 + 3*x + 2 := by
  let p := x-8
  let q := t-8*x
  have hp : 0≤p := by dsimp [p]; omega
  have hq : 0≤q := by dsimp [q]; omega
  have he : 8*t^2 + 14*t*x^2 - 6*t*x + 2*t + 4*x^2 + 3*x + 2 =
      112*p^3 + 14*p^2*q + 3156*p^2 + 346*p*q + 29011*p + 8*q^2 + 1874*q + 87450 := by dsimp [p,q]; ring
  rw [he]
  positivity

-- Independent certificate 9: high_u1_old1.
private theorem cert09 (x t : ℤ) (hx : 8≤x) (ht : 8*x≤t) :
    0 < 4*t^2*x + 4*t^2 - 15*t*x^2 + t*x + 5*t - 4*x^2 - 4*x - 2 := by
  let p := x-8
  let q := t-8*x
  have hp : 0≤p := by dsimp [p]; omega
  have hq : 0≤q := by dsimp [q]; omega
  have he : 4*t^2*x + 4*t^2 - 15*t*x^2 + t*x + 5*t - 4*x^2 - 4*x - 2 =
      136*p^3 + 49*p^2*q + 3524*p^2 + 4*p*q^2 + 849*p*q + 30308*p + 36*q^2 + 3661*q + 86558 := by dsimp [p,q]; ring
  rw [he]
  positivity

-- Independent certificate 10: high_u1_old1upper.
private theorem cert10 (x t : ℤ) (hx : 8≤x) (ht : 8*x≤t) :
    0 < 15*t*x^2 - t*x - t + 4*x^2 + 4*x + 2 := by
  let p := x-8
  let q := t-8*x
  have hp : 0≤p := by dsimp [p]; omega
  have hq : 0≤q := by dsimp [q]; omega
  have he : 15*t*x^2 - t*x - t + 4*x^2 + 4*x + 2 =
      120*p^3 + 15*p^2*q + 2876*p^2 + 239*p*q + 22972*p + 951*q + 61154 := by dsimp [p,q]; ring
  rw [he]
  positivity

-- Independent certificate 11: high_u1_old2.
private theorem cert11 (x t : ℤ) (hx : 8≤x) (ht : 8*x≤t) :
    0 < 4*t^2*x - 4*t^2 - 15*t*x^2 + 9*t*x - 3*t - 4*x^2 - 2*x - 2 := by
  let p := x-8
  let q := t-8*x
  have hp : 0≤p := by dsimp [p]; omega
  have hq : 0≤q := by dsimp [q]; omega
  have he : 4*t^2*x - 4*t^2 - 15*t*x^2 + 9*t*x - 3*t - 4*x^2 - 2*x - 2 =
      136*p^3 + 49*p^2*q + 3076*p^2 + 4*p*q^2 + 729*p*q + 23078*p + 28*q^2 + 2693*q + 57390 := by dsimp [p,q]; ring
  rw [he]
  positivity

-- Independent certificate 12: high_u1_old2upper.
private theorem cert12 (x t : ℤ) (hx : 8≤x) (ht : 8*x≤t) :
    0 < 4*t^2 + 15*t*x^2 - 5*t*x + 3*t + 4*x^2 + 3*x + 2 := by
  let p := x-8
  let q := t-8*x
  have hp : 0≤p := by dsimp [p]; omega
  have hq : 0≤q := by dsimp [q]; omega
  have he : 4*t^2 + 15*t*x^2 - 5*t*x + 3*t + 4*x^2 + 3*x + 2 =
      120*p^3 + 15*p^2*q + 3100*p^2 + 299*p*q + 26587*p + 4*q^2 + 1435*q + 75738 := by dsimp [p,q]; ring
  rw [he]
  positivity

-- Independent certificate 13: high_u1_new1.
private theorem cert13 (x t : ℤ) (hx : 8≤x) (ht : 8*x≤t) :
    0 < 8*t^2*x + 8*t^2 - 30*t*x^2 + 2*t*x + 6*t - 8*x^2 - 8*x - 6 := by
  let p := x-8
  let q := t-8*x
  have hp : 0≤p := by dsimp [p]; omega
  have hq : 0≤q := by dsimp [q]; omega
  have he : 8*t^2*x + 8*t^2 - 30*t*x^2 + 2*t*x + 6*t - 8*x^2 - 8*x - 6 =
      272*p^3 + 98*p^2*q + 7048*p^2 + 8*p*q^2 + 1698*p*q + 60584*p + 72*q^2 + 7318*q + 172858 := by dsimp [p,q]; ring
  rw [he]
  positivity

-- Independent certificate 14: high_u1_new1upper.
private theorem cert14 (x t : ℤ) (hx : 8≤x) (ht : 8*x≤t) :
    0 < 30*t*x^2 - 2*t*x - 2*t + 8*x^2 + 8*x + 6 := by
  let p := x-8
  let q := t-8*x
  have hp : 0≤p := by dsimp [p]; omega
  have hq : 0≤q := by dsimp [q]; omega
  have he : 30*t*x^2 - 2*t*x - 2*t + 8*x^2 + 8*x + 6 =
      240*p^3 + 30*p^2*q + 5752*p^2 + 478*p*q + 45944*p + 1902*q + 122310 := by dsimp [p,q]; ring
  rw [he]
  positivity

-- Independent certificate 15: high_u1_new2.
private theorem cert15 (x t : ℤ) (hx : 8≤x) (ht : 8*x≤t) :
    0 < 8*t^2*x - 8*t^2 - 30*t*x^2 + 10*t*x - 2*t - 8*x^2 - 6*x - 6 := by
  let p := x-8
  let q := t-8*x
  have hp : 0≤p := by dsimp [p]; omega
  have hq : 0≤q := by dsimp [q]; omega
  have he : 8*t^2*x - 8*t^2 - 30*t*x^2 + 10*t*x - 2*t - 8*x^2 - 6*x - 6 =
      272*p^3 + 98*p^2*q + 6088*p^2 + 8*p*q^2 + 1450*p*q + 45162*p + 56*q^2 + 5326*q + 110922 := by dsimp [p,q]; ring
  rw [he]
  positivity

-- Independent certificate 16: high_u1_new2upper.
private theorem cert16 (x t : ℤ) (hx : 8≤x) (ht : 8*x≤t) :
    0 < 8*t^2 + 30*t*x^2 - 6*t*x + 2*t + 8*x^2 + 7*x + 6 := by
  let p := x-8
  let q := t-8*x
  have hp : 0≤p := by dsimp [p]; omega
  have hq : 0≤q := by dsimp [q]; omega
  have he : 8*t^2 + 30*t*x^2 - 6*t*x + 2*t + 8*x^2 + 7*x + 6 =
      240*p^3 + 30*p^2*q + 6232*p^2 + 602*p*q + 53655*p + 8*q^2 + 2898*q + 153278 := by dsimp [p,q]; ring
  rw [he]
  positivity

-- Independent certificate 17: high_E>z.
private theorem cert17 (x t : ℤ) (hx : 8≤x) (ht : 8*x≤t) :
    0 < 4*t*x - x^2 - x + 3 := by
  let p := x-8
  let q := t-8*x
  have hp : 0≤p := by dsimp [p]; omega
  have hq : 0≤q := by dsimp [q]; omega
  have he : 4*t*x - x^2 - x + 3 =
      31*p^2 + 4*p*q + 495*p + 32*q + 1979 := by dsimp [p,q]; ring
  rw [he]
  positivity

-- Independent certificate 18: high_A>4E+z.
private theorem cert18 (x t : ℤ) (hx : 8≤x) (ht : 8*x≤t) :
    0 < 4*t*x^2 - 16*t*x - 20*t + 5*x^2 + 5*x - 11 := by
  let p := x-8
  let q := t-8*x
  have hp : 0≤p := by dsimp [p]; omega
  have hq : 0≤q := by dsimp [q]; omega
  have he : 4*t*x^2 - 16*t*x - 20*t + 5*x^2 + 5*x - 11 =
      32*p^3 + 4*p^2*q + 645*p^2 + 48*p*q + 4021*p + 108*q + 7261 := by dsimp [p,q]; ring
  rw [he]
  positivity

-- Independent certificate 19: high_zB>xL.
private theorem cert19 (x t : ℤ) (hx : 8≤x) (ht : 8*x≤t) :
    0 < 4*t^2 - 4*t*x + 4*t - x := by
  let p := x-8
  let q := t-8*x
  have hp : 0≤p := by dsimp [p]; omega
  have hq : 0≤q := by dsimp [q]; omega
  have he : 4*t^2 - 4*t*x + 4*t - x =
      224*p^2 + 60*p*q + 3615*p + 4*q^2 + 484*q + 14584 := by dsimp [p,q]; ring
  rw [he]
  positivity

-- Independent certificate 20: high_L>B.
private theorem cert20 (x t : ℤ) (hx : 8≤x) (ht : 8*x≤t) :
    0 < 4*t^2*x + 4*t^2 - t*x^2 - t*x + 3*t := by
  let p := x-8
  let q := t-8*x
  have hp : 0≤p := by dsimp [p]; omega
  have hq : 0≤q := by dsimp [q]; omega
  have he : 4*t^2*x + 4*t^2 - t*x^2 - t*x + 3*t =
      248*p^3 + 63*p^2*q + 6200*p^2 + 4*p*q^2 + 1071*p*q + 51608*p + 36*q^2 + 4539*q + 143040 := by dsimp [p,q]; ring
  rw [he]
  positivity

-- Independent certificate 21: high_A>2B.
private theorem cert21 (x t : ℤ) (hx : 8≤x) (ht : 8*x≤t) :
    0 < 2*t*x^2 - 2*t*x - 2*t + x^2 + x - 1 := by
  let p := x-8
  let q := t-8*x
  have hp : 0≤p := by dsimp [p]; omega
  have hq : 0≤q := by dsimp [q]; omega
  have he : 2*t*x^2 - 2*t*x - 2*t + x^2 + x - 1 =
      16*p^3 + 2*p^2*q + 369*p^2 + 30*p*q + 2817*p + 110*q + 7111 := by dsimp [p,q]; ring
  rw [he]
  positivity

-- Independent certificate 22: boundary_old1.
private theorem cert22 (x : ℤ) (hx : 8≤x) :
    0 < 4*(4*x)^2*x + 4*(4*x)^2 - 7*(4*x)*x^2 + (4*x)*x + 5*(4*x) - 2*x^2 - 2*x := by
  let p := x-8
  have hp : 0≤p := by dsimp [p]; omega
  have he : 4*(4*x)^2*x + 4*(4*x)^2 - 7*(4*x)*x^2 + (4*x)*x + 5*(4*x) - 2*x^2 - 2*x =
      36*p^3 + 930*p^2 + 7986*p + 22800 := by dsimp [p]; ring
  rw [he]
  positivity

-- Independent certificate 23: boundary_old1upper.
private theorem cert23 (x : ℤ) (hx : 8≤x) :
    0 < 7*(4*x)*x^2 - (4*x)*x - (4*x) + 2*x^2 + 2*x := by
  let p := x-8
  have hp : 0≤p := by dsimp [p]; omega
  have he : 7*(4*x)*x^2 - (4*x)*x - (4*x) + 2*x^2 + 2*x =
      28*p^3 + 670*p^2 + 5342*p + 14192 := by dsimp [p]; ring
  rw [he]
  positivity

-- Independent certificate 24: boundary_old2.
private theorem cert24 (x : ℤ) (hx : 8≤x) :
    0 < 4*(4*x)^2*x - 4*(4*x)^2 - 7*(4*x)*x^2 + 9*(4*x)*x - 3*(4*x) - 2*x^2 := by
  let p := x-8
  have hp : 0≤p := by dsimp [p]; omega
  have he : 4*(4*x)^2*x - 4*(4*x)^2 - 7*(4*x)*x^2 + 9*(4*x)*x - 3*(4*x) - 2*x^2 =
      36*p^3 + 834*p^2 + 6420*p + 16416 := by dsimp [p]; ring
  rw [he]
  positivity

-- Independent certificate 25: boundary_old2upper.
private theorem cert25 (x : ℤ) (hx : 8≤x) :
    0 < 4*(4*x)^2 + 7*(4*x)*x^2 - 5*(4*x)*x + 3*(4*x) + 2*x^2 + x := by
  let p := x-8
  have hp : 0≤p := by dsimp [p]; omega
  have he : 4*(4*x)^2 + 7*(4*x)*x^2 - 5*(4*x)*x + 3*(4*x) + 2*x^2 + x =
      28*p^3 + 718*p^2 + 6125*p + 17384 := by dsimp [p]; ring
  rw [he]
  positivity

-- Independent certificate 26: boundary_new1.
private theorem cert26 (x : ℤ) (hx : 8≤x) :
    0 < 8*(4*x)^2*x + 8*(4*x)^2 - 14*(4*x)*x^2 + 2*(4*x)*x + 6*(4*x) - 4*x^2 - 4*x - 2 := by
  let p := x-8
  have hp : 0≤p := by dsimp [p]; omega
  have he : 8*(4*x)^2*x + 8*(4*x)^2 - 14*(4*x)*x^2 + 2*(4*x)*x + 6*(4*x) - 4*x^2 - 4*x - 2 =
      72*p^3 + 1860*p^2 + 15956*p + 45470 := by dsimp [p]; ring
  rw [he]
  positivity

-- Independent certificate 27: boundary_new1upper.
private theorem cert27 (x : ℤ) (hx : 8≤x) :
    0 < 14*(4*x)*x^2 - 2*(4*x)*x - 2*(4*x) + 4*x^2 + 4*x + 2 := by
  let p := x-8
  have hp : 0≤p := by dsimp [p]; omega
  have he : 14*(4*x)*x^2 - 2*(4*x)*x - 2*(4*x) + 4*x^2 + 4*x + 2 =
      56*p^3 + 1340*p^2 + 10684*p + 28386 := by dsimp [p]; ring
  rw [he]
  positivity

-- Independent certificate 28: boundary_new2.
private theorem cert28 (x : ℤ) (hx : 8≤x) :
    0 < 8*(4*x)^2*x - 8*(4*x)^2 - 14*(4*x)*x^2 + 10*(4*x)*x - 2*(4*x) - 4*x^2 - 2*x - 2 := by
  let p := x-8
  have hp : 0≤p := by dsimp [p]; omega
  have he : 8*(4*x)^2*x - 8*(4*x)^2 - 14*(4*x)*x^2 + 10*(4*x)*x - 2*(4*x) - 4*x^2 - 2*x - 2 =
      72*p^3 + 1636*p^2 + 12342*p + 30894 := by dsimp [p]; ring
  rw [he]
  positivity

-- Independent certificate 29: boundary_new2upper.
private theorem cert29 (x : ℤ) (hx : 8≤x) :
    0 < 8*(4*x)^2 + 14*(4*x)*x^2 - 6*(4*x)*x + 2*(4*x) + 4*x^2 + 3*x + 2 := by
  let p := x-8
  have hp : 0≤p := by dsimp [p]; omega
  have he : 8*(4*x)^2 + 14*(4*x)*x^2 - 6*(4*x)*x + 2*(4*x) + 4*x^2 + 3*x + 2 =
      56*p^3 + 1452*p^2 + 12491*p + 35674 := by dsimp [p]; ring
  rw [he]
  positivity

-- Independent certificate 30: boundary_old3.
private theorem cert30 (x : ℤ) (hx : 8≤x) :
    0 < -4*(4*x)^2*x - 4*(4*x)^2 + 17*(4*x)*x^2 + 17*(4*x)*x + 13*(4*x) + 16 := by
  let p := x-8
  have hp : 0≤p := by dsimp [p]; omega
  have he : -4*(4*x)^2*x - 4*(4*x)^2 + 17*(4*x)*x^2 + 17*(4*x)*x + 13*(4*x) + 16 =
      4*p^3 + 100*p^2 + 884*p + 2736 := by dsimp [p]; ring
  rw [he]
  positivity

-- Independent certificate 31: boundary_old3upper.
private theorem cert31 (x : ℤ) (hx : 8≤x) :
    0 < 4*(4*x)^2*x + 4*(4*x)^2 - 13*(4*x)*x^2 - 17*(4*x)*x - 13*(4*x) + x^2 + x - 16 := by
  let p := x-8
  have hp : 0≤p := by dsimp [p]; omega
  have he : 4*(4*x)^2*x + 4*(4*x)^2 - 13*(4*x)*x^2 - 17*(4*x)*x - 13*(4*x) + x^2 + x - 16 =
      12*p^3 + 285*p^2 + 2205*p + 5528 := by dsimp [p]; ring
  rw [he]
  positivity

-- Independent certificate 32: boundary_new3.
private theorem cert32 (x : ℤ) (hx : 8≤x) :
    0 < -8*(4*x)^2*x - 8*(4*x)^2 + 34*(4*x)*x^2 + 34*(4*x)*x + 30*(4*x) + 16 := by
  let p := x-8
  have hp : 0≤p := by dsimp [p]; omega
  have he : -8*(4*x)^2*x - 8*(4*x)^2 + 34*(4*x)*x^2 + 34*(4*x)*x + 30*(4*x) + 16 =
      8*p^3 + 200*p^2 + 1784*p + 5584 := by dsimp [p]; ring
  rw [he]
  positivity

-- Independent certificate 33: boundary_new3upper.
private theorem cert33 (x : ℤ) (hx : 8≤x) :
    0 < 8*(4*x)^2*x + 8*(4*x)^2 - 30*(4*x)*x^2 - 34*(4*x)*x - 30*(4*x) + x^2 + x - 16 := by
  let p := x-8
  have hp : 0≤p := by dsimp [p]; omega
  have he : 8*(4*x)^2*x + 8*(4*x)^2 - 30*(4*x)*x^2 - 34*(4*x)*x - 30*(4*x) + x^2 + x - 16 =
      8*p^3 + 185*p^2 + 1305*p + 2680 := by dsimp [p]; ring
  rw [he]
  positivity

-- Independent certificate 34: boundary_v>0.
private theorem cert34 (x : ℤ) (hx : 8≤x) :
    0 < 8 := by norm_num

-- Independent certificate 35: boundary_stockupper.
private theorem cert35 (x : ℤ) (hx : 8≤x) :
    0 < 2*(4*x) - 9 := by
  let p := x-8
  have hp : 0≤p := by dsimp [p]; omega
  have he : 2*(4*x) - 9 =
      8*p + 55 := by dsimp [p]; ring
  rw [he]
  positivity

-- Independent certificate 36: small_old1.
private theorem cert36 (t : ℤ) (ht : 128≤t) :
    0 < 4*t^2*(4:ℤ) + 4*t^2 - 55*t*(4:ℤ)^2 + t*(4:ℤ) + 5*t - 14*(4:ℤ)^2 - 14*(4:ℤ) - 12 := by
  let p := t-128
  have hp : 0≤p := by dsimp [p]; omega
  have he : 4*t^2*(4:ℤ) + 4*t^2 - 55*t*(4:ℤ)^2 + t*(4:ℤ) + 5*t - 14*(4:ℤ)^2 - 14*(4:ℤ) - 12 =
      20*p^2 + 4249*p + 215900 := by dsimp [p]; ring
  rw [he]
  positivity

-- Independent certificate 37: small_old1upper.
private theorem cert37 (t : ℤ) (ht : 128≤t) :
    0 < 7*t*(4:ℤ)^2 - t*(4:ℤ) - t + 2*(4:ℤ)^2 + 2*(4:ℤ) := by
  let p := t-128
  have hp : 0≤p := by dsimp [p]; omega
  have he : 7*t*(4:ℤ)^2 - t*(4:ℤ) - t + 2*(4:ℤ)^2 + 2*(4:ℤ) =
      107*p + 13736 := by dsimp [p]; ring
  rw [he]
  positivity

-- Independent certificate 38: small_old2.
private theorem cert38 (t : ℤ) (ht : 128≤t) :
    0 < 4*t^2*(4:ℤ) - 4*t^2 - 55*t*(4:ℤ)^2 + 9*t*(4:ℤ) - 3*t - 14*(4:ℤ)^2 - 12*(4:ℤ) - 12 := by
  let p := t-128
  have hp : 0≤p := by dsimp [p]; omega
  have he : 4*t^2*(4:ℤ) - 4*t^2 - 55*t*(4:ℤ)^2 + 9*t*(4:ℤ) - 3*t - 14*(4:ℤ)^2 - 12*(4:ℤ) - 12 =
      12*p^2 + 2225*p + 87908 := by dsimp [p]; ring
  rw [he]
  positivity

-- Independent certificate 39: small_old2upper.
private theorem cert39 (t : ℤ) (ht : 128≤t) :
    0 < 4*t^2 + 7*t*(4:ℤ)^2 - 5*t*(4:ℤ) + 3*t + 2*(4:ℤ)^2 + (4:ℤ) := by
  let p := t-128
  have hp : 0≤p := by dsimp [p]; omega
  have he : 4*t^2 + 7*t*(4:ℤ)^2 - 5*t*(4:ℤ) + 3*t + 2*(4:ℤ)^2 + (4:ℤ) =
      4*p^2 + 1119*p + 77732 := by dsimp [p]; ring
  rw [he]
  positivity

-- Independent certificate 40: small_new1.
private theorem cert40 (t : ℤ) (ht : 128≤t) :
    0 < 8*t^2*(4:ℤ) + 8*t^2 - 110*t*(4:ℤ)^2 + 2*t*(4:ℤ) + 6*t - 28*(4:ℤ)^2 - 28*(4:ℤ) - 26 := by
  let p := t-128
  have hp : 0≤p := by dsimp [p]; omega
  have he : 8*t^2*(4:ℤ) + 8*t^2 - 110*t*(4:ℤ)^2 + 2*t*(4:ℤ) + 6*t - 28*(4:ℤ)^2 - 28*(4:ℤ) - 26 =
      40*p^2 + 8494*p + 431286 := by dsimp [p]; ring
  rw [he]
  positivity

-- Independent certificate 41: small_new1upper.
private theorem cert41 (t : ℤ) (ht : 128≤t) :
    0 < 14*t*(4:ℤ)^2 - 2*t*(4:ℤ) - 2*t + 4*(4:ℤ)^2 + 4*(4:ℤ) + 2 := by
  let p := t-128
  have hp : 0≤p := by dsimp [p]; omega
  have he : 14*t*(4:ℤ)^2 - 2*t*(4:ℤ) - 2*t + 4*(4:ℤ)^2 + 4*(4:ℤ) + 2 =
      214*p + 27474 := by dsimp [p]; ring
  rw [he]
  positivity

-- Independent certificate 42: small_new2.
private theorem cert42 (t : ℤ) (ht : 128≤t) :
    0 < 8*t^2*(4:ℤ) - 8*t^2 - 110*t*(4:ℤ)^2 + 10*t*(4:ℤ) - 2*t - 28*(4:ℤ)^2 - 26*(4:ℤ) - 26 := by
  let p := t-128
  have hp : 0≤p := by dsimp [p]; omega
  have he : 8*t^2*(4:ℤ) - 8*t^2 - 110*t*(4:ℤ)^2 + 10*t*(4:ℤ) - 2*t - 28*(4:ℤ)^2 - 26*(4:ℤ) - 26 =
      24*p^2 + 4422*p + 172222 := by dsimp [p]; ring
  rw [he]
  positivity

-- Independent certificate 43: small_new2upper.
private theorem cert43 (t : ℤ) (ht : 128≤t) :
    0 < 8*t^2 + 14*t*(4:ℤ)^2 - 6*t*(4:ℤ) + 2*t + 4*(4:ℤ)^2 + 3*(4:ℤ) + 2 := by
  let p := t-128
  have hp : 0≤p := by dsimp [p]; omega
  have he : 8*t^2 + 14*t*(4:ℤ)^2 - 6*t*(4:ℤ) + 2*t + 4*(4:ℤ)^2 + 3*(4:ℤ) + 2 =
      8*p^2 + 2250*p + 157006 := by dsimp [p]; ring
  rw [he]
  positivity

-- Independent certificate 44: small_zB>4L.
private theorem cert44 (t : ℤ) (ht : 128≤t) :
    0 < 4*t^2*(4:ℤ)^2 - 12*t^2*(4:ℤ) - 12*t^2 - 12*t - 4 := by
  let p := t-128
  have hp : 0≤p := by dsimp [p]; omega
  have he : 4*t^2*(4:ℤ)^2 - 12*t^2*(4:ℤ) - 12*t^2 - 12*t - 4 =
      4*p^2 + 1012*p + 63996 := by dsimp [p]; ring
  rw [he]
  positivity

-- Independent certificate 45: small_A>2B.
private theorem cert45 (t : ℤ) (ht : 128≤t) :
    0 < 2*t*(4:ℤ)^2 - 2*t*(4:ℤ) - 2*t + (4:ℤ)^2 + (4:ℤ) - 1 := by
  let p := t-128
  have hp : 0≤p := by dsimp [p]; omega
  have he : 2*t*(4:ℤ)^2 - 2*t*(4:ℤ) - 2*t + (4:ℤ)^2 + (4:ℤ) - 1 =
      22*p + 2835 := by dsimp [p]; ring
  rw [he]
  positivity

private theorem high_firstTwo (x t : ℤ) (hx : 8≤x) (ht : 8*x≤t) :
    firstTwo x t 0 ∧ firstTwo x t 1 := by
  have h1 := cert01 x t hx ht
  have h2 := cert02 x t hx ht
  have h3 := cert03 x t hx ht
  have h4 := cert04 x t hx ht
  have h5 := cert05 x t hx ht
  have h6 := cert06 x t hx ht
  have h7 := cert07 x t hx ht
  have h8 := cert08 x t hx ht
  have h9 := cert09 x t hx ht
  have h10 := cert10 x t hx ht
  have h11 := cert11 x t hx ht
  have h12 := cert12 x t hx ht
  have h13 := cert13 x t hx ht
  have h14 := cert14 x t hx ht
  have h15 := cert15 x t hx ht
  have h16 := cert16 x t hx ht
  dsimp [firstTwo,window,H1,H2,J1,J2,SU,SV,SW,A,B,L,K]
  refine ⟨⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩,
    ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩⟩
  all_goals nlinarith only [h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16]

private theorem high_aux (x t : ℤ) (hx : 8≤x) (ht : 8*x≤t) :
    4*t<E x t ∧ 4*E x t+4*t<A x t ∧
    x*L x t<4*t*B x t ∧ B x t<L x t ∧ 2*B x t<A x t := by
  have h17 := cert17 x t hx ht
  have h18 := cert18 x t hx ht
  have h19 := cert19 x t hx ht
  have h20 := cert20 x t hx ht
  have h21 := cert21 x t hx ht
  dsimp [E,A,B,L]
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals nlinarith only [h17,h18,h19,h20,h21]

private theorem boundary_windows (x : ℤ) (hx : 8≤x) :
    windows x (4*x) 0 8 := by
  have h22 := cert22 x hx
  have h23 := cert23 x hx
  have h24 := cert24 x hx
  have h25 := cert25 x hx
  have h26 := cert26 x hx
  have h27 := cert27 x hx
  have h28 := cert28 x hx
  have h29 := cert29 x hx
  have h30 := cert30 x hx
  have h31 := cert31 x hx
  have h32 := cert32 x hx
  have h33 := cert33 x hx
  dsimp [windows,firstTwo,window,H1,H2,J1,J2,D,T,SU,SV,SW,A,B,L,K]
  refine ⟨⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩
  all_goals nlinarith only [h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33]

private theorem boundary_stock (x : ℤ) (hx : 8≤x) : 0≤(8:ℤ) ∧ 8<2*(4*x)-1 := by
  have h := cert35 x hx
  constructor <;> linarith

private theorem small_firstTwo (t u : ℤ) (ht : 128≤t) (hu : 0≤u) (hu6 : u≤6) :
    firstTwo 4 t u := by
  have h36 := cert36 t ht
  have h37 := cert37 t ht
  have h38 := cert38 t ht
  have h39 := cert39 t ht
  have h40 := cert40 t ht
  have h41 := cert41 t ht
  have h42 := cert42 t ht
  have h43 := cert43 t ht
  have ht0 : 0≤t := by omega
  have hA : 0≤A 4 t := by dsimp [A]; positivity
  have hlow := mul_le_mul_of_nonneg_right hu6 hA
  have hupp := mul_nonneg hu hA
  dsimp [A] at hlow hupp
  dsimp [firstTwo,window,H1,H2,J1,J2,SU,SV,SW,A,B,L,K]
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩
  all_goals nlinarith only [hlow,hupp,h36,h37,h38,h39,h40,h41,h42,h43]

private theorem small_aux (t : ℤ) (ht : 128≤t) :
    4*L 4 t<4*t*B 4 t ∧ 2*B 4 t<A 4 t ∧ B 4 t<L 4 t := by
  have h44 := cert44 t ht
  have h45 := cert45 t ht
  have hp : 0<t := by omega
  have hp2 : 0≤t^2 := sq_nonneg t
  have hshift : 0≤t*(t-128) := mul_nonneg hp.le (by omega)
  dsimp [A,B,L]
  refine ⟨?_,?_,?_⟩
  · nlinarith only [h44]
  · nlinarith only [h45]
  · nlinarith only [ht,hp2,hshift]

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo
