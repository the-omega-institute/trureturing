/- GID: D5/S3/Zeros/Convolution/GribinskiDegreeThreeDiscriminant
   generality: G
   mirror-B: D5/B/S3/Zeros/Convolution/GribinskiDegreeThreeDiscriminant
   mirror-E: none(waiver:symbolic-real-parameter-proof)
   anchors: []
   utility: none
   digest: A sum-of-squares discriminant certificate for ordered nonnegative cubic roots. -/

import Mathlib.Tactic

/-!
The discriminant numerator is cubic in t = alpha + 1. Each coefficient is
checked separately against its exact nonnegative decomposition. The four
remainders contain 767 positive monomials in total; the other 20 terms are
nonnegative monomial multiples of squares. No input domain is enumerated.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Zeros.Convolution.GribinskiDegreeThreeDiscriminant

/-- Denominator-cleared discriminant for affine T and U, with denominator 6+3*t. -/
def numerator (t s a b c d : Real) : Real :=
  s^2 * (a+b*t)^2 * (6+3*t) - 4*(a+b*t)^3 -
    4*s^3*(c+d*t)*(6+3*t)^2 - 27*(c+d*t)^2*(6+3*t) +
    18*s*(a+b*t)*(c+d*t)*(6+3*t)

private def coeff0 (s a _b c _d : Real) : Real :=
  (((-162) * (c ^ 2)) + ((-4) * (a ^ 3)) + ((-144) * c * (s ^ 3)) + (6 * (a ^ 2) * (s ^ 2)) +
  (108 * a * c * s))

private def coeff1 (s a b c d : Real) : Real :=
  (((-81) * (c ^ 2)) + ((-324) * c * d) + ((-144) * c * (s ^ 3)) + ((-144) * d * (s ^ 3)) +
  ((-12) * b * (a ^ 2)) + (3 * (a ^ 2) * (s ^ 2)) + (12 * a * b * (s ^ 2)) + (54 * a * c * s) +
  (108 * a * d * s) + (108 * b * c * s))

private def coeff2 (s a b c d : Real) : Real :=
  (((-162) * (d ^ 2)) + ((-162) * c * d) + ((-144) * d * (s ^ 3)) + ((-36) * c * (s ^ 3)) +
  ((-12) * a * (b ^ 2)) + (6 * (b ^ 2) * (s ^ 2)) + (6 * a * b * (s ^ 2)) + (54 * a * d * s) +
  (54 * b * c * s) + (108 * b * d * s))

private def coeff3 (s _a b _c d : Real) : Real :=
  (((-81) * (d ^ 2)) + ((-4) * (b ^ 3)) + ((-36) * d * (s ^ 3)) + (3 * (b ^ 2) * (s ^ 2)) + (54
  * b * d * s))

private theorem numerator_expansion (t s a b c d : Real) :
    numerator t s a b c d = coeff0 s a b c d + coeff1 s a b c d * t +
      coeff2 s a b c d * t^2 + coeff3 s a b c d * t^3 := by
  unfold numerator coeff0 coeff1 coeff2 coeff3
  ring

private def sumRoots (x u v : Real) : Real := x + (x+u) + (x+u+v)
private def pairRoots (x u v : Real) : Real :=
  x*(x+u) + x*(x+u+v) + (x+u)*(x+u+v)
private def prodRoots (x u v : Real) : Real := x*(x+u)*(x+u+v)

private def sos0 (x u v y w z : Real) : Real :=
  ((u * ((u * ((96 * (z ^ 4)) + (u * ((416 * (z ^ 3)) + (u * ((600 * (z ^ 2)) + (u * ((288 * z)
  + (576 * w) + (864 * y))) + (v * ((216 * v) + (720 * z) + (1440 * w) + (2160 * y))) + (w *
  ((1536 * w) + (1536 * z))) + (y * ((1872 * z) + (2808 * y) + (3744 * w))))) + (v * ((1200 * (z
  ^ 2)) + (v * ((432 * v) + (864 * z) + (1728 * w) + (2592 * y))) + (w * ((3072 * w) + (3072 *
  z))) + (y * ((3744 * z) + (5616 * y) + (7488 * w))))) + (w * ((1920 * (z ^ 2)) + (w * ((2176 *
  w) + (3264 * z))))) + (y * ((2592 * (z ^ 2)) + (w * ((9504 * w) + (9504 * z))) + (y * ((6912 *
  y) + (6912 * z) + (13824 * w))))))) + (v * ((624 * (z ^ 3)) + (v * ((792 * (z ^ 2)) + (v *
  ((216 * v) + (576 * z) + (1152 * w) + (1728 * y))) + (w * ((2736 * w) + (2736 * z))) + (y *
  ((3888 * z) + (5832 * y) + (7776 * w))))) + (w * ((2880 * (z ^ 2)) + (w * ((3264 * w) + (4896
  * z))))) + (y * ((3888 * (z ^ 2)) + (w * ((14256 * w) + (14256 * z))) + (y * ((10368 * y) +
  (10368 * z) + (20736 * w))))))) + (w * ((1200 * (z ^ 3)) + (w * ((2736 * (z ^ 2)) + (w *
  ((1536 * w) + (3072 * z))))))) + (y * ((2016 * (z ^ 3)) + (w * ((6480 * (z ^ 2)) + (w * ((4896
  * w) + (7344 * z))))) + (y * ((3456 * (z ^ 2)) + (w * ((3456 * w) + (3456 * z))))))))) + (v *
  ((96 * (z ^ 4)) + (v * ((240 * (z ^ 3)) + (v * ((192 * (z ^ 2)) + (v * ((144 * z) + (288 * w)
  + (432 * y))) + (w * ((1200 * w) + (1200 * z))) + (y * ((2016 * z) + (3024 * y) + (4032 *
  w))))) + (w * ((1440 * (z ^ 2)) + (w * ((1920 * w) + (2880 * z))))) + (y * ((2160 * (z ^ 2)) +
  (w * ((7344 * w) + (7344 * z))) + (y * ((5184 * y) + (5184 * z) + (10368 * w))))))) + (w *
  ((1200 * (z ^ 3)) + (w * ((2736 * (z ^ 2)) + (w * ((1536 * w) + (3072 * z))))))) + (y * ((2016
  * (z ^ 3)) + (w * ((6480 * (z ^ 2)) + (w * ((4896 * w) + (7344 * z))))) + (y * ((3456 * (z ^
  2)) + (w * ((3456 * w) + (3456 * z))))))))) + (w * ((288 * (z ^ 4)) + (w * ((1152 * (z ^ 3)) +
  (w * ((1728 * (z ^ 2)) + (w * ((576 * w) + (1440 * z))))))))) + (y * ((576 * (z ^ 4)) + (w *
  ((1152 * (z ^ 3)) + (w * ((1728 * (z ^ 2)) + (w * ((576 * w) + (1152 * z))))))))))) + (v * ((v
  * ((24 * (z ^ 4)) + (v * ((16 * (z ^ 3)) + (v * ((24 * (z ^ 2)) + (w * ((96 * w) + (96 * z)))
  + (y * ((144 * z) + (216 * y) + (288 * w))))) + (w * ((240 * (z ^ 2)) + (w * ((416 * w) + (624
  * z))))) + (y * ((432 * (z ^ 2)) + (w * ((1296 * w) + (1296 * z))) + (y * ((864 * y) + (864 *
  z) + (1728 * w))))))) + (w * ((192 * (z ^ 3)) + (w * ((792 * (z ^ 2)) + (w * ((600 * w) +
  (1200 * z))))))) + (y * ((288 * (z ^ 3)) + (w * ((1296 * (z ^ 2)) + (w * ((1440 * w) + (2160 *
  z))))) + (y * ((864 * (z ^ 2)) + (w * ((864 * w) + (864 * z))))))))) + (w * ((144 * (z ^ 4)) +
  (w * ((576 * (z ^ 3)) + (w * ((864 * (z ^ 2)) + (w * ((288 * w) + (720 * z))))))))) + (y *
  ((288 * (z ^ 4)) + (w * ((576 * (z ^ 3)) + (w * ((864 * (z ^ 2)) + (w * ((288 * w) + (576 *
  z))))))))))) + (x * ((u * ((288 * (z ^ 4)) + (u * ((1296 * (z ^ 3)) + (u * ((1440 * (z ^ 2)) +
  (u * ((288 * z) + (576 * w) + (864 * y))) + (v * ((576 * z) + (1152 * w) + (1728 * y))) + (w *
  ((4896 * w) + (4896 * z))) + (y * ((6912 * z) + (10368 * y) + (13824 * w))))) + (v * ((2160 *
  (z ^ 2)) + (v * ((864 * z) + (1728 * w) + (2592 * y))) + (w * ((7344 * w) + (7344 * z))) + (y
  * ((10368 * z) + (15552 * y) + (20736 * w))))) + (w * ((7344 * (z ^ 2)) + (w * ((9504 * w) +
  (14256 * z))))) + (y * ((10800 * (z ^ 2)) + (w * ((41904 * w) + (41904 * z))) + (y * ((31104 *
  y) + (31104 * z) + (62208 * w))))))) + (v * ((1296 * (z ^ 3)) + (v * ((1296 * (z ^ 2)) + (v *
  ((576 * z) + (1152 * w) + (1728 * y))) + (w * ((6480 * w) + (6480 * z))) + (y * ((10368 * z) +
  (15552 * y) + (20736 * w))))) + (w * ((7344 * (z ^ 2)) + (w * ((9504 * w) + (14256 * z))))) +
  (y * ((10800 * (z ^ 2)) + (w * ((41904 * w) + (41904 * z))) + (y * ((31104 * y) + (31104 * z)
  + (62208 * w))))))) + (w * ((4032 * (z ^ 3)) + (w * ((7776 * (z ^ 2)) + (w * ((3744 * w) +
  (7488 * z))))))) + (y * ((6912 * (z ^ 3)) + (w * ((20736 * (z ^ 2)) + (w * ((13824 * w) +
  (20736 * z))))) + (y * ((10368 * (z ^ 2)) + (w * ((10368 * w) + (10368 * z))))))))) + (v *
  ((144 * (z ^ 4)) + (v * ((432 * (z ^ 3)) + (v * ((288 * (z ^ 2)) + (v * ((288 * z) + (576 * w)
  + (864 * y))) + (w * ((2016 * w) + (2016 * z))) + (y * ((3456 * z) + (5184 * y) + (6912 *
  w))))) + (w * ((2160 * (z ^ 2)) + (w * ((2592 * w) + (3888 * z))))) + (y * ((3024 * (z ^ 2)) +
  (w * ((10800 * w) + (10800 * z))) + (y * ((7776 * y) + (7776 * z) + (15552 * w))))))) + (w *
  ((2016 * (z ^ 3)) + (w * ((3888 * (z ^ 2)) + (w * ((1872 * w) + (3744 * z))))))) + (y * ((3456
  * (z ^ 3)) + (w * ((10368 * (z ^ 2)) + (w * ((6912 * w) + (10368 * z))))) + (y * ((5184 * (z ^
  2)) + (w * ((5184 * w) + (5184 * z))))))))) + (w * ((432 * (z ^ 4)) + (w * ((1728 * (z ^ 3)) +
  (w * ((2592 * (z ^ 2)) + (w * ((864 * w) + (2160 * z))))))))) + (x * ((216 * (z ^ 4)) + (u *
  ((1728 * (z ^ 3)) + (u * ((864 * (z ^ 2)) + (w * ((3456 * w) + (3456 * z))) + (y * ((5184 * z)
  + (7776 * y) + (10368 * w))))) + (v * ((864 * (z ^ 2)) + (w * ((3456 * w) + (3456 * z))) + (y
  * ((5184 * z) + (7776 * y) + (10368 * w))))) + (w * ((10368 * (z ^ 2)) + (w * ((13824 * w) +
  (20736 * z))))) + (y * ((15552 * (z ^ 2)) + (w * ((62208 * w) + (62208 * z))) + (y * ((46656 *
  y) + (46656 * z) + (93312 * w))))))) + (v * ((864 * (z ^ 3)) + (v * ((864 * (z ^ 2)) + (w *
  ((3456 * w) + (3456 * z))) + (y * ((5184 * z) + (7776 * y) + (10368 * w))))) + (w * ((5184 *
  (z ^ 2)) + (w * ((6912 * w) + (10368 * z))))) + (y * ((7776 * (z ^ 2)) + (w * ((31104 * w) +
  (31104 * z))) + (y * ((23328 * y) + (23328 * z) + (46656 * w))))))) + (w * ((3024 * (z ^ 3)) +
  (w * ((5832 * (z ^ 2)) + (w * ((2808 * w) + (5616 * z))))))) + (x * ((864 * (z ^ 3)) + (w *
  ((5184 * (z ^ 2)) + (w * ((6912 * w) + (10368 * z))))) + (y * ((7776 * (z ^ 2)) + (w * ((31104
  * w) + (31104 * z))) + (y * ((23328 * y) + (23328 * z) + (46656 * w))))))) + (y * ((5184 * (z
  ^ 3)) + (w * ((15552 * (z ^ 2)) + (w * ((10368 * w) + (15552 * z))))) + (y * ((7776 * (z ^ 2))
  + (w * ((7776 * w) + (7776 * z))))))))) + (y * ((864 * (z ^ 4)) + (w * ((1728 * (z ^ 3)) + (w
  * ((2592 * (z ^ 2)) + (w * ((864 * w) + (1728 * z))))))))))) + ((w ^ 2) * ((216 * (z ^ 4)) +
  (w * ((432 * (z ^ 3)) + (216 * w * (z ^ 2)))))))

private theorem sos0_nonneg (x u v y w z : Real)
    (hx : 0 <= x) (hu : 0 <= u) (hv : 0 <= v)
    (hy : 0 <= y) (hw : 0 <= w) (hz : 0 <= z) :
    0 <= sos0 x u v y w z := by
  unfold sos0
  positivity

private theorem coeff0_identity (x u v y w z : Real) :
    coeff0 (sumRoots x u v + sumRoots y w z)
      (6*(pairRoots x u v + pairRoots y w z) + 2*sumRoots x u v*sumRoots y w z)
      (3*(pairRoots x u v + pairRoots y w z) + 2*sumRoots x u v*sumRoots y w z)
      (6*(prodRoots x u v + prodRoots y w z))
      (3*(prodRoots x u v + prodRoots y w z) +
        sumRoots x u v*pairRoots y w z + pairRoots x u v*sumRoots y w z) = sos0 x u v y w z := by
  unfold coeff0 sumRoots pairRoots prodRoots sos0
  ring

private theorem ordered_coeff0_nonneg (x u v y w z : Real)
    (hx : 0 <= x) (hu : 0 <= u) (hv : 0 <= v)
    (hy : 0 <= y) (hw : 0 <= w) (hz : 0 <= z) :
    0 <= coeff0 (sumRoots x u v + sumRoots y w z)
      (6*(pairRoots x u v + pairRoots y w z) + 2*sumRoots x u v*sumRoots y w z)
      (3*(pairRoots x u v + pairRoots y w z) + 2*sumRoots x u v*sumRoots y w z)
      (6*(prodRoots x u v + prodRoots y w z))
      (3*(prodRoots x u v + prodRoots y w z) +
        sumRoots x u v*pairRoots y w z + pairRoots x u v*sumRoots y w z) := by
  rw [coeff0_identity]
  exact sos0_nonneg x u v y w z hx hu hv hy hw hz

private def sos1 (x u v y w z : Real) : Real :=
  ((u * ((u * ((96 * (z ^ 4)) + (u * ((336 * (z ^ 3)) + (u * ((492 * (z ^ 2)) + (u * ((288 * z)
  + (576 * w) + (864 * y))) + (v * ((324 * v) + (720 * z) + (1440 * w) + (2160 * y))) + (w *
  ((960 * w) + (960 * z))) + (y * ((936 * z) + (1404 * y) + (1872 * w))))) + (v * ((984 * (z ^
  2)) + (v * ((648 * v) + (864 * z) + (1728 * w) + (2592 * y))) + (w * ((1920 * w) + (1920 *
  z))) + (y * ((1872 * z) + (2808 * y) + (3744 * w))))) + (w * ((864 * (z ^ 2)) + (w * ((384 *
  w) + (576 * z))))) + (y * ((720 * (z ^ 2)) + (w * ((720 * w) + (720 * z))))))) + (v * ((504 *
  (z ^ 3)) + (v * ((612 * (z ^ 2)) + (v * ((324 * v) + (576 * z) + (1152 * w) + (1728 * y))) +
  (w * ((1584 * w) + (1584 * z))) + (y * ((1944 * z) + (2916 * y) + (3888 * w))))) + (w * ((1296
  * (z ^ 2)) + (w * ((576 * w) + (864 * z))))) + (y * ((1080 * (z ^ 2)) + (w * ((1080 * w) +
  (1080 * z))))))) + (w * ((624 * (z ^ 3)) + (w * ((1584 * (z ^ 2)) + (w * ((960 * w) + (1920 *
  z))))))) + (y * ((864 * (z ^ 3)) + (w * ((3024 * (z ^ 2)) + (w * ((2592 * w) + (3888 * z)))))
  + (y * ((1728 * (z ^ 2)) + (w * ((1728 * w) + (1728 * z))))))))) + (v * ((96 * (z ^ 4)) + (v *
  ((216 * (z ^ 3)) + (v * ((120 * (z ^ 2)) + (v * ((144 * z) + (288 * w) + (432 * y))) + (w *
  ((624 * w) + (624 * z))) + (y * ((1008 * z) + (1512 * y) + (2016 * w))))) + (w * ((864 * (z ^
  2)) + (w * ((864 * w) + (1296 * z))))) + (y * ((1080 * (z ^ 2)) + (w * ((1080 * w) + (1080 *
  z))))))) + (w * ((624 * (z ^ 3)) + (w * ((1584 * (z ^ 2)) + (w * ((960 * w) + (1920 * z)))))))
  + (y * ((864 * (z ^ 3)) + (w * ((3024 * (z ^ 2)) + (w * ((2592 * w) + (3888 * z))))) + (y *
  ((1728 * (z ^ 2)) + (w * ((1728 * w) + (1728 * z))))))))) + (w * ((288 * (z ^ 4)) + (w *
  ((1152 * (z ^ 3)) + (w * ((1728 * (z ^ 2)) + (w * ((576 * w) + (1440 * z))))))))) + (y * ((576
  * (z ^ 4)) + (w * ((1152 * (z ^ 3)) + (w * ((1728 * (z ^ 2)) + (w * ((576 * w) + (1152 *
  z))))))))))) + (v * ((v * ((60 * (z ^ 4)) + (v * ((24 * (z ^ 3)) + (v * ((60 * (z ^ 2)) + (w *
  ((96 * w) + (96 * z))) + (y * ((72 * z) + (108 * y) + (144 * w))))) + (w * ((216 * (z ^ 2)) +
  (w * ((336 * w) + (504 * z))))) + (y * ((360 * (z ^ 2)) + (w * ((360 * w) + (360 * z))))))) +
  (w * ((120 * (z ^ 3)) + (w * ((612 * (z ^ 2)) + (w * ((492 * w) + (984 * z))))))) + (y * ((w *
  ((432 * (z ^ 2)) + (w * ((864 * w) + (1296 * z))))) + (y * ((432 * (z ^ 2)) + (w * ((432 * w)
  + (432 * z))))))))) + (w * ((144 * (z ^ 4)) + (w * ((576 * (z ^ 3)) + (w * ((864 * (z ^ 2)) +
  (w * ((288 * w) + (720 * z))))))))) + (y * ((288 * (z ^ 4)) + (w * ((576 * (z ^ 3)) + (w *
  ((864 * (z ^ 2)) + (w * ((288 * w) + (576 * z))))))))))) + (x * ((u * ((144 * (z ^ 4)) + (u *
  ((360 * (z ^ 3)) + (u * ((864 * (z ^ 2)) + (u * ((288 * z) + (576 * w) + (864 * y))) + (v *
  ((576 * z) + (1152 * w) + (1728 * y))) + (w * ((2592 * w) + (2592 * z))) + (y * ((3456 * z) +
  (5184 * y) + (6912 * w))))) + (v * ((1296 * (z ^ 2)) + (v * ((864 * z) + (1728 * w) + (2592 *
  y))) + (w * ((3888 * w) + (3888 * z))) + (y * ((5184 * z) + (7776 * y) + (10368 * w))))) + (w
  * ((1080 * (z ^ 2)) + (w * ((720 * w) + (1080 * z))))) + (y * ((1080 * (z ^ 2)) + (w * ((1080
  * w) + (1080 * z))))))) + (v * ((360 * (z ^ 3)) + (v * ((432 * (z ^ 2)) + (v * ((576 * z) +
  (1152 * w) + (1728 * y))) + (w * ((3024 * w) + (3024 * z))) + (y * ((5184 * z) + (7776 * y) +
  (10368 * w))))) + (w * ((1080 * (z ^ 2)) + (w * ((720 * w) + (1080 * z))))) + (y * ((1080 * (z
  ^ 2)) + (w * ((1080 * w) + (1080 * z))))))) + (w * ((2016 * (z ^ 3)) + (w * ((3888 * (z ^ 2))
  + (w * ((1872 * w) + (3744 * z))))))) + (y * ((3456 * (z ^ 3)) + (w * ((10368 * (z ^ 2)) + (w
  * ((6912 * w) + (10368 * z))))) + (y * ((5184 * (z ^ 2)) + (w * ((5184 * w) + (5184 *
  z))))))))) + (v * ((72 * (z ^ 4)) + (v * ((360 * (z ^ 3)) + (v * ((v * ((288 * z) + (576 * w)
  + (864 * y))) + (w * ((864 * w) + (864 * z))) + (y * ((1728 * z) + (2592 * y) + (3456 * w)))))
  + (w * ((1080 * (z ^ 2)) + (w * ((720 * w) + (1080 * z))))) + (y * ((1080 * (z ^ 2)) + (w *
  ((1080 * w) + (1080 * z))))))) + (w * ((1008 * (z ^ 3)) + (w * ((1944 * (z ^ 2)) + (w * ((936
  * w) + (1872 * z))))))) + (y * ((1728 * (z ^ 3)) + (w * ((5184 * (z ^ 2)) + (w * ((3456 * w) +
  (5184 * z))))) + (y * ((2592 * (z ^ 2)) + (w * ((2592 * w) + (2592 * z))))))))) + (w * ((432 *
  (z ^ 4)) + (w * ((1728 * (z ^ 3)) + (w * ((2592 * (z ^ 2)) + (w * ((864 * w) + (2160 *
  z))))))))) + (x * ((108 * (z ^ 4)) + (u * ((u * ((432 * (z ^ 2)) + (w * ((1728 * w) + (1728 *
  z))) + (y * ((2592 * z) + (3888 * y) + (5184 * w))))) + (v * ((432 * (z ^ 2)) + (w * ((1728 *
  w) + (1728 * z))) + (y * ((2592 * z) + (3888 * y) + (5184 * w))))))) + (w * ((1512 * (z ^ 3))
  + (w * ((2916 * (z ^ 2)) + (w * ((1404 * w) + (2808 * z))))))) + (y * ((2592 * (z ^ 3)) + (w *
  ((7776 * (z ^ 2)) + (w * ((5184 * w) + (7776 * z))))) + (y * ((3888 * (z ^ 2)) + (w * ((3888 *
  w) + (3888 * z))))))) + ((v ^ 2) * ((432 * (z ^ 2)) + (w * ((1728 * w) + (1728 * z))) + (y *
  ((2592 * z) + (3888 * y) + (5184 * w))))))) + (y * ((864 * (z ^ 4)) + (w * ((1728 * (z ^ 3)) +
  (w * ((2592 * (z ^ 2)) + (w * ((864 * w) + (1728 * z))))))))))) + ((w ^ 2) * ((324 * (z ^ 4))
  + (w * ((648 * (z ^ 3)) + (324 * w * (z ^ 2)))))))

private theorem sos1_nonneg (x u v y w z : Real)
    (hx : 0 <= x) (hu : 0 <= u) (hv : 0 <= v)
    (hy : 0 <= y) (hw : 0 <= w) (hz : 0 <= z) :
    0 <= sos1 x u v y w z := by
  unfold sos1
  positivity

private theorem coeff1_identity (x u v y w z : Real) :
    coeff1 (sumRoots x u v + sumRoots y w z)
      (6*(pairRoots x u v + pairRoots y w z) + 2*sumRoots x u v*sumRoots y w z)
      (3*(pairRoots x u v + pairRoots y w z) + 2*sumRoots x u v*sumRoots y w z)
      (6*(prodRoots x u v + prodRoots y w z))
      (3*(prodRoots x u v + prodRoots y w z) +
        sumRoots x u v*pairRoots y w z + pairRoots x u v*sumRoots y w z) = sos1 x u v y w z := by
  unfold coeff1 sumRoots pairRoots prodRoots sos1
  ring

private theorem ordered_coeff1_nonneg (x u v y w z : Real)
    (hx : 0 <= x) (hu : 0 <= u) (hv : 0 <= v)
    (hy : 0 <= y) (hw : 0 <= w) (hz : 0 <= z) :
    0 <= coeff1 (sumRoots x u v + sumRoots y w z)
      (6*(pairRoots x u v + pairRoots y w z) + 2*sumRoots x u v*sumRoots y w z)
      (3*(pairRoots x u v + pairRoots y w z) + 2*sumRoots x u v*sumRoots y w z)
      (6*(prodRoots x u v + prodRoots y w z))
      (3*(prodRoots x u v + prodRoots y w z) +
        sumRoots x u v*pairRoots y w z + pairRoots x u v*sumRoots y w z) := by
  rw [coeff1_identity]
  exact sos1_nonneg x u v y w z hx hu hv hy hw hz

private def sos2 (x u v y w z : Real) : Real :=
  ((u * ((u * ((48 * (z ^ 4)) + (u * ((144 * (z ^ 3)) + (u * ((120 * (z ^ 2)) + (u * ((72 * z) +
  (144 * w) + (216 * y))) + (v * ((162 * v) + (180 * z) + (360 * w) + (540 * y))) + (w * ((120 *
  w) + (120 * z))))) + (v * ((240 * (z ^ 2)) + (v * ((216 * z) + (324 * v) + (432 * w) + (648 *
  y))) + (w * ((240 * w) + (240 * z))))) + (w * ((360 * (z ^ 2)) + (w * ((144 * w) + (216 *
  z))))) + (y * ((198 * (z ^ 2)) + (w * ((288 * w) + (288 * z))))))) + (v * ((216 * (z ^ 3)) +
  (v * ((180 * (z ^ 2)) + (v * ((144 * z) + (162 * v) + (288 * w) + (432 * y))) + (w * ((180 *
  w) + (180 * z))))) + (w * ((540 * (z ^ 2)) + (w * ((216 * w) + (324 * z))))) + (y * ((432 * (z
  ^ 2)) + (w * ((432 * w) + (432 * z))))))) + (w * ((60 * (z ^ 3)) + (w * ((180 * (z ^ 2)) + (w
  * ((120 * w) + (240 * z))))))) + (y * (w ^ 2) * ((72 * w) + (108 * z))))) + (v * ((48 * (z ^
  4)) + (v * ((72 * (z ^ 3)) + (v * ((60 * (z ^ 2)) + (v * ((36 * z) + (72 * w) + (108 * y))) +
  (w * ((60 * w) + (60 * z))))) + (w * ((324 * (z ^ 2)) + (w * ((360 * w) + (540 * z))))) + (y *
  ((342 * (z ^ 2)) + (w * ((432 * w) + (432 * z))))))) + (w * ((60 * (z ^ 3)) + (w * ((180 * (z
  ^ 2)) + (w * ((120 * w) + (240 * z))))))) + (y * (w ^ 2) * ((72 * w) + (108 * z))))) + (w *
  ((72 * (z ^ 4)) + (w * ((288 * (z ^ 3)) + (w * ((432 * (z ^ 2)) + (w * ((144 * w) + (360 *
  z))))))))) + (y * ((72 * (z ^ 4)) + (w * ((288 * (z ^ 3)) + (w * ((324 * (z ^ 2)) + (w * ((144
  * w) + (288 * z))))))))))) + (v * ((v * ((48 * (z ^ 4)) + (v * ((v * ((48 * (z ^ 2)) + (w *
  ((48 * w) + (48 * z))))) + (w * ((72 * (z ^ 2)) + (w * ((144 * w) + (216 * z))))) + (y * ((54
  * (z ^ 2)) + (w * ((144 * w) + (144 * z))))))) + (w * ((60 * (z ^ 3)) + (w * ((180 * (z ^ 2))
  + (w * ((120 * w) + (240 * z))))))) + (y * (w ^ 2) * ((72 * w) + (108 * z))))) + (w * ((36 *
  (z ^ 4)) + (w * ((144 * (z ^ 3)) + (w * ((216 * (z ^ 2)) + (w * ((72 * w) + (180 * z)))))))))
  + (y * ((36 * (z ^ 4)) + (w * ((144 * (z ^ 3)) + (w * ((162 * (z ^ 2)) + (w * ((72 * w) + (144
  * z))))))))))) + (x * ((u * ((u * ((144 * (z ^ 3)) + (u * ((72 * (z ^ 2)) + (u * ((72 * z) +
  (144 * w) + (216 * y))) + (v * ((144 * z) + (288 * w) + (432 * y))) + (w * ((72 * w) + (72 *
  z))))) + (v * ((108 * (z ^ 2)) + (v * ((216 * z) + (378 * w) + (648 * y))) + (w * ((108 * w) +
  (108 * z))))) + (w * ((432 * (z ^ 2)) + (w * ((288 * w) + (432 * z))))) + (y * ((432 * (z ^
  2)) + (w * ((432 * w) + (432 * z))))))) + (v * ((90 * (z ^ 3)) + (w * ((432 * (z ^ 2)) + (w *
  ((234 * w) + (432 * z))))) + (y * ((432 * (z ^ 2)) + (w * ((432 * w) + (432 * z))))) + ((v ^
  2) * ((90 * z) + (234 * w) + (432 * y))))))) + (w * ((108 * (z ^ 4)) + (w * ((432 * (z ^ 3)) +
  (w * ((648 * (z ^ 2)) + (w * ((216 * w) + (540 * z))))))))) + (y * ((216 * (z ^ 4)) + (w *
  ((432 * (z ^ 3)) + (w * ((648 * (z ^ 2)) + (w * ((216 * w) + (432 * z))))))))) + ((v ^ 2) *
  ((108 * (z ^ 3)) + (w * ((342 * (z ^ 2)) + (w * ((252 * w) + (432 * z))))) + (y * ((432 * (z ^
  2)) + (w * ((432 * w) + (432 * z))))) + ((v ^ 2) * ((36 * z) + (72 * w) + (216 * y))))))) +
  ((w ^ 2) * ((162 * (z ^ 4)) + (w * ((324 * (z ^ 3)) + (162 * w * (z ^ 2)))))) + (36 * u * y *
  (z ^ 2) * ((z + ((-1) * u)) ^ 2)) + (36 * u * y * (z ^ 2) * ((z + ((-1) * v)) ^ 2)) + (36 * v
  * y * (z ^ 2) * ((z + ((-1) * v)) ^ 2)) + (36 * w * x * (v ^ 2) * ((w + ((-1) * v)) ^ 2)) +
  (36 * w * x * (v ^ 2) * ((z + ((-1) * v)) ^ 2)) + (36 * x * z * (v ^ 2) * ((z + ((-1) * v)) ^
  2)) + (54 * u * y * (z ^ 2) * ((w + ((-1) * u)) ^ 2)) + (54 * u * y * (z ^ 2) * ((w + ((-1) *
  v)) ^ 2)) + (54 * v * y * (z ^ 2) * ((w + ((-1) * v)) ^ 2)) + (54 * w * x * (v ^ 2) * ((z +
  ((-1) * u)) ^ 2)) + (54 * u * v * w * x * ((w + ((-1) * v)) ^ 2)) + (54 * u * v * x * z * ((z
  + ((-1) * v)) ^ 2)))

private theorem sos2_nonneg (x u v y w z : Real)
    (hx : 0 <= x) (hu : 0 <= u) (hv : 0 <= v)
    (hy : 0 <= y) (hw : 0 <= w) (hz : 0 <= z) :
    0 <= sos2 x u v y w z := by
  unfold sos2
  positivity

private theorem coeff2_identity (x u v y w z : Real) :
    coeff2 (sumRoots x u v + sumRoots y w z)
      (6*(pairRoots x u v + pairRoots y w z) + 2*sumRoots x u v*sumRoots y w z)
      (3*(pairRoots x u v + pairRoots y w z) + 2*sumRoots x u v*sumRoots y w z)
      (6*(prodRoots x u v + prodRoots y w z))
      (3*(prodRoots x u v + prodRoots y w z) +
        sumRoots x u v*pairRoots y w z + pairRoots x u v*sumRoots y w z) = sos2 x u v y w z := by
  unfold coeff2 sumRoots pairRoots prodRoots sos2
  ring

private theorem ordered_coeff2_nonneg (x u v y w z : Real)
    (hx : 0 <= x) (hu : 0 <= u) (hv : 0 <= v)
    (hy : 0 <= y) (hw : 0 <= w) (hz : 0 <= z) :
    0 <= coeff2 (sumRoots x u v + sumRoots y w z)
      (6*(pairRoots x u v + pairRoots y w z) + 2*sumRoots x u v*sumRoots y w z)
      (3*(pairRoots x u v + pairRoots y w z) + 2*sumRoots x u v*sumRoots y w z)
      (6*(prodRoots x u v + prodRoots y w z))
      (3*(prodRoots x u v + prodRoots y w z) +
        sumRoots x u v*pairRoots y w z + pairRoots x u v*sumRoots y w z) := by
  rw [coeff2_identity]
  exact sos2_nonneg x u v y w z hx hu hv hy hw hz

private def sos3 (x u v y w z : Real) : Real :=
  ((u * ((u * ((12 * (z ^ 4)) + (u * ((8 * (z ^ 3)) + (u * ((12 * (z ^ 2)) + (27 * (v ^ 2)) + (w
  * ((6 * z) + (8 * w))))) + (v * ((24 * (z ^ 2)) + (54 * (v ^ 2)) + (w * ((18 * w) + (24 *
  z))))) + (12 * w * (z ^ 2)))) + (v * ((12 * (z ^ 3)) + (v * ((27 * (v ^ 2)) + (27 * (z ^ 2)) +
  (w * ((27 * w) + (36 * z))))) + (18 * w * (z ^ 2)))) + (w * ((24 * (z ^ 3)) + (w * ((27 * (z ^
  2)) + (w * ((8 * w) + (18 * z))))))))) + (v * ((6 * (z ^ 4)) + (v * ((v * ((18 * (z ^ 2)) + (w
  * ((24 * w) + (24 * z))))) + ((w ^ 2) * ((12 * w) + (18 * z))))) + (w * ((24 * (z ^ 3)) + (w *
  ((36 * (z ^ 2)) + (w * ((6 * w) + (24 * z))))))))))) + ((v ^ 2) * ((8 * (z ^ 4)) + (v * ((v *
  ((2 * (z ^ 2)) + (w * ((12 * w) + (12 * z))))) + ((w ^ 2) * ((8 * w) + (12 * z))))) + (w *
  ((24 * (z ^ 3)) + (w * ((21 * (z ^ 2)) + (w * ((12 * w) + (24 * z))))))))) + ((w ^ 2) * ((27 *
  (z ^ 4)) + (w * ((54 * (z ^ 3)) + (27 * w * (z ^ 2)))))) + (4 * (u ^ 2) * (w ^ 2) * ((w +
  ((-1) * u)) ^ 2)) + (4 * (v ^ 2) * (z ^ 2) * ((z + ((-1) * v)) ^ 2)) + (6 * (v ^ 2) * (z ^ 2)
  * ((w + ((-1) * v)) ^ 2)) + (9 * (u ^ 2) * (w ^ 2) * ((z + ((-1) * v)) ^ 2)) + (9 * (v ^ 2) *
  (z ^ 2) * ((w + ((-1) * u)) ^ 2)) + (6 * u * v * (w ^ 2) * ((w + ((-1) * u)) ^ 2)) + (6 * u *
  v * (z ^ 2) * ((z + ((-1) * v)) ^ 2)) + (6 * w * z * (u ^ 2) * ((w + ((-1) * u)) ^ 2)))

private theorem sos3_nonneg (x u v y w z : Real)
    (hx : 0 <= x) (hu : 0 <= u) (hv : 0 <= v)
    (hy : 0 <= y) (hw : 0 <= w) (hz : 0 <= z) :
    0 <= sos3 x u v y w z := by
  unfold sos3
  positivity

private theorem coeff3_identity (x u v y w z : Real) :
    coeff3 (sumRoots x u v + sumRoots y w z)
      (6*(pairRoots x u v + pairRoots y w z) + 2*sumRoots x u v*sumRoots y w z)
      (3*(pairRoots x u v + pairRoots y w z) + 2*sumRoots x u v*sumRoots y w z)
      (6*(prodRoots x u v + prodRoots y w z))
      (3*(prodRoots x u v + prodRoots y w z) +
        sumRoots x u v*pairRoots y w z + pairRoots x u v*sumRoots y w z) = sos3 x u v y w z := by
  unfold coeff3 sumRoots pairRoots prodRoots sos3
  ring

private theorem ordered_coeff3_nonneg (x u v y w z : Real)
    (hx : 0 <= x) (hu : 0 <= u) (hv : 0 <= v)
    (hy : 0 <= y) (hw : 0 <= w) (hz : 0 <= z) :
    0 <= coeff3 (sumRoots x u v + sumRoots y w z)
      (6*(pairRoots x u v + pairRoots y w z) + 2*sumRoots x u v*sumRoots y w z)
      (3*(pairRoots x u v + pairRoots y w z) + 2*sumRoots x u v*sumRoots y w z)
      (6*(prodRoots x u v + prodRoots y w z))
      (3*(prodRoots x u v + prodRoots y w z) +
        sumRoots x u v*pairRoots y w z + pairRoots x u v*sumRoots y w z) := by
  rw [coeff3_identity]
  exact sos3_nonneg x u v y w z hx hu hv hy hw hz

/-- The certificate covers every nonnegative ordered-gap tuple and t >= 0. -/
theorem ordered_numerator_nonneg (t x u v y w z : Real) (ht : 0 <= t)
    (hx : 0 <= x) (hu : 0 <= u) (hv : 0 <= v)
    (hy : 0 <= y) (hw : 0 <= w) (hz : 0 <= z) :
    let A1 := x + (x+u) + (x+u+v)
    let A2 := x*(x+u) + x*(x+u+v) + (x+u)*(x+u+v)
    let A3 := x*(x+u)*(x+u+v)
    let B1 := y + (y+w) + (y+w+z)
    let B2 := y*(y+w) + y*(y+w+z) + (y+w)*(y+w+z)
    let B3 := y*(y+w)*(y+w+z)
    0 <= numerator t (A1+B1) (6*(A2+B2)+2*A1*B1)
      (3*(A2+B2)+2*A1*B1) (6*(A3+B3)) (3*(A3+B3)+A1*B2+A2*B1) := by
  change 0 <= numerator t (sumRoots x u v + sumRoots y w z)
      (6*(pairRoots x u v + pairRoots y w z) + 2*sumRoots x u v*sumRoots y w z)
      (3*(pairRoots x u v + pairRoots y w z) + 2*sumRoots x u v*sumRoots y w z)
      (6*(prodRoots x u v + prodRoots y w z))
      (3*(prodRoots x u v + prodRoots y w z) +
        sumRoots x u v*pairRoots y w z + pairRoots x u v*sumRoots y w z)
  rw [numerator_expansion]
  exact add_nonneg
    (add_nonneg
      (add_nonneg (ordered_coeff0_nonneg x u v y w z hx hu hv hy hw hz)
        (mul_nonneg (ordered_coeff1_nonneg x u v y w z hx hu hv hy hw hz) ht))
      (mul_nonneg (ordered_coeff2_nonneg x u v y w z hx hu hv hy hw hz) (sq_nonneg t)))
    (mul_nonneg (ordered_coeff3_nonneg x u v y w z hx hu hv hy hw hz) (pow_nonneg ht 3))

#print axioms ordered_numerator_nonneg
#print axioms numerator_expansion
#print axioms coeff0_identity
#print axioms coeff1_identity
#print axioms coeff2_identity
#print axioms coeff3_identity
#print axioms sos0_nonneg
#print axioms sos1_nonneg
#print axioms sos2_nonneg
#print axioms sos3_nonneg
#print axioms ordered_coeff0_nonneg
#print axioms ordered_coeff1_nonneg
#print axioms ordered_coeff2_nonneg
#print axioms ordered_coeff3_nonneg

end D5.S3.Zeros.Convolution.GribinskiDegreeThreeDiscriminant
