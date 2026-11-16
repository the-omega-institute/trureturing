/- GID: D5/S3/Quantum/Analysis/PositiveInteriorGridObstruction
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/PositiveInteriorGridObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A positive-interior three-point spectral-grid algebraic obstruction. -/

import Mathlib.Tactic

/-! # Positive-interior spectral-grid obstruction -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Analysis.PositiveInteriorGridObstruction

/--
The two reduced power-sum equations for a three-by-three unit-circle grid are
incompatible with a product modulus strictly between zero and one.

The variables `ur + I ui` and `vr + I vi` represent the two reduced complex
parameters, `s` and `t` their squared norms, and `hnorm` the squared norm of
their product.  This is the algebraic bridge used by the spectral-grid
argument; it does not assert the preceding saturation or unitary-realization
steps.
-/
theorem positive_interior_grid_algebraic_obstruction
    (r ur ui vr vi s t : ℝ)
    (hr_pos : 0 < r) (hr_lt_one : r < 1)
    (hsum_re : ur + vr = 2) (hsum_im : ui + vi = 0)
    (he_re : ur * s + vr * t + s * t + 3 - 3 * (s + t) = 0)
    (he_im : ui * s + vi * t = 0)
    (hs : s = ur ^ 2 + ui ^ 2) (ht : t = vr ^ 2 + vi ^ 2)
    (hnorm : (ur * vr - ui * vi) ^ 2 + (ur * vi + ui * vr) ^ 2 = r ^ 2) :
    False := by
  have hvr : vr = 2 - ur := by linarith
  have hvi : vi = -ui := by linarith
  subst vr
  subst vi
  by_cases hui : ui = 0
  · subst ui
    have hs' : s = ur ^ 2 := by simpa using hs
    have ht' : t = (2 - ur) ^ 2 := by simpa using ht
    have hq : (ur * (2 - ur)) ^ 2 = 1 := by
      nlinarith [he_re, hs', ht']
    have hrq : r ^ 2 = (ur * (2 - ur)) ^ 2 := by
      nlinarith [hnorm]
    nlinarith
  · have hst : s = t := by
      have hzero : ui * (s - t) = 0 := by
        nlinarith [he_im]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hui)
    have hur : ur = 1 := by
      nlinarith [hs, ht, hst]
    have hs_one : 1 < s := by
      nlinarith [hs]
    have hr_s : r ^ 2 = s ^ 2 := by
      nlinarith [hnorm, hur]
    nlinarith

end D5.S3.Quantum.Analysis.PositiveInteriorGridObstruction
