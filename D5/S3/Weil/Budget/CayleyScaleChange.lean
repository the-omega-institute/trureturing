/- GID: D5/S3/Weil/Budget/CayleyScaleChange
   generality: G
   mirror-B: D5/B/S3/Weil/Budget/CayleyScaleChange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Changing a positive Cayley scale is the corresponding real disk automorphism. -/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/- Library-search audit trail (2026-08-29):
   * D5 and current-origin searches found no parameterized Cayley scale-change law.
   * The only matching coordinate body was the fixed-scale definition
     `D5.S3.Analytic.LiCausalTrichotomy.cayley` at scale `1/2`; it cannot carry
     the source's two positive scale parameters.
   * Body-shape searches for `(a - b) / (a + b)` and `(z + r) / (1 + r * z)`
     found no reusable D5 scale parameter or real disk automorphism.
   * Pinned Mathlib has field normalization tactics but no exact identity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Budget.CayleyScaleChange

/-- The source's Cayley coordinate at a real scale. -/
noncomputable def cayleyCoordinate (scale spectral : Real) : Complex :=
  ((spectral : Complex) + Complex.I * (scale : Complex)) /
    ((spectral : Complex) - Complex.I * (scale : Complex))

/-- The hyperbolic parameter comparing two positive scales. -/
noncomputable def scaleChangeParameter (a b : Real) : Real :=
  (a - b) / (a + b)

/-- The real-parameter disk automorphism used to transport Cayley coordinates. -/
noncomputable def realDiskAutomorphism (r : Real) (z : Complex) : Complex :=
  (z + (r : Complex)) / (1 + (r : Complex) * z)

set_option linter.flexible false in
private theorem cayley_scale_change_algebra
    (A B X : Complex)
    (hA : A ≠ 0) (hAB : A + B ≠ 0)
    (hXA : X - Complex.I * A ≠ 0)
    (hXB : X - Complex.I * B ≠ 0) :
    (X + Complex.I * B) / (X - Complex.I * B) =
      (((X + Complex.I * A) / (X - Complex.I * A)) + (A - B) / (A + B)) /
        (1 + (A - B) / (A + B) *
          ((X + Complex.I * A) / (X - Complex.I * A))) := by
  have htwoA : (2 : Complex) * A ≠ 0 := mul_ne_zero (by norm_num) hA
  have hXAcomm : -(A * Complex.I) + X ≠ 0 := by
    simpa [mul_comm, sub_eq_add_neg, add_comm] using hXA
  have hXAalt : X - A * Complex.I ≠ 0 := by
    simpa [mul_comm] using hXA
  have htransportDen : X * A * 2 - Complex.I * B * A * 2 ≠ 0 := by
    have hproduct := mul_ne_zero htwoA hXB
    convert hproduct using 1
    ring
  have hcombinedDen :
      (X - Complex.I * A) * (A + B) +
          (X + Complex.I * A) * (A - B) ≠ 0 := by
    convert htransportDen using 1
    ring
  have hdenIdentity :
      1 + (A - B) / (A + B) *
          ((X + Complex.I * A) / (X - Complex.I * A)) =
        ((2 : Complex) * A * (X - Complex.I * B)) /
          ((A + B) * (X - Complex.I * A)) := by
    field_simp [hAB, hXA, hXAcomm]
    apply (mul_right_cancel₀ hXAcomm)
    simp [hXAcomm]
    apply (mul_right_cancel₀ hXAalt)
    simp [hXAalt]
    ring
  have hden :
      1 + (A - B) / (A + B) *
          ((X + Complex.I * A) / (X - Complex.I * A)) ≠ 0 := by
    rw [hdenIdentity]
    exact div_ne_zero (mul_ne_zero htwoA hXB) (mul_ne_zero hAB hXA)
  field_simp [hAB, hXA, hXAcomm, hXB, hden, htransportDen]
  apply (mul_right_cancel₀ htransportDen)
  simp [htransportDen]
  field_simp [hcombinedDen]
  ring_nf

/-- For positive real scales `a` and `b`, the scale-`b` Cayley coordinate is
the real disk automorphism with parameter `(a - b) / (a + b)` applied to the
scale-`a` coordinate. -/
theorem cayley_scale_change
    (a b spectral : Real) (ha : 0 < a) (hb : 0 < b) :
    cayleyCoordinate b spectral =
      realDiskAutomorphism (scaleChangeParameter a b)
        (cayleyCoordinate a spectral) := by
  have hA : (a : Complex) ≠ 0 := by exact_mod_cast ne_of_gt ha
  have hAB : (a : Complex) + (b : Complex) ≠ 0 := by
    exact_mod_cast ne_of_gt (add_pos ha hb)
  have hXA : (spectral : Complex) - Complex.I * (a : Complex) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hXB : (spectral : Complex) - Complex.I * (b : Complex) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  simpa only [cayleyCoordinate, realDiskAutomorphism, scaleChangeParameter,
    Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_div] using
      cayley_scale_change_algebra
        (a : Complex) (b : Complex) (spectral : Complex) hA hAB hXA hXB

#print axioms cayley_scale_change

end D5.S3.Weil.Budget.CayleyScaleChange
