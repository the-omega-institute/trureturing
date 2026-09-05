/- GID: D5/S3/Midline/Cayley/CayleyMirrorCoordinates
   generality: I
   mirror-B: D5/B/S3/Midline/Cayley/CayleyMirrorCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Mirror inversion negates the logarithmic Cayley radius and preserves its angle. -/

/- Library-search audit trail (2026-09-04):
   * D5 supplies the canonical `mirror`, `cayleyCoefficient`, and
     `logarithmicRadialDefect` definitions.  The frozen
     `logarithmic_radial_defect_and_mirror` is restricted to indexed source
     zeros and omits both the coefficient identity and the phase clause.
   * Pinned Mathlib supplies the exact quotient-valued phase identities
     `Complex.arg_conj_coe_angle` and `Complex.arg_inv_coe_angle`, together
     with `Real.log_inv`; no declaration packages the three clauses below.
   * Loogle and GitHub ecosystem searches for the Cayley coefficient and
     inverse-conjugate argument found only the Mathlib phase lemmas and a
     downstream use of them, not the whole statement.
-/

import D5.S3.Midline.Cayley.LogarithmicRadialDefect
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Midline.Cayley.CayleyMirrorCoordinates

open D5.S3.Midline.Cayley.CayleyUnitarityDefect
open D5.S3.Midline.Cayley.LogarithmicRadialDefect
open D5.S3.Weil.ReflectionLedger
open scoped ComplexConjugate

/-- Conjugate reflection sends the Cayley coefficient to the reciprocal of
its conjugate.  Consequently the logarithmic radius changes sign while the
argument, viewed modulo two pi in `Real.Angle`, is unchanged. -/
theorem cayley_mirror_coordinates (s : Complex) :
    cayleyCoefficient (mirror s) = (conj (cayleyCoefficient s))⁻¹ ∧
      logarithmicRadialDefect (mirror s) = -logarithmicRadialDefect s ∧
      (Complex.arg (cayleyCoefficient (mirror s)) : Real.Angle) =
        (Complex.arg (cayleyCoefficient s) : Real.Angle) := by
  have hcoefficient :
      cayleyCoefficient (mirror s) = (conj (cayleyCoefficient s))⁻¹ := by
    simp only [cayleyCoefficient, mirror, reflection]
    rw [show 1 - conj s - 1 = -conj s by ring,
      show 1 - conj s = -(conj s - 1) by ring, neg_div_neg_eq]
    simp
  refine ⟨hcoefficient, ?_, ?_⟩
  · simp [logarithmicRadialDefect, hcoefficient, Real.log_inv]
  · rw [hcoefficient]
    simp

#print axioms cayley_mirror_coordinates

end D5.S3.Midline.Cayley.CayleyMirrorCoordinates
