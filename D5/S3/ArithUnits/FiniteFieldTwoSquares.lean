/- GID: D5/S3/ArithUnits/FiniteFieldTwoSquares
   generality: G
   mirror-B: D5/B/S3/ArithUnits/FiniteFieldTwoSquares
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every residue modulo a prime is the sum of two residue squares. -/

import Mathlib.FieldTheory.Finite.Basic

namespace D5.S3.ArithUnits.FiniteFieldTwoSquares

/-- Every element of a prime residue field is a sum of two squares. This is the
repository-addressed form of Mathlib's finite-field theorem `ZMod.sq_add_sq`. -/
theorem every_element_eq_sq_add_sq (p : ℕ) [Fact p.Prime] (x : ZMod p) :
    ∃ a b : ZMod p, a ^ 2 + b ^ 2 = x :=
  ZMod.sq_add_sq p x

end D5.S3.ArithUnits.FiniteFieldTwoSquares
