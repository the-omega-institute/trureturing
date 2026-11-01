/- GID: D5/S3/Geometry/Hyperideal/MixedMatchingRawCosine
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/MixedMatchingRawCosine
   mirror-E: none(waiver:mixed-matching-raw-cosine)
   anchors: []
   utility: none
   digest: The symmetric six-variable hyper-ideal cosine reduces to the radial closed form used by mixed matching. -/

/-
proof_shape: raw_cosine_formula: content
admission_basis: escape-witness.
escape_witness: the factorization of the two square-root radicands and the
numerator cancellation are derived from the six-variable formula in this file.
Escape audit unfinished: issue #10609 tracks the missing faithful four-slot
registration for this mixed-matching analytic family.
-/

import D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Geometry.Hyperideal.MixedMatchingRawCosine

open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes

/-- The radial parameter used by the symmetric mixed-matching shape. -/
def radialQ (r t : ℝ) : ℝ := 2 * t ^ 2 / (r - 1)

/-- The raw six-variable cosine on `(r,t,t,o,t,t)` has a one-variable radial form. -/
theorem raw_cosine_formula {r t o : ℝ} (hr : 1 < r) (ht : 0 < t) :
    cosine r t t o t t =
      (radialQ r t - o) / (radialQ r t + 1) := by
  have hrm : 0 < r - 1 := by linarith
  have hrp : 0 < r + 1 := by linarith
  have hrad : 0 < rad r t t := by
    unfold rad
    nlinarith [sq_nonneg (r - 1), sq_nonneg t]
  have hsqrt : 0 < Real.sqrt (rad r t t) := Real.sqrt_pos.2 hrad
  have hsqrt_sq : (Real.sqrt (rad r t t)) ^ 2 = rad r t t :=
    Real.sq_sqrt hrad.le
  have hrad_factor : rad r t t = (r + 1) * (r - 1 + 2 * t ^ 2) := by
    unfold rad
    ring
  have hnum_factor : numerator r t t o t t =
      (r + 1) * (2 * t ^ 2 - (r - 1) * o) := by
    unfold numerator
    ring
  rw [cosine, hnum_factor, div_div, ← pow_two, hsqrt_sq, hrad_factor]
  dsimp [radialQ]
  field_simp [ne_of_gt hrm, ne_of_gt hrp]
  ring

#print axioms raw_cosine_formula

end D5.S3.Geometry.Hyperideal.MixedMatchingRawCosine
