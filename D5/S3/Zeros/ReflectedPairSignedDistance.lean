/- GID: D5/S3/Zeros/ReflectedPairSignedDistance
   generality: G
   mirror-B: D5/B/S3/Zeros/ReflectedPairSignedDistance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A reflected pair becomes a negative signed distance in the squared normal coordinate. -/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

/-!
# Reflected-pair signed distance

A reflected pair at normal offsets `-delta` and `delta` has amplitude
`(r - delta) * (r + delta)`. Passing to the squared normal coordinate turns
this into `r^2 - delta^2`. Thus the pair is represented by the negative signed
support point `-delta^2`.

The same finite model has logarithmic slope `2 / (u - delta^2)` away from its
pole. This is the elementary resolvent chart that a later spectral bridge must
recover from completed-xi data. No claim about xi, zero isolation, or RH is made
here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Zeros.ReflectedPairSignedDistance

/-- A reflected normal pair factors through the negative signed squared
support `-delta^2`; its squared-coordinate intensity has the corresponding
simple resolvent logarithmic slope away from the pole. -/
theorem reflected_pair_signed_distance_resolvent
    (delta r u : Real)
    (hdelta : 0 < delta)
    (hu : u ≠ delta ^ 2) :
    let signedDistance := -delta ^ 2
    let pairAmplitude := (r - delta) * (r + delta)
    let centerIntensity := fun v : Real => (v + signedDistance) ^ 2
    signedDistance < 0 /\
      pairAmplitude = r ^ 2 + signedDistance /\
      pairAmplitude ^ 2 = centerIntensity (r ^ 2) /\
      deriv centerIntensity u / centerIntensity u =
        2 / (u + signedDistance) := by
  dsimp only
  have hDeltaSquare : 0 < delta ^ 2 := sq_pos_of_pos hdelta
  have hNonzero : u + -delta ^ 2 ≠ 0 := by
    simpa [sub_eq_add_neg] using (sub_ne_zero.mpr hu)
  have hDerivative :
      HasDerivAt (fun v : Real => (v + -delta ^ 2) ^ 2)
        (2 * (u + -delta ^ 2)) u := by
    convert (((hasDerivAt_id u).add_const (-delta ^ 2)).pow 2) using 1 <;> ring
  refine ⟨by nlinarith, by ring, by ring, ?_⟩
  rw [hDerivative.deriv]
  field_simp [hNonzero]
  ring

#print axioms reflected_pair_signed_distance_resolvent

end D5.S3.Zeros.ReflectedPairSignedDistance
