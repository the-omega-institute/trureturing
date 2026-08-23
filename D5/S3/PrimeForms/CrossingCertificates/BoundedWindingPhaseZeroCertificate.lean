/- GID: D5/S3/PrimeForms/CrossingCertificates/BoundedWindingPhaseZeroCertificate
   generality: I
   mirror-B: D5/B/S3/PrimeForms/CrossingCertificates/BoundedWindingPhaseZeroCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A bounded integral winding phase divisible by its modulus is zero. -/

import D5.S3.PrimeForms.Crossing.ExactPropagation
import Mathlib.Algebra.Order.Group.Unbundled.Int

/- Library-search audit trail (2026-08-24):
   * Exact pinned-Mathlib hit `Int.eq_zero_of_abs_lt_dvd` proves that an
     integer strictly smaller in absolute value than a divisor is zero; it is
     applied directly below.
   * Repository exact hits `PositiveMatrix` and `windingPhase` provide the
     canonical crossing carrier and phase channel and are imported rather
     than redeclared.
   * Searches for bounded winding-phase divisibility and local-to-global zero
     certificates found no existing repository theorem with this statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.PrimeForms.CrossingCertificates.BoundedWindingPhaseZeroCertificate

open D5.S3.PrimeForms.Crossing.ExactPropagation

/-- If the canonical winding phase has an integral value whose absolute value
is strictly below a natural modulus and that modulus divides the value, then
the winding phase is globally zero. -/
theorem bounded_winding_phase_zero_certificate
    (A : PositiveMatrix) (phaseValue : Int) (modulus : Nat)
    (hphase : windingPhase A = phaseValue)
    (hbound : |phaseValue| < (modulus : Int))
    (hdivides : (modulus : Int) ∣ phaseValue) :
    windingPhase A = 0 := by
  have hzero : phaseValue = 0 :=
    Int.eq_zero_of_abs_lt_dvd hdivides hbound
  simpa [hzero] using hphase

#print axioms bounded_winding_phase_zero_certificate

end D5.S3.PrimeForms.CrossingCertificates.BoundedWindingPhaseZeroCertificate
