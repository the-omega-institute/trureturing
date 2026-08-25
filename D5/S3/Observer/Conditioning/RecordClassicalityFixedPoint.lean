/- GID: D5/S3/Observer/Conditioning/RecordClassicalityFixedPoint
   generality: G
   mirror-B: D5/B/S3/Observer/Conditioning/RecordClassicalityFixedPoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Unread record fixed points are exactly matrices with vanishing cross-record blocks. -/

import D5.S3.Observer.Conditioning

/- Library-search audit trail (2026-08-25):
   * Exact repository hit: `unreadState_fixed_iff` already proves the complete
     fixed-point characterization for the canonical finite record measurement
     and unread-state construction; it is applied directly below.
   * Searches in pinned Mathlib for pinching fixed points, off-diagonal block
     vanishing, and finite projection families found no equivalent arbitrary-family
     theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Conditioning.RecordClassicalityFixedPoint

open D5.S3.Observer.Conditioning

variable {n kappa : Type*} [Fintype n] [DecidableEq n] [Fintype kappa]
    {P : kappa -> Matrix n n ℂ}

/-- Relative to a finite complete orthogonal record measurement, the unread
record map fixes exactly the matrices whose cross-record blocks vanish. -/
theorem record_classicality_fixed_point
    (hP : IsRecordMeasurement P) (rho : Matrix n n ℂ) :
    unreadState P rho = rho <->
      forall k l, k ≠ l -> P k * rho * P l = 0 :=
  unreadState_fixed_iff hP rho

#print axioms record_classicality_fixed_point

end D5.S3.Observer.Conditioning.RecordClassicalityFixedPoint
