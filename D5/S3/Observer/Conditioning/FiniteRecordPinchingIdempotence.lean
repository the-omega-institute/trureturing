/- GID: D5/S3/Observer/Conditioning/FiniteRecordPinchingIdempotence
   generality: G
   mirror-B: D5/B/S3/Observer/Conditioning/FiniteRecordPinchingIdempotence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite complete record pinching is idempotent as a matrix endomorphism. -/

/- Library-search audit trail (2026-08-22):
   * The frozen repository declaration `Conditioning.unreadState_idempotent` is the exact
     pointwise theorem for the source construction and is applied directly below.
   * Local pinned-Mathlib searches found projection predicates such as `IsStarProjection`,
     but no packaged theorem for this finite complete pinching construction.
   * Loogle searches for a star-projection multiplication theorem and for
     `Function.comp f f = f` found no exact finite pinching theorem.
   * The qubit standard-basis theorem `QuantumChannels.Pinching.pinching_idempotent` is a
     strict special case, so it is not used as coverage for the general finite family.
-/

import D5.S3.Observer.Conditioning

namespace D5.S3.Observer.Conditioning.FiniteRecordPinchingIdempotence

open D5.S3.Observer.Conditioning

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- For any finite complete family of pairwise orthogonal self-adjoint projections, the
unread record map `rho |-> sum k, P k * rho * P k` is idempotent as a function. -/
theorem finite_record_pinching_idempotent
    {n kappa : Type*} [Fintype n] [DecidableEq n]
    [Fintype kappa]
    (P : kappa -> Matrix n n ℂ) (hP : IsRecordMeasurement P) :
    Function.comp (unreadState P) (unreadState P) = unreadState P := by
  funext rho
  exact unreadState_idempotent hP rho

end D5.S3.Observer.Conditioning.FiniteRecordPinchingIdempotence
