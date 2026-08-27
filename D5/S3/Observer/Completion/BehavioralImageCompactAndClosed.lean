/- GID: D5/S3/Observer/Completion/BehavioralImageCompactAndClosed
   generality: G
   mirror-B: D5/B/S3/Observer/Completion/BehavioralImageCompactAndClosed
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Continuous coordinate readouts have a compact and closed behavioral image. -/

/- Library-search audit trail (2026-08-28):
   * Repository searches found no D5 theorem stating both compactness and closedness for this
     dependent-product behavior map.
   * Pinned Mathlib's `continuous_pi` proves continuity of the assembled behavior map from its
     coordinate hypotheses, and `isCompact_range` is the exact compact-image theorem.
   * `IsCompact.isClosed` is applied directly using the product's Hausdorff instance. -/

import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Completion.BehavioralImageCompactAndClosed

/-- The behavior map is constructed coordinatewise from the source readouts. Compactness of the
state carrier makes its range compact, and the Hausdorff dependent product makes that range
closed. -/
theorem behavioral_image_compact_and_closed
    {P X : Type*} {Lambda : P -> Type*}
    [TopologicalSpace X] [CompactSpace X]
    [forall p, TopologicalSpace (Lambda p)]
    [forall p, T2Space (Lambda p)]
    (readout : forall p, X -> Lambda p)
    (continuousReadout : forall p, Continuous (readout p)) :
    IsCompact (Set.range (fun x p => readout p x)) /\
      IsClosed (Set.range (fun x p => readout p x)) := by
  have continuousBehavior : Continuous (fun x p => readout p x) :=
    continuous_pi continuousReadout
  have compactBehavior : IsCompact (Set.range (fun x p => readout p x)) :=
    isCompact_range continuousBehavior
  exact ⟨compactBehavior, compactBehavior.isClosed⟩

#print axioms behavioral_image_compact_and_closed

end D5.S3.Observer.Completion.BehavioralImageCompactAndClosed
