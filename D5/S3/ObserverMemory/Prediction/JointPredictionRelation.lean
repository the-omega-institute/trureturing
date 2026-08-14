/- GID: D5/S3/ObserverMemory/Prediction/JointPredictionRelation
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/JointPredictionRelation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A joint observation identifies exactly the pairs identified by every component. -/

import Mathlib.Data.Set.Lattice

/- Provenance: pinned mathlib supplies function extensionality as `funext_iff`
   and indexed-intersection membership as `Set.mem_iInter`. Searches for a
   packaged joint equality-kernel identity returned no declaration. -/

namespace D5.S3.ObserverMemory.Prediction.JointPredictionRelation

universe u v w

/-- The equality-kernel relation induced by an observation. -/
def predictionRelation {Y : Type v} {Z : Type w} (q : Y -> Z) : Set (Y × Y) :=
  {pair | q pair.1 = q pair.2}

/-- The observation that records every member of an indexed family. -/
def jointObservation {I : Type u} {Y : Type v} {Z : I -> Type w}
    (q : (i : I) -> Y -> Z i) : Y -> (i : I) -> Z i :=
  fun y i => q i y

/-- The equality-kernel of a joint observation is the intersection of the
equality-kernels of all its component observations. -/
theorem joint_prediction_relation {I : Type u} {Y : Type v} {Z : I -> Type w}
    (q : (i : I) -> Y -> Z i) :
    predictionRelation (jointObservation q) =
      ⋂ i, predictionRelation (q i) := by
  ext pair
  simp only [predictionRelation, Set.mem_setOf_eq, Set.mem_iInter]
  exact funext_iff

end D5.S3.ObserverMemory.Prediction.JointPredictionRelation
