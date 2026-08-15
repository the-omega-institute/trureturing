/- GID: D5/S3/ObserverMemory/Prediction/ForwardMergePersistence
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/ForwardMergePersistence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: States merged by a deterministic update have identical future states and readouts. -/

import Mathlib.Logic.Function.Iterate

/- Library-search audit trail (2026-08-15):
   * Exact pinned-Mathlib support hit: `Function.iterate_add_apply` decomposes
     an iterate at `t + r`; it is imported and applied below.
   * Loogle found no declaration matching the full persistent-equality shape.
   * LeanSearch returned nearby iterate and fixed-point lemmas, but no theorem
     carrying equality from one common iterate through every later iterate.
   * Repository searches for the hypothesis and conclusion shapes found no
     declaration covering this result.
-/

namespace D5.S3.ObserverMemory.Prediction.ForwardMergePersistence

/-- Once two states agree after a deterministic update has been iterated `t`
times, their states and every readout of those states agree after every
further number of updates. -/
theorem forward_merge_persistence
    {State : Type*} {Output : Type*} (F : State -> State)
    (q : State -> Output) (y y' : State) (t : Nat)
    (hMerge : (F^[t]) y = (F^[t]) y') :
    forall r : Nat,
      (F^[t + r]) y = (F^[t + r]) y' /\
        q ((F^[t + r]) y) = q ((F^[t + r]) y') := by
  intro r
  have hState : (F^[t + r]) y = (F^[t + r]) y' := by
    rw [Nat.add_comm t r, Function.iterate_add_apply,
      Function.iterate_add_apply]
    exact congrArg (F^[r]) hMerge
  exact And.intro hState (congrArg q hState)

/-- A constant Boolean update merges two distinct states after one step. -/
example :
    forall r : Nat,
      (((fun _ : Bool => false)^[1 + r]) false =
          ((fun _ : Bool => false)^[1 + r]) true) /\
        id (((fun _ : Bool => false)^[1 + r]) false) =
          id (((fun _ : Bool => false)^[1 + r]) true) :=
  forward_merge_persistence (fun _ : Bool => false) id false true 1 rfl

end D5.S3.ObserverMemory.Prediction.ForwardMergePersistence
