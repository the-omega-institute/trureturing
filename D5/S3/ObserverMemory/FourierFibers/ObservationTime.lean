/- GID: D5/S3/ObserverMemory/FourierFibers/ObservationTime
   generality: G
   mirror-B: none(waiver:new-observer-library-node)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Observation time is the first finite readout depth at which two states become distinguishable. -/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.FourierFibers.ObservationTime

/-- A finite observation window records the first `depth` orbit readouts. -/
def observationWindow {State Readout : Type*}
    (step : State → State) (readout : State → Readout)
    (depth : ℕ) (state : State) : Fin depth → Readout :=
  fun i => readout ((step^[i.1]) state)

/-- Two states are indistinguishable through a finite observation depth. -/
def IndistinguishableThrough {State Readout : Type*}
    (step : State → State) (readout : State → Readout)
    (depth : ℕ) (left right : State) : Prop :=
  observationWindow step readout depth left =
    observationWindow step readout depth right

/-- The first visible depth of a pair is the least finite observation window
that distinguishes it. This separates observation depth from dynamical time. -/
def FirstVisibleDepth {State Readout : Type*}
    (step : State → State) (readout : State → Readout)
    (left right : State) (depth : ℕ) : Prop :=
  ¬ IndistinguishableThrough step readout depth left right ∧
    ∀ earlier < depth,
      IndistinguishableThrough step readout earlier left right

/-- Enlarging the observation window cannot restore indistinguishability once
an earlier prefix already distinguishes the states. -/
theorem distinguishable_monotone {State Readout : Type*}
    (step : State → State) (readout : State → Readout)
    {left right : State} {small large : ℕ}
    (hsmall : small ≤ large)
    (hdiff : ¬ IndistinguishableThrough step readout small left right) :
    ¬ IndistinguishableThrough step readout large left right := by
  intro hlarge
  apply hdiff
  funext i
  have hi : i.1 < large := lt_of_lt_of_le i.2 hsmall
  have hpoint := congrFun hlarge ⟨i.1, hi⟩
  exact hpoint

/-- A first visible depth remains visible at every deeper observation window. -/
theorem first_visible_depth_persists {State Readout : Type*}
    (step : State → State) (readout : State → Readout)
    {left right : State} {depth later : ℕ}
    (hfirst : FirstVisibleDepth step readout left right depth)
    (hdepth : depth ≤ later) :
    ¬ IndistinguishableThrough step readout later left right :=
  distinguishable_monotone step readout hdepth hfirst.1

#print axioms distinguishable_monotone
#print axioms first_visible_depth_persists

end D5.S3.ObserverMemory.FourierFibers.ObservationTime
