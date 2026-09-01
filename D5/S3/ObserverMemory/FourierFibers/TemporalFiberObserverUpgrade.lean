/- GID: D5/S3/ObserverMemory/FourierFibers/TemporalFiberObserverUpgrade
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/FourierFibers/TemporalFiberObserverUpgrade
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Enlarging a time window shrinks observation fibers, and a separated finite mode family is resolved by its first full window. -/

import D5.S3.ObserverMemory.FourierFibers.FiniteCrystalTimeFrequencyBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ObserverMemory.FourierFibers.TemporalFiberObserverUpgrade

open D5.S3.ObserverMemory.FourierFibers.FiniteCrystalTimeFrequencyBridge

universe u

variable {K : Type u} [Field K]

/-- Joint readout over a finite set of observation times. -/
def temporalWindowReadout {n : ℕ}
    (modes : Fin n → K) (times : Finset ℕ) (amplitudes : Fin n → K) :
    {time : ℕ // time ∈ times} → K :=
  fun time => crystalTimeSample modes amplitudes time.1

/-- Two hidden states lie in the same temporal fiber when the selected time
window gives identical readings. -/
def SameTemporalFiber {n : ℕ}
    (modes : Fin n → K) (times : Finset ℕ)
    (left right : Fin n → K) : Prop :=
  temporalWindowReadout modes times left =
    temporalWindowReadout modes times right

/-- Adding observation times can only shrink a temporal fiber. -/
theorem same_temporal_fiber_antitone {n : ℕ}
    (modes : Fin n → K) {earlier later : Finset ℕ}
    (hIncluded : earlier ⊆ later) {left right : Fin n → K}
    (hLater : SameTemporalFiber modes later left right) :
    SameTemporalFiber modes earlier left right := by
  unfold SameTemporalFiber temporalWindowReadout at *
  funext time
  let lifted : {candidate : ℕ // candidate ∈ later} :=
    ⟨time.1, hIncluded time.2⟩
  exact congrFun hLater lifted

/-- The first `n` observations separate all amplitudes when the `n` modal
multipliers are distinct. -/
theorem first_full_window_separates {n : ℕ}
    {modes : Fin n → K} (hModes : Function.Injective modes)
    {left right : Fin n → K}
    (hSame : firstCrystalTimeWindow modes left =
      firstCrystalTimeWindow modes right) :
    left = right :=
  first_crystal_time_window_injective hModes hSame

/-- Every fiber of the first full window is a subsingleton under mode separation. -/
theorem first_full_window_fiber_subsingleton {n : ℕ}
    {modes : Fin n → K} (hModes : Function.Injective modes)
    (target : Fin n → K) :
    Set.Subsingleton
      {amplitudes : Fin n → K |
        firstCrystalTimeWindow modes amplitudes = target} := by
  intro left hLeft right hRight
  apply first_full_window_separates hModes
  rw [hLeft, hRight]

#print axioms same_temporal_fiber_antitone
#print axioms first_full_window_separates
#print axioms first_full_window_fiber_subsingleton

end D5.S3.ObserverMemory.FourierFibers.TemporalFiberObserverUpgrade
