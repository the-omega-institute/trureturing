/- GID: D5/S3/ContinuousObservables/ObserverZeroDistanceFibers
   generality: G
   mirror-B: D5/B/S3/ContinuousObservables/ObserverZeroDistanceFibers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Unit-ball spanning identifies observer fibers with zero-distance classes. -/

import D5.S3.ContinuousObservables.DualObserverDistanceReadings

/- Library-search audit trail (2026-08-28):
   * `DualObserverDistanceReadings` is the frozen owner of the unit-ball spanning zero
     criterion and is imported and projected rather than reproved.
   * Repository searches found no public theorem assembling that criterion with the exact
     readout-fiber equality, state separation consequence, and hidden-kernel witness.
   * Pinned Mathlib provides set extensionality; no exact observer-fiber theorem exists. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace D5.S3.ContinuousObservables.ObserverZeroDistanceFibers

open D5.S3.ContinuousObservables.DualObserverDistanceReadings
open D5.S3.Observer.Separation.RefinementDistanceMonotonicity

/-- When the unit-cost ball spans the bounded observable space, zero observer distance is
exactly agreement on all accessible readouts. Thus every readout fiber is a zero-distance
class; separating readouts make those classes singletons, while a hidden readout kernel
produces distinct states in one zero-distance class. -/
theorem observer_zero_distance_fibers
    {X : Type*}
    (observables : Submodule Real (lp (fun _ : X => Real) ∞))
    (cost : observables -> ENNReal)
    (costHomogeneous : forall (c : Real) (f : observables),
      cost (c • f) = ENNReal.ofReal |c| * cost f)
    (unitBallSpans : Submodule.span Real {f : observables | cost f <= 1} = ⊤) :
    (forall rho sigma : X,
      observerDistance Set.univ cost
          (fun state observable => observable.1 state) rho sigma = 0 <->
        forall f : observables, f.1 rho = f.1 sigma) /\
      (forall rho : X,
        {sigma | forall f : observables, f.1 rho = f.1 sigma} =
          {sigma | observerDistance Set.univ cost
            (fun state observable => observable.1 state) rho sigma = 0}) /\
      ((forall rho sigma : X,
          (forall f : observables, f.1 rho = f.1 sigma) -> rho = sigma) ->
        forall rho sigma : X,
          observerDistance Set.univ cost
            (fun state observable => observable.1 state) rho sigma = 0 ->
          rho = sigma) /\
      ((Exists fun pair : X × X =>
          pair.1 ≠ pair.2 /\
            forall f : observables, f.1 pair.1 = f.1 pair.2) ->
        Exists fun pair : X × X =>
          pair.1 ≠ pair.2 /\
            observerDistance Set.univ cost
              (fun state observable => observable.1 state) pair.1 pair.2 = 0) := by
  have zeroMeaning (rho sigma : X) :
      observerDistance Set.univ cost
          (fun state observable => observable.1 state) rho sigma = 0 <->
        forall f : observables, f.1 rho = f.1 sigma := by
    have readings := dual_observer_distance_readings
      observables observables cost cost costHomogeneous costHomogeneous rho sigma
    dsimp only at readings
    rcases readings.1 with zeroReading | finiteReading | infiniteReading
    · exact zeroReading.2.1 unitBallSpans
    · exact finiteReading.2.1 unitBallSpans
    · exact infiniteReading.2.1 unitBallSpans
  refine ⟨zeroMeaning, ?_, ?_, ?_⟩
  · intro rho
    ext sigma
    exact (zeroMeaning rho sigma).symm
  · intro separates rho sigma zeroDistance
    exact separates rho sigma ((zeroMeaning rho sigma).mp zeroDistance)
  · rintro ⟨⟨rho, sigma⟩, distinct, sameReadout⟩
    exact ⟨⟨rho, sigma⟩, distinct, (zeroMeaning rho sigma).mpr sameReadout⟩

example :
    let observables : Submodule Real (lp (fun _ : Unit => Real) ∞) := ⊥
    let cost : observables -> ENNReal := fun _ => 0
    (forall (c : Real) (f : observables),
      cost (c • f) = ENNReal.ofReal |c| * cost f) /\
      Submodule.span Real {f : observables | cost f <= 1} = ⊤ := by
  dsimp only
  constructor
  · intro c f
    simp
  · simp

#print axioms observer_zero_distance_fibers

end D5.S3.ContinuousObservables.ObserverZeroDistanceFibers
