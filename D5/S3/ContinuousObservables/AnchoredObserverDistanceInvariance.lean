/- GID: D5/S3/ContinuousObservables/AnchoredObserverDistanceInvariance
   generality: G
   mirror-B: D5/B/S3/ContinuousObservables/AnchoredObserverDistanceInvariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Compatible group actions preserve observer distance and anchored radius. -/

import D5.S3.Observer.Separation.RefinementDistanceMonotonicity

/- Library-search audit trail (2026-08-28):
   * Repository body-shape searches found the canonical general `observerDistance` in
     `RefinementDistanceMonotonicity`, which is imported and used without redeclaration.
   * Searches for action invariance of that distance and its anchored radius were misses;
     permutation-specific orbit distances have a different observable carrier.
   * Pinned Mathlib supplies the group-action identities used to reindex the supremum, but
     no theorem specialized to this observer-distance construction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ContinuousObservables.AnchoredObserverDistanceInvariance

open D5.S3.Observer.Separation.RefinementDistanceMonotonicity

/-- A group action that transports admissible observables without changing their cost and
commutes with evaluation preserves the induced distance. The distance from an origin fixed by
the acting element is consequently invariant as well. -/
theorem anchored_observer_distance_invariance
    {G Observable State : Type*}
    [Group G] [MulAction G Observable] [MulAction G State]
    (observables : Set Observable) (seminorm : Observable -> ENNReal)
    (evaluate : State -> Observable -> Real)
    (actionClosed : forall (g : G) (f : Observable),
      f ∈ observables -> g • f ∈ observables)
    (costInvariant : forall (g : G) (f : Observable),
      f ∈ observables -> seminorm (g • f) = seminorm f)
    (evaluationCompatible : forall (g : G) (f : Observable) (x : State),
      evaluate (g • x) (g • f) = evaluate x f)
    (origin : State) :
    observerDistance observables seminorm evaluate origin origin = 0 /\
      (forall (g : G) (x y : State),
        observerDistance observables seminorm evaluate (g • x) (g • y) =
          observerDistance observables seminorm evaluate x y) /\
      forall (g : G) (x : State), g • origin = origin ->
        observerDistance observables seminorm evaluate origin (g • x) =
          observerDistance observables seminorm evaluate origin x := by
  have oneSide (g : G) (x y : State) :
      observerDistance observables seminorm evaluate (g • x) (g • y) <=
        observerDistance observables seminorm evaluate x y := by
    unfold observerDistance
    apply iSup_le
    intro observable
    let pulled : {f // f ∈ observables ∧ seminorm f <= 1} :=
      ⟨g⁻¹ • observable.1,
        actionClosed g⁻¹ observable.1 observable.2.1,
        by simpa [costInvariant g⁻¹ observable.1 observable.2.1] using observable.2.2⟩
    have hx : evaluate (g • x) observable.1 = evaluate x pulled.1 := by
      simpa [pulled, smul_smul] using
        evaluationCompatible g (g⁻¹ • observable.1) x
    have hy : evaluate (g • y) observable.1 = evaluate y pulled.1 := by
      simpa [pulled, smul_smul] using
        evaluationCompatible g (g⁻¹ • observable.1) y
    rw [hx, hy]
    exact le_iSup
      (fun f : {A // A ∈ observables ∧ seminorm A <= 1} =>
        ENNReal.ofReal |evaluate x f.1 - evaluate y f.1|) pulled
  have distanceInvariant (g : G) (x y : State) :
      observerDistance observables seminorm evaluate (g • x) (g • y) =
        observerDistance observables seminorm evaluate x y := by
    apply le_antisymm
    · exact oneSide g x y
    · simpa [smul_smul] using oneSide g⁻¹ (g • x) (g • y)
  refine ⟨?_, distanceInvariant, ?_⟩
  · unfold observerDistance
    exact iSup_eq_bot.mpr (fun _ => by simp)
  · intro g x fixedOrigin
    simpa only [fixedOrigin] using distanceInvariant g origin x

example :
    let action : Unit -> Unit -> Unit := fun _ x => x
    (forall (g f : Unit),
      f ∈ (Set.univ : Set Unit) -> action g f ∈ (Set.univ : Set Unit)) /\
      (forall (_g : Unit) (f : Unit), f ∈ (Set.univ : Set Unit) ->
        (0 : ENNReal) = (0 : ENNReal)) /\
      forall (_g _f _x : Unit), (0 : Real) = (0 : Real) := by
  simp

#print axioms anchored_observer_distance_invariance

end D5.S3.ContinuousObservables.AnchoredObserverDistanceInvariance
