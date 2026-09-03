/- GID: D5/S3/ObserverMemory/PredictionCertificates/FiniteStableDepth
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/PredictionCertificates/FiniteStableDepth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite state space reaches its complete prediction relation at a finite depth. -/

import D5.S3.ObserverMemory.Prediction.JointPredictionRelation
import D5.S3.ObserverMemory.RefinementClosure.FiniteHorizonKernelRecurrence

/- Library-search audit trail (2026-09-03):
   * Exact repository hit `finite_horizon_stabilizes_at_completionDepth`
     supplies the finite-state kernel equality and is applied directly.
   * Repository hit `jointObservation` carries the source's indexed local
     readouts without introducing a second joint-readout definition.
   * Pinned-Mathlib text searches found no exact finite-horizon Setoid
     stabilization theorem. A shaped Loogle query was rejected by its parser;
     no third-party search was needed after the exact repository hit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.PredictionCertificates.FiniteStableDepth

open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
open D5.S3.ObserverMemory.Prediction.ItineraryCompletion
open D5.S3.ObserverMemory.Prediction.JointPredictionRelation
open D5.S3.ObserverMemory.RefinementClosure.FiniteHorizonKernelRecurrence

universe u v w

/-- A finite state space reaches the complete prediction relation at a finite
depth. Here `jointObservation q` is the source's `q_J`; `finiteHorizonKernel`
is `R_m^J` (source lines 1456-1470 and 1666-1672), while the kernel of
`completeItinerary` is `R_infinity^J` (source lines 1488-1504). -/
theorem finite_state_has_stable_depth
    {X : Type u} {J : Type v} {O : J -> Type w} [Finite X]
    (F : X -> X) (q : (i : J) -> X -> O i) :
    exists m : Nat,
      finiteHorizonKernel F (jointObservation q) m =
        Setoid.ker (completeItinerary F (jointObservation q)) := by
  let _ := Fintype.ofFinite X
  exact
    ⟨completionDepth F (jointObservation q),
      finite_horizon_stabilizes_at_completionDepth F (jointObservation q)⟩

/- Reverse probe for CAS-A1: the public existential equality yields a finite
depth at which finite agreement forces every indexed future observation to
agree. -/
example
    {X : Type u} {J : Type v} {O : J -> Type w} [Finite X]
    (F : X -> X) (q : (i : J) -> X -> O i) :
    exists m : Nat, forall x y : X,
      finiteHorizonKernel F (jointObservation q) m x y ->
        forall n : Nat, forall i : J,
          q i ((F^[n]) x) = q i ((F^[n]) y) := by
  rcases finite_state_has_stable_depth F q with ⟨m, stableAtM⟩
  refine ⟨m, ?_⟩
  intro x y sameFinite n i
  have sameComplete :
      Setoid.ker (completeItinerary F (jointObservation q)) x y := by
    rw [← stableAtM]
    exact sameFinite
  exact congrFun (congrFun sameComplete n) i

/- Satisfiability probe for CAS-A1: a concrete nontrivial finite carrier has
the promised stable depth. -/
example :
    exists m : Nat,
      finiteHorizonKernel Bool.not
          (jointObservation (fun (_ : Unit) (x : Bool) => x)) m =
        Setoid.ker
          (completeItinerary Bool.not
            (jointObservation (fun (_ : Unit) (x : Bool) => x))) := by
  exact finite_state_has_stable_depth Bool.not
    (fun (_ : Unit) (x : Bool) => x)

/- Trivialization probe for CAS-A1: depth zero is not a universal witness,
even on a four-state carrier. The second coordinate is initially hidden and
is moved into the observed first coordinate after one update. -/
example :
    let update : Bool × Bool -> Bool × Bool := fun x => (x.2, x.2)
    let readout : Unit -> Bool × Bool -> Bool := fun _ x => x.1
    finiteHorizonKernel update (jointObservation readout) 0 ≠
      Setoid.ker (completeItinerary update (jointObservation readout)) := by
  dsimp only
  intro relationsEqual
  have sameAtZero :
      finiteHorizonKernel (fun x : Bool × Bool => (x.2, x.2))
        (jointObservation (fun (_ : Unit) x => x.1)) 0
        (false, false) (false, true) := by
    funext k
    have hk : k = 0 := Fin.eq_zero k
    subst k
    rfl
  have sameComplete :
      Setoid.ker
        (completeItinerary (fun x : Bool × Bool => (x.2, x.2))
          (jointObservation (fun (_ : Unit) x => x.1)))
        (false, false) (false, true) := by
    rw [← relationsEqual]
    exact sameAtZero
  have sameAtOne := congrFun (congrFun sameComplete 1) ()
  simp [completeItinerary, jointObservation] at sameAtOne

#print axioms finite_state_has_stable_depth

end D5.S3.ObserverMemory.PredictionCertificates.FiniteStableDepth
