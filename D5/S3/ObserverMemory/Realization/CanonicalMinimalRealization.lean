/- GID: D5/S3/ObserverMemory/Realization/CanonicalMinimalRealization
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Realization/CanonicalMinimalRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact realizations factor dynamically onto the itinerary range, degeneracies included. -/

import D5.S3.ObserverMemory.PredictionFactors.CausalStateFactorization
import D5.S3.ObserverMemory.PredictionFactors.PredictionCompletionUniversality

/- Library-search audit trail (2026-08-25):
   * The prescribed repository search for an infinite word found no exact hit because the
     relevant declaration's type is line-broken and its name uses `itinerary`, not `word`.
     Extended repository search found the exact existing definitions `completeItinerary`,
     `ItineraryRange`, and `itineraryUpdate`; they are reused instead of redeclared.
   * Exact repository hit `prediction_completion_universality` factors the complete future
     itinerary through any state map commuting with update and readout; it is applied directly.
   * Exact repository hit `causal_state_factorization` constructs the unique map between the
     two realized images; its factorization component is applied directly.
   * Exact pinned-Mathlib hits `Set.rangeFactorization_surjective` and
     `Function.Surjective.injective_comp_right` prove surjectivity and uniqueness.
   * Repository and pinned-Mathlib searches found no theorem already packaging the induced
     reachable update, the surjective image factor, and left-shift commutation. -/

namespace D5.S3.ObserverMemory.Realization.CanonicalMinimalRealization

open D5.S3.ObserverMemory.Prediction.ItineraryCompletion
open D5.S3.ObserverMemory.PredictionFactors.CausalStateFactorization
open D5.S3.ObserverMemory.PredictionFactors.PredictionCompletionUniversality

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Update commutation makes the realization image invariant under the realized update. -/
theorem realization_range_invariant
    {X S : Type*} (F : X -> X) (R : X -> S) (nu : S -> S)
    (hcommute : forall x, R (F x) = nu (R x)) :
    forall state : Set.range R, nu state.1 ∈ Set.range R := by
  intro state
  rcases state.property with ⟨x, hx⟩
  refine ⟨F x, ?_⟩
  calc
    R (F x) = nu (R x) := hcommute x
    _ = nu state.1 := congrArg nu hx

#print axioms realization_range_invariant

/-- The update induced by `nu` on the reachable part of a realization. -/
def reachableUpdate
    {X S : Type*} (F : X -> X) (R : X -> S) (nu : S -> S)
    (hcommute : forall x, R (F x) = nu (R x)) :
    Set.range R -> Set.range R :=
  fun state =>
    ⟨nu state.1, realization_range_invariant F R nu hcommute state⟩

private theorem itinerary_update_range_factorization
    {X B : Type*} (F : X -> X) (q : X -> B) (x : X) :
    itineraryUpdate F q (Set.rangeFactorization (completeItinerary F q) x) =
      Set.rangeFactorization (completeItinerary F q) (F x) := by
  apply Subtype.ext
  funext n
  simp [itineraryUpdate, completeItinerary, Function.iterate_succ_apply]

/-- Every exact realization has a unique surjective factor from its reachable image onto the
causal-state image. The factor agrees with the complete future itinerary on source states and
intertwines the induced reachable update with left shift. -/
theorem canonical_minimal_realization
    {X S B : Type*} (F : X -> X) (q : X -> B)
    (R : X -> S) (nu : S -> S) (o : S -> B)
    (hcommute : forall x, R (F x) = nu (R x))
    (hreadout : forall x, q x = o (R x)) :
    ∃! pi : Set.range R -> ItineraryRange F q,
      Function.Surjective pi ∧
        Set.rangeFactorization (completeItinerary F q) =
          pi ∘ Set.rangeFactorization R ∧
        pi ∘ reachableUpdate F R nu hcommute = itineraryUpdate F q ∘ pi := by
  have step_factors : R ∘ F = nu ∘ R := by
    funext x
    exact hcommute x
  have readout_factors : q = o ∘ R := by
    funext x
    exact hreadout x
  rcases prediction_completion_universality F q R nu o step_factors readout_factors with
    ⟨completion, completion_factors⟩
  rcases (causal_state_factorization R (completeItinerary F q) completion
      completion_factors).1 with
    ⟨pi, pi_property, _⟩
  have pi_surjective : Function.Surjective pi := by
    intro itinerary
    rcases itinerary.property with ⟨x, hx⟩
    refine ⟨Set.rangeFactorization R x, ?_⟩
    calc
      pi (Set.rangeFactorization R x) =
          Set.rangeFactorization (completeItinerary F q) x :=
        (congrFun pi_property.1 x).symm
      _ = itinerary := Subtype.ext hx
  have pi_update :
      pi ∘ reachableUpdate F R nu hcommute = itineraryUpdate F q ∘ pi := by
    funext state
    rcases state.property with ⟨x, hx⟩
    have state_eq : Set.rangeFactorization R x = state := Subtype.ext hx
    rw [← state_eq]
    calc
      pi (reachableUpdate F R nu hcommute (Set.rangeFactorization R x)) =
          pi (Set.rangeFactorization R (F x)) := by
        apply congrArg pi
        apply Subtype.ext
        exact (hcommute x).symm
      _ = Set.rangeFactorization (completeItinerary F q) (F x) :=
        (congrFun pi_property.1 (F x)).symm
      _ = itineraryUpdate F q
          (Set.rangeFactorization (completeItinerary F q) x) :=
        (itinerary_update_range_factorization F q x).symm
      _ = itineraryUpdate F q (pi (Set.rangeFactorization R x)) :=
        congrArg (itineraryUpdate F q) (congrFun pi_property.1 x)
  refine ⟨pi, ⟨pi_surjective, pi_property.1, pi_update⟩, ?_⟩
  intro candidate candidate_property
  apply Set.rangeFactorization_surjective.injective_comp_right
  exact candidate_property.2.1.symm.trans pi_property.1

#print axioms canonical_minimal_realization

/-- Without exact readout factorization, even commuting dynamics need not admit a map agreeing
with both source itineraries. -/
theorem readout_exactness_is_necessary :
    let F : Bool -> Bool := id
    let q : Bool -> Bool := id
    let R : Bool -> Unit := fun _ => ()
    let nu : Unit -> Unit := id
    let o : Unit -> Bool := fun _ => false
    (forall x, R (F x) = nu (R x)) ∧
      (¬ forall x, q x = o (R x)) ∧
      ¬ ∃ pi : Set.range R -> ItineraryRange F q,
        forall x,
          pi (Set.rangeFactorization R x) =
            Set.rangeFactorization (completeItinerary F q) x := by
  dsimp
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · intro hreadout
    have h := hreadout true
    exact Bool.noConfusion h
  · rintro ⟨pi, pi_factors⟩
    have source_eq :
        Set.rangeFactorization (fun _ : Bool => ()) false =
          Set.rangeFactorization (fun _ : Bool => ()) true := by
      apply Subtype.ext
      rfl
    have target_eq :
        Set.rangeFactorization (completeItinerary (id : Bool -> Bool) id) false =
          Set.rangeFactorization (completeItinerary (id : Bool -> Bool) id) true := by
      calc
        Set.rangeFactorization (completeItinerary (id : Bool -> Bool) id) false =
            pi (Set.rangeFactorization (fun _ : Bool => ()) false) :=
          (pi_factors false).symm
        _ = pi (Set.rangeFactorization (fun _ : Bool => ()) true) :=
          congrArg pi source_eq
        _ = Set.rangeFactorization (completeItinerary (id : Bool -> Bool) id) true :=
          pi_factors true
    have coordinate_eq := congrFun (congrArg Subtype.val target_eq) 0
    have : false = true := by
      simpa [completeItinerary] using coordinate_eq
    exact Bool.noConfusion this

#print axioms readout_exactness_is_necessary

/-- Without update commutation, exact readout factorization does not make the realization image
invariant under the proposed realized update. -/
theorem update_commutation_is_necessary :
    let F : Unit -> Unit := id
    let q : Unit -> Unit := id
    let R : Unit -> Bool := fun _ => false
    let nu : Bool -> Bool := Bool.not
    let o : Bool -> Unit := fun _ => ()
    (forall x, q x = o (R x)) ∧
      (¬ forall x, R (F x) = nu (R x)) ∧
      ¬ forall state : Set.range R, nu state.1 ∈ Set.range R := by
  dsimp
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · intro hcommute
    have h := hcommute ()
    exact Bool.noConfusion h
  · intro hinvariant
    have hmem := hinvariant ⟨false, ⟨(), rfl⟩⟩
    rcases hmem with ⟨x, hx⟩
    have : false = true := by
      simpa using hx
    exact Bool.noConfusion this

#print axioms update_commutation_is_necessary

-- Degeneracy audit: an empty source is accepted without additional hypotheses.
example : True := by
  have _empty_source := canonical_minimal_realization
    (X := Empty) (S := Unit) (B := Unit)
    (id : Empty -> Empty) (fun x : Empty => x.elim)
    (fun x : Empty => x.elim) id id (fun x => x.elim) (fun x => x.elim)
  trivial

-- Degeneracy audit: an empty realization carrier forces, and admits, an empty source.
example : True := by
  have _empty_realization := canonical_minimal_realization
    (X := Empty) (S := Empty) (B := Unit)
    (id : Empty -> Empty) (fun x : Empty => x.elim) id id
    (fun x : Empty => x.elim) (fun x => x.elim) (fun x => x.elim)
  trivial

-- Degeneracy audit: an empty output carrier is consistent when all preceding carriers are empty.
example : True := by
  have _empty_output := canonical_minimal_realization
    (X := Empty) (S := Empty) (B := Empty) id id id id id
    (fun x => x.elim) (fun x => x.elim)
  trivial

-- Degeneracy audit: the one-output case has the expected one-state realization.
example : True := by
  have _one_output := canonical_minimal_realization
    (X := Unit) (S := Unit) (B := Unit) id id id id id
    (fun _ => rfl) (fun _ => rfl)
  trivial

-- Degeneracy audit: the realization map need not be onto its ambient carrier.
example : True := by
  have _nonsurjective_realization := canonical_minimal_realization
    (X := Unit) (S := Bool) (B := Unit) id id (fun _ => false) id
    (fun _ => ()) (fun _ => rfl) (fun _ => rfl)
  trivial

-- Degeneracy audit: identity source dynamics are admitted on a nontrivial carrier.
example : True := by
  have _identity_source_update := canonical_minimal_realization
    (X := Bool) (S := Bool) (B := Bool) id id id id id
    (fun _ => rfl) (fun _ => rfl)
  trivial

-- Degeneracy audit: the realized update may be identity even when the source update is not.
example : True := by
  have _identity_realized_update := canonical_minimal_realization
    (X := Bool) (S := Unit) (B := Unit) Bool.not (fun _ => ())
    (fun _ => ()) id id (fun _ => rfl) (fun _ => rfl)
  trivial

end D5.S3.ObserverMemory.Realization.CanonicalMinimalRealization
