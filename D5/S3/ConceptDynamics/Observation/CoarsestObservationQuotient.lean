/- GID: D5/S3/ConceptDynamics/Observation/CoarsestObservationQuotient
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Observation/CoarsestObservationQuotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The quotient by an observation kernel is the coarsest exact interface, and every accurate surjective readout factors uniquely through it. -/

import Mathlib.Data.Setoid.Basic
import Mathlib.Logic.Function.Basic

/- Library-search audit trail (2026-09-11):
   * `Factor.UniqueInterfaceKernelCriterion` already states the abstract
     existence criterion for a surjective readout and a declared target, but it
     does not construct the canonical quotient or its universal factor.
   * `SufficiencyQuotient.TargetFamilyMinimalQuotient` constructs a quotient
     for a dependent target family, but does not expose the source atom's
     arbitrary accurate-surjection-to-canonical-quotient factorization.
   * No existing declaration at the requested `Observation/` address defines
     this canonical carrier and its unique universal factor. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Observation.CoarsestObservationQuotient

universe u v w

/-- The canonical quotient carrier for an observation. -/
abbrev ObservationQuotient {X : Type u} {O : Type v} (observation : X → O) :=
  Quotient (Setoid.ker observation)

/-- The canonical projection to the observation-kernel quotient. -/
def observationProjection {X : Type u} {O : Type v} (observation : X → O) :
    X → ObservationQuotient observation :=
  Quotient.mk _

/-- The observation descends uniquely to its kernel quotient. -/
theorem observation_quotient_recovers
    {X : Type u} {O : Type v} (observation : X → O) :
    ∃! decoder : ObservationQuotient observation → O,
      observation = decoder ∘ observationProjection observation := by
  let decoder : ObservationQuotient observation → O :=
    Quotient.lift observation (by
      intro left right sameObservation
      exact sameObservation)
  have factorization :
      observation = decoder ∘ observationProjection observation := by
    funext state
    rfl
  refine ⟨decoder, factorization, ?_⟩
  intro candidate candidateFactorization
  funext quotientState
  induction quotientState using Quotient.inductionOn with
  | _ state =>
      have candidateValue := congrFun candidateFactorization state
      have decoderValue := congrFun factorization state
      exact candidateValue.symm.trans decoderValue

/-- Every accurate surjective readout factors uniquely through the canonical
observation-kernel quotient. -/
theorem accurate_surjective_readout_factors
    {X : Type u} {O : Type v} {Q : Type w}
    (observation : X → O) (readout : X → Q)
    (readout_surjective : Function.Surjective readout)
    (decoder : Q → O)
    (accurate : observation = decoder ∘ readout) :
    ∃! factor : Q → ObservationQuotient observation,
      observationProjection observation = factor ∘ readout := by
  let representative : Q → X := Function.surjInv readout_surjective
  have representativeRight : Function.RightInverse representative readout :=
    Function.rightInverse_surjInv readout_surjective
  let factor : Q → ObservationQuotient observation :=
    fun value => Quotient.mk _ (representative value)
  have factorization :
      observationProjection observation = factor ∘ readout := by
    funext state
    change Quotient.mk _ state = Quotient.mk _ (representative (readout state))
    apply Quotient.sound
    have readout_equal :
        readout state = readout (representative (readout state)) :=
      (representativeRight (readout state)).symm
    change observation state = observation (representative (readout state))
    calc
      observation state = decoder (readout state) := congrFun accurate state
      _ = decoder (readout (representative (readout state))) :=
        congrArg decoder readout_equal
      _ = observation (representative (readout state)) :=
        (congrFun accurate (representative (readout state))).symm
  refine ⟨factor, factorization, ?_⟩
  intro other otherFactorization
  funext value
  obtain ⟨state, rfl⟩ := readout_surjective value
  have otherValue := congrFun otherFactorization state
  have factorValue := congrFun factorization state
  exact otherValue.symm.trans factorValue

#print axioms observation_quotient_recovers
#print axioms accurate_surjective_readout_factors

end D5.S3.ConceptDynamics.Observation.CoarsestObservationQuotient
