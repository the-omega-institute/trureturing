/- GID: D5/S3/ConceptDynamics/NormativeRequirements/CrossStraitSafeguards
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/NormativeRequirements/CrossStraitSafeguards
   mirror-E: none(waiver:no-empirical-premise-is-certified)
   anchors: []
   utility: none
   digest: Cross-strait endorsement criteria remain conditional on consent, peace, and rights. -/

import D5.S3.ConceptDynamics.NormativeRequirements.NecessarySafeguardObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.NormativeRequirements.CrossStraitSafeguards

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.NormativeRequirements.NecessarySafeguardObstruction

/-- These labels index a chosen evaluative standard, not a legal definition. -/
inductive Safeguard
  | peace
  | consent
  | rights

/-- No actual proposal or population preference is asserted to instantiate
the hypotheses. Consent is the freely expressed consent of Taiwan residents. -/
theorem unification_aim_does_not_replace_consent
    {Proposal : Type*}
    (unificationAim endorsed residentsConsent : Concept Proposal Prop)
    (consentNecessary : ∀ proposal, endorsed proposal -> residentsConsent proposal)
    (proposal : Proposal) (servesAim : unificationAim proposal)
    (lacksConsent : ¬ residentsConsent proposal) :
    ¬ endorsed proposal ∧
      ¬ (∀ candidate, unificationAim candidate -> endorsed candidate) := by
  exact rationale_does_not_supply_necessary_safeguard
    unificationAim endorsed residentsConsent consentNecessary proposal servesAim lacksConsent

/-- If endorsement requires all three safeguards, a failure of any one excludes
endorsement under that standard. The necessity rule is an explicit premise. -/
theorem failed_cross_strait_safeguard_excludes_endorsement
    {Proposal : Type*}
    (endorsed peaceful residentsConsent protectsRights : Concept Proposal Prop)
    (necessary : ∀ proposal, endorsed proposal ->
      peaceful proposal ∧ residentsConsent proposal ∧ protectsRights proposal)
    (proposal : Proposal)
    (failure : ¬ peaceful proposal ∨ ¬ residentsConsent proposal ∨
      ¬ protectsRights proposal) :
    ¬ endorsed proposal := by
  let requirement : Safeguard -> Concept Proposal Prop
    | .peace => peaceful
    | .consent => residentsConsent
    | .rights => protectsRights
  apply violated_requirement_excludes_permission endorsed requirement ?_ proposal ?_
  · intro candidate admitted key
    have safeguards := necessary candidate admitted
    cases key with
    | peace => exact safeguards.1
    | consent => exact safeguards.2.1
    | rights => exact safeguards.2.2
  · rcases failure with noPeace | noConsent | noRights
    · exact ⟨.peace, noPeace⟩
    · exact ⟨.consent, noConsent⟩
    · exact ⟨.rights, noRights⟩

/-- A shared political arrangement cannot determine endorsement when one
proposal is endorsed and another violates a necessary safeguard. -/
theorem unification_outcome_does_not_determine_endorsement
    {Proposal Arrangement : Type*}
    (arrangement : Concept Proposal Arrangement)
    (endorsed safeguard : Concept Proposal Prop)
    (necessary : ∀ proposal, endorsed proposal -> safeguard proposal)
    (consensualProposal failingProposal : Proposal)
    (sameArrangement : arrangement consensualProposal = arrangement failingProposal)
    (accepted : endorsed consensualProposal)
    (failure : ¬ safeguard failingProposal) :
    ¬ ∃ decision : Arrangement -> Prop, endorsed = decision ∘ arrangement := by
  exact necessary_safeguard_blocks_readout_factorization
    arrangement endorsed safeguard necessary
    consensualProposal failingProposal sameArrangement accepted failure

#print axioms unification_aim_does_not_replace_consent
#print axioms failed_cross_strait_safeguard_excludes_endorsement
#print axioms unification_outcome_does_not_determine_endorsement

end D5.S3.ConceptDynamics.NormativeRequirements.CrossStraitSafeguards
