/- GID: D5/S3/ConceptDynamics/InformationEscape/TemplateShadow
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/TemplateShadow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.spectrum_kernel_equal; instance=D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.spectrumRealization
   digest: Shadow registration regression checks preserve canonical arenas, primitive kernels and statements, with sensitivity witnesses and sealed query evidence. -/

import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscapeCounting.Enumerations
import LeanInformationAudit.SealCommand

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.ConceptDynamics.InformationEscape.TemplateShadow

open RegistrationTemplates
open D5.S3.ConceptDynamics.InformationEscapeArenas
open D5.S3.ConceptDynamics.InformationEscapeRealizations

section Spectrum
open D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope
open FirstThreeArenas
def spectrumRealization := cutRealization SpectrumAtom.index
theorem spectrum_bridge : LegacyPrimitiveRealization spectrumArena
    (Function.Bijective SpectrumAtom.index) spectrumRealization :=
  bijectiveLegacy spectrumArena.toArena SpectrumAtom.index
example : (bijectiveArena spectrumArena.toArena (Fin 5)).toArena = spectrumArena.toArena := rfl
theorem spectrum_kernel_equal : ∀ x y, spectrumRealization.toPrimitiveBundle.agrees x y ↔
    FirstThreeRealizations.spectrumRealization.toPrimitiveBundle.agrees x y := by decide
example : spectrumArena.Law spectrumRealization ↔ Function.Bijective SpectrumAtom.index := Iff.rfl
theorem spectrum_nondegenerate : spectrumArena.toArena.Nondegenerate := by decide
def spectrumEnumeration : Arena.StateEnumeration spectrumArena.toArena := spectrumArena.__state_enumeration
theorem spectrum_lawSensitive : spectrumArena.Law spectrumRealization ∧
    ¬ spectrumArena.Law (cutRealization (fun _ => (0 : Fin 5))) := by
  refine ⟨spectrum_bridge.equivalence.mp spectrum_atom_index_bijective, ?_⟩
  intro h
  exact (by decide : SpectrumAtom.t1 ≠ SpectrumAtom.t2) (h.1 rfl)
example : ¬ spectrumRealization.toPrimitiveBundle.agrees SpectrumAtom.t1 SpectrumAtom.t2 := by decide
register_information_theorem spectrum_atom_index_bijective in spectrumArena
  primitives spectrumRealization.toPrimitiveBundle realization spectrum_bridge
end Spectrum

section Intervention
open D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
open FourthFifthArenas
attribute [local instance] modelFintype modelDecidableEq
def interventionTemplate := separationRealization Int CF
def interventionRealization : PrimitiveRealization interventionSignature where
  readout | .intervention => interventionTemplate.readout false
          | .counterfactual => interventionTemplate.readout true
  anchor := Fin.elim0
theorem intervention_bridge : LegacyPrimitiveRealization interventionArena
    (∃ M N : DeterministicBoolSCM, Int M = Int N ∧ CF M ≠ CF N) interventionRealization :=
  ⟨(separationLegacy interventionArena.toArena Int CF).equivalence⟩
example : (separationArena interventionArena.toArena
    (Bool → Bool → Nat) (Bool → Bool → Bool → Bool)).toArena = interventionArena.toArena := rfl
example : ∀ x y, interventionTemplate.toPrimitiveBundle.agrees x y ↔
    FourthFifthRealizations.interventionRealization.toPrimitiveBundle.agrees x y := by decide
example : interventionArena.Law interventionRealization ↔
    (∃ M N : DeterministicBoolSCM, Int M = Int N ∧ CF M ≠ CF N) := Iff.rfl
theorem intervention_nondegenerate : interventionArena.toArena.Nondegenerate := by decide
def interventionEnumeration : Arena.StateEnumeration interventionArena.toArena :=
  interventionArena.__state_enumeration
theorem intervention_lawSensitive : interventionArena.Law interventionRealization ∧
    ¬ interventionArena.Law ⟨(fun i _ => interventionRealization.readout i noEffectModel), Fin.elim0⟩ := by
  refine ⟨intervention_bridge.equivalence.mp intervention_strictly_weaker_than_counterfactual, ?_⟩
  rintro ⟨x, y, _, h⟩
  exact h rfl
example : ¬ interventionTemplate.toPrimitiveBundle.agrees noEffectModel flipEffectModel := by decide
register_information_theorem intervention_strictly_weaker_than_counterfactual in interventionArena
  primitives interventionRealization.toPrimitiveBundle realization intervention_bridge
end Intervention

section Observation
open D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
open InformationEscapeArenas.ObservationIntervention
def observationTemplate := separationRealization Obs Int
def observationRealization : PrimitiveRealization observationInterventionSignature where
  readout | .observation => observationTemplate.readout false
          | .intervention => observationTemplate.readout true
  anchor := Fin.elim0
theorem observation_bridge : LegacyPrimitiveRealization observationInterventionArena
    ObservationInterventionStatement observationRealization :=
  ⟨(separationLegacy observationInterventionArena.toArena Obs Int).equivalence⟩
example : (separationArena observationInterventionArena.toArena
    (Bool → Bool × Bool) (Bool → Bool → Bool × Bool)).toArena = observationInterventionArena.toArena := rfl
example : ∀ x y, observationTemplate.toPrimitiveBundle.agrees x y ↔
    InformationEscapeRealizations.ObservationIntervention.observationInterventionRealization.toPrimitiveBundle.agrees x y := by decide
example : observationInterventionArena.Law observationRealization ↔ ObservationInterventionStatement := Iff.rfl
theorem observation_nondegenerate : observationInterventionArena.toArena.Nondegenerate := by decide
def observationEnumeration : Arena.StateEnumeration observationInterventionArena.toArena :=
  observationInterventionArena.__state_enumeration
theorem observation_lawSensitive : observationInterventionArena.Law observationRealization ∧
    ¬ observationInterventionArena.Law ⟨(fun i _ => observationRealization.readout i xCausesYModel), Fin.elim0⟩ := by
  refine ⟨observation_bridge.equivalence.mp observation_strictly_weaker_than_intervention, ?_⟩
  rintro ⟨x, y, _, h⟩
  exact h rfl
example : ¬ observationTemplate.toPrimitiveBundle.agrees xCausesYModel yCausesXModel := by decide
register_information_theorem observation_strictly_weaker_than_intervention in observationInterventionArena
  primitives observationRealization.toPrimitiveBundle realization observation_bridge
end Observation

end D5.S3.ConceptDynamics.InformationEscape.TemplateShadow
