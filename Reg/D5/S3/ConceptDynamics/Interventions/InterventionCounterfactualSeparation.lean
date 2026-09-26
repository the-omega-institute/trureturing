import Reg.Support.CausalSourceFamily
import Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.InformationRoot
import Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.SharedArenaPeers
import Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.TemplateShadow
import Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.UnifiedCausalRegistration


namespace Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.SourceFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
open Reg.Support.CausalSourceFamily
open LeanInformationAudit

/-- An additional source-family occurrence preserves the complete original statement. -/
noncomputable def registration : Registration separationArena (Separation actual) where
  actual := actual
  bridge := Iff.rfl
  variation := separation_variation
  sensitivity := separation_sensitivity
  dependence := dependence

register_information_theorem intervention_strictly_weaker_than_counterfactual in separationArena
  readout via (realize signature actual.readout actual.anchor)
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
    coordinates := #[]
    readouts := #[
      { path := #["arg", "body", "arg", "body", "arg", "fn", "arg"], stateBinder := 0 },
      { path := #["arg", "body", "arg", "body", "fn", "arg", "fn", "arg"], stateBinder := 0 }] })
  escape continues (open)

#print axioms registration
end Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.SourceFamily
