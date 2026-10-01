/- L0 原型 -/
import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers

namespace Reg.ContractPrototype.Templates.Intervention
open LeanInformationAudit.Contract
open D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates

def enrollment : TemplateEnrollment (@interventionFiniteRealization) where
  name := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.interventionFiniteRealization
  version := 1
  constructors := #[{
    name := `D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM
    type := D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM }]
  options := Lean.Options.set
    (Lean.Options.set
      (Lean.Options.setBool {} `backward.isDefEq.respectTransparency.types false)
      `maxHeartbeats (2000000 : Nat))
    `maxRecDepth (100000 : Nat)

def observationEnrollment : TemplateEnrollment (@observationFiniteRealization) where
  name := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.observationFiniteRealization
  version := 1
  constructors := #[
    { name := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.CausalDirection
      type := D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.CausalDirection },
    { name := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM
      type := D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM }]
  options := Lean.Options.set
    (Lean.Options.set
      (Lean.Options.setBool {} `backward.isDefEq.respectTransparency.types false)
      `maxHeartbeats (2000000 : Nat))
    `maxRecDepth (100000 : Nat)

end Reg.ContractPrototype.Templates.Intervention
