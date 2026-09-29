import Reg.Support.LegacyCausalSlots
import Reg.Support.CausalSourceFamily

/- Full original statements and lawful transports, isolated from production
catalogs. This fixture exposes the current finite extraction boundary. -/
namespace LeanInformationAuditRegTests.LegacyCausalBindingBoundary
open Reg.Support.LegacyCausalCoordinates Reg.Support.LegacyCausalSlots LeanInformationAudit

namespace Candidate0
register_information_theorem _root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual
  in Reg.Support.LegacyCausalSlots.localDomainArena
  object_arena icObjectArena catalog Reg.Support.LegacyCausalCoordinates.icObjectArena
  readout via (slotRealization (fun i x =>
    let c := icInt x
    let f := icCF x
    choose i slot0 c.1
      (choose i slot1 c.2.1
      (choose i slot2 c.2.2.1
      (choose i slot3 c.2.2.2
      (choose i slot4 f.1
      (choose i slot5 f.2.1
      (choose i slot6 f.2.2.1
      (f.2.2.2)))))))))
  primitives Reg.Support.LegacyCausalSlots.localActual.toPrimitiveBundle
    realization Reg.Support.LegacyCausalSlots.local_bridge
  variation Reg.Support.LegacyCausalSlots.local_variation
    sensitivity Reg.Support.LegacyCausalSlots.local_sensitivity
  escape from (_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) escape continues (open)

end Candidate0

namespace Candidate1
register_information_theorem _root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual
  in Reg.Support.LegacyCausalSlots.icDomainArena
  object_arena objectArena catalog «causal-unified-transitions»
  readout via (slotRealization (fun i x =>
    let c := spread (icCoarse x)
    let f := spread (icFine x)
    choose i slot0 c.1
      (choose i slot1 c.2.1
      (choose i slot2 c.2.2.1
      (choose i slot3 c.2.2.2
      (choose i slot4 f.1
      (choose i slot5 f.2.1
      (choose i slot6 f.2.2.1
      (f.2.2.2)))))))))
  primitives Reg.Support.LegacyCausalSlots.icActual.toPrimitiveBundle
    realization Reg.Support.LegacyCausalSlots.ic_bridge
  variation Reg.Support.LegacyCausalSlots.ic_variation
    sensitivity Reg.Support.LegacyCausalSlots.ic_sensitivity
  escape from (_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) escape continues (open)

end Candidate1

namespace Candidate2
register_information_theorem _root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention
  in Reg.Support.LegacyCausalSlots.oiDomainArena
  object_arena objectArena catalog «causal-unified-transitions»
  readout via (slotRealization (fun i x =>
    let c := spread (oiCoarse x)
    let f := spread (oiFine x)
    choose i slot0 c.1
      (choose i slot1 c.2.1
      (choose i slot2 c.2.2.1
      (choose i slot3 c.2.2.2
      (choose i slot4 f.1
      (choose i slot5 f.2.1
      (choose i slot6 f.2.2.1
      (f.2.2.2)))))))))
  primitives Reg.Support.LegacyCausalSlots.oiActual.toPrimitiveBundle
    realization Reg.Support.LegacyCausalSlots.oi_bridge
  variation Reg.Support.LegacyCausalSlots.oi_variation
    sensitivity Reg.Support.LegacyCausalSlots.oi_sensitivity
  escape from (_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) escape continues (open)

end Candidate2

open Lean Meta in
run_meta do
  let env ← getEnv
  let events := (TemplateBinding.inventory env).filter
    (·.key.registrationModule == env.header.mainModule)
  unless events.size == 3 do throwError "expected three complete causal boundary cases"
  for event in events do
    let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
      | throwError "missing complete causal candidate"
    let record ← TemplateBinding.assess event (some claim)
    let wire := (← TemplateBinding.recordJson record).compress
    unless wire.contains "incomplete_closure" && wire.contains "E8.work" do
      throwError "causal boundary changed; reassess the historical occurrences: {wire}"
  logInfo "[BOUNDARY] three full original causal candidates reach E8.work; no impossibility claim"

end LeanInformationAuditRegTests.LegacyCausalBindingBoundary
