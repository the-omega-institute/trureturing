import LeanInformationAudit.SealCommand

open D5.S3.ConceptDynamics.Aggregation.AgendaPower
open D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas
open D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations

namespace LeanInformationAudit.Tests.Seal.ReflectedRoute

set_option maxRecDepth 100000

register_information_theorem
  agenda_power
  in agendaPowerArena
  primitives agendaPowerRealization.toPrimitiveBundle
  realization agenda_power_realization

/-- info: information seal: arena=D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.agendaPowerArena theorem=D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power unique=570 method=reflected-fused-counts -/
#guard_msgs (info) in
#seal_information_theory

end LeanInformationAudit.Tests.Seal.ReflectedRoute
