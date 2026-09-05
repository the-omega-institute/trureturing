import D5.S3.ConceptDynamics.InformationEscape.InformationRoot

open D5.S3.ConceptDynamics.Aggregation.AgendaPower
open D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas

namespace LeanInformationAudit.Tests.V2Baseline

example : agendaPowerArena.__information_catalog.uniqueCaptureCount (0 : Fin 1) = 570 := by
  decide

#check agenda_power.__lowers_escape
#check agendaPowerArena.__catalog_irredundant
#print axioms agenda_power.__lowers_escape
#print axioms agendaPowerArena.__catalog_irredundant

end LeanInformationAudit.Tests.V2Baseline
