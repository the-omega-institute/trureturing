import LeanInformationAuditInterface.RootContract
import Reg.Support.FixedSnapshot
import Reg.Support.FrozenBaseline

namespace Reg.Support.InformationRootContract
open Lean LeanInformationAudit

-- Independent production expectations, supplied before this root is sealed.
def rootId : Name := `Reg.Catalogs.InformationRoot

-- Preserve historical snapshots; each current arena has a complete statement
-- bridge and proved kernel correspondence in its Reg support module.
def currentOccurrence (row : SnapshotOccurrence) : SnapshotOccurrence :=
  { row with objectArenaName :=
    if row.objectArenaName == `D5.S3.ConceptDynamics.InformationEscapeArenas.ObservationIntervention.observationInterventionArena then
      `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena
    else if row.objectArenaName == `D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.agendaPowerArena then
      `Reg.Support.LegacyAgenda.arena
    else if row.objectArenaName == `D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.residueArena then
      `Reg.Support.LegacyResidue.arena
    else if row.objectArenaName == `D5.S3.ConceptDynamics.InformationEscapeArenas.StaticExactExperimentDesign.staticExactExperimentArena then
      `Reg.Support.LegacyStaticDesign.arena
    else if row.objectArenaName == `D5.S3.ConceptDynamics.InformationEscapeArenas.LocalLawGluingObstruction.localLawGluingArena then
      `Reg.Support.LegacyGluing.arena
    else if row.objectArenaName == `D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.contextArena then
      `Reg.Support.LegacyContextReplacement.objectArena
    else if row.objectArenaName == `D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.interventionArena then
      `Reg.Support.LegacyCausalCoordinates.icObjectArena
    else if row.objectArenaName == `D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment.unifiedArena then
      `Reg.Support.LegacyCausalCoordinates.objectArena
    else row.objectArenaName }

def contract : RootCatalogContract := {
  rootId
  expected := Reg.Support.frozenInformationRootBaseline.map currentOccurrence
  source := Reg.Support.fixedInformationSourceSnapshot.occurrences.map currentOccurrence
  baseline := Reg.Support.frozenInformationRootBaseline.map currentOccurrence
  companionPrefix := some rootId }

-- Seal reference after the faithful finite arena transports.
def expectedSealDigest : String :=
  "10d7a7bee7c78e925a53ac2b379d2d3fc00545193cf0ab22dd1a76159bd58e30"

end Reg.Support.InformationRootContract
