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
    else row.objectArenaName }

def contract : RootCatalogContract := {
  rootId
  expected := Reg.Support.frozenInformationRootBaseline.map currentOccurrence
  source := Reg.Support.fixedInformationSourceSnapshot.occurrences.map currentOccurrence
  baseline := Reg.Support.frozenInformationRootBaseline.map currentOccurrence
  companionPrefix := some rootId }

-- Seal reference after the faithful finite arena transports.
def expectedSealDigest : String :=
  "8db3b830b9de6b17c35d317868e6640ca91e92c1be627cd0fe4aff0d053df4af"

end Reg.Support.InformationRootContract
