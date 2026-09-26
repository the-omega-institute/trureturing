import LeanInformationAuditInterface.RootContract
import Reg.Support.FixedSnapshot
import Reg.Support.FrozenBaseline

namespace Reg.Support.InformationRootContract
open Lean LeanInformationAudit

-- Independent production expectations, supplied before this root is sealed.
def rootId : Name := `Reg.Catalogs.InformationRoot

-- Preserve the historical snapshots above; transport only the observation/intervention
-- arena address whose state kernel and statement are checked in
-- Reg.Support.LegacyCausalMapping.
def currentOccurrence (row : SnapshotOccurrence) : SnapshotOccurrence :=
  { row with objectArenaName :=
    if row.objectArenaName == `D5.S3.ConceptDynamics.InformationEscapeArenas.ObservationIntervention.observationInterventionArena then
      `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena
    else row.objectArenaName }

def contract : RootCatalogContract := {
  rootId
  expected := Reg.Support.frozenInformationRootBaseline.map currentOccurrence
  source := Reg.Support.fixedInformationSourceSnapshot.occurrences.map currentOccurrence
  baseline := Reg.Support.frozenInformationRootBaseline.map currentOccurrence
  companionPrefix := some rootId }

-- Seal reference after the faithful observation/intervention arena transport.
def expectedSealDigest : String :=
  "f798368c769e9f926f8125492d7ded9586f7be28411d8dcdb567d720c37b80ae"

end Reg.Support.InformationRootContract
