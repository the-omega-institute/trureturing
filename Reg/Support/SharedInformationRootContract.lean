import Reg.Support.InformationRootContract

namespace Reg.Support.SharedInformationRootContract
open Lean LeanInformationAudit

-- The separately enumerated source contains the eleven baseline occurrences
-- and two unified causal transitions; the seal never supplies these inputs.
def rootId : Name := `Reg.Catalogs.SharedInformationRoot

def causalOccurrences : Array SnapshotOccurrence :=
  (Reg.Support.fixedInformationSourceSnapshot.occurrences.filter fun row =>
    row.objectArenaName ==
      `D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment.unifiedArena).map InformationRootContract.currentOccurrence

def contract : RootCatalogContract := {
  rootId
  expected := InformationRootContract.contract.expected ++ causalOccurrences
  source := InformationRootContract.contract.source
  baseline := InformationRootContract.contract.baseline
  companionPrefix := some rootId }

-- Seal reference for the combined finite and lossless context transports.
def expectedSealDigest : String :=
  "25105046611fa8c42d96f1e62b51c732a37c092d2c9a1c1310f4145bd215797f"

end Reg.Support.SharedInformationRootContract
