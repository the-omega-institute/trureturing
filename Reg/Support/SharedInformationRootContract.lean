import Reg.Support.InformationRootContract

namespace Reg.Support.SharedInformationRootContract
open Lean LeanInformationAudit

-- The separately enumerated source contains the eleven baseline occurrences
-- and two unified causal transitions; the seal never supplies these inputs.
def rootId : Name := `Reg.Catalogs.SharedInformationRoot

def causalOccurrences : Array SnapshotOccurrence :=
  Reg.Support.fixedInformationSourceSnapshot.occurrences.filter fun row =>
    row.objectArenaName ==
      `D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment.unifiedArena

def contract : RootCatalogContract := {
  rootId
  expected := InformationRootContract.contract.expected ++ causalOccurrences
  source := InformationRootContract.contract.source
  baseline := InformationRootContract.contract.baseline
  companionPrefix := some rootId }

-- Seal reference for the combined finite and lossless context transports.
def expectedSealDigest : String :=
  "2438640b3303fdcc8c622ad046a241e457d90f212afc0c29f044b90f4f8c0764"

end Reg.Support.SharedInformationRootContract
