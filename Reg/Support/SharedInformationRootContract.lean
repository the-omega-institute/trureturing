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

-- Seal reference after the faithful observation/intervention arena transport.
def expectedSealDigest : String :=
  "c13fb34fffb44834e52f466bfa860ed6d7735d9eb1708575ae99875dc02e2f1e"

end Reg.Support.SharedInformationRootContract
