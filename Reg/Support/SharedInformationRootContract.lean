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
  "ebfbc7633da209a2a2e788a578d2ef6b463ceb9e59d90bf2f91e81d48795e8e5"

end Reg.Support.SharedInformationRootContract
