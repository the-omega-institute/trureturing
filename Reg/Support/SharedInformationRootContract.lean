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

-- Independently translated from the existing D5 seal: only catalog, verdict,
-- unit and certificate names change to this root's generated names.
def expectedSealDigest : String :=
  "f38a50d6a9696940e04d8368b1c2d6d5f9491b990b94f9083b81f757c7cbbb88"

end Reg.Support.SharedInformationRootContract
