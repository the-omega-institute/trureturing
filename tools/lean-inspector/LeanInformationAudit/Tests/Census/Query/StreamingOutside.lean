import LeanInformationAudit.Census.Query
import LeanInformationAudit.Tests.Census.Query.StreamingTarget

open Lean LeanInformationAudit DispositionCensus

namespace LeanInformationAudit.Tests.Census.Query.StreamingOutside

theorem obligation : ClosedNumericalObligation ``StreamingTarget.target (2 + 3) 5 :=
  ⟨StreamingTarget.target⟩

def evidence : UnreachableElaborationEvidence (2 + 3 = 5) where
  reason := .noCanonicalObjectCarrier
  candidateArena := none
  explanation := "Valid evidence outside the source root's import closure."
  failedObligation := some ``obligation

run_cmd Lean.Elab.Command.liftTermElabM do
  let key := StatementKey.mk ``StreamingTarget.target ("sha256:" ++ String.ofList (List.replicate 64 '0'))
  let outside ← CensusQuery.indexScope `LeanInformationAudit.Tests.Census.Query.StreamingTarget
  let .observed _ ← CensusQuery.assess outside "fixture-head" key
    | throwError "streamOutsideRoot: out-of-scope evidence certified"
  let inside ← CensusQuery.indexScope (← getEnv).header.mainModule
  let .certified (.unreachable _) ← CensusQuery.assess inside "fixture-head" key
    | throwError "streamInsideRoot: valid control evidence did not certify"

end LeanInformationAudit.Tests.Census.Query.StreamingOutside
