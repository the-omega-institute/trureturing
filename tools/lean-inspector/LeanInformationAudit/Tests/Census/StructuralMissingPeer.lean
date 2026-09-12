import LeanInformationAudit.Tests.Census.StructuralTrivial
open Lean Meta Lean.Elab.Command LeanInformationAudit DispositionCensus
open LeanInformationAudit.Tests.Census.StructuralTrivial
structural_theorem newPeer in law realization readouts nondegeneracy nondegenerate := fun _ => rfl
run_cmd liftTermElabM do
  let env ← getEnv
  let key : StatementKey := ⟨``member, theoremStatementIdentity env ``member⟩
  let mut rejected := false
  try discard <| CensusQuery.assess (← CensusQuery.indexScope env.header.mainModule) "fixture-head" key
  catch error => rejected := (← error.toMessageData.toString).endsWith "invalid=maximal_catalog_membership"
  unless rejected do throwError "StructuralMissingPeer: stale catalog accepted"
