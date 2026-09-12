import LeanInformationAudit.Tests.Census.StructuralTrivial
import LeanInformationAudit.Census.Command
import LeanInformationAudit.Tests.Projection.FixtureState
open Lean Meta Lean.Elab.Command LeanInformationAudit DispositionCensus
open LeanInformationAudit.Tests.Projection
run_cmd do
  let reportPath ← fixturePath "trivial-source-report.json"
  let request ← fixturePath "trivial-source-request.json"
  let metadata ← fixturePath "trivial-source-index.json"
  let destination ← fixturePath "trivial-source-output.json"
  liftTermElabM do
    let env ← getEnv
    let index ← CensusQuery.indexScope env.header.mainModule
    let owner := "LeanInformationAudit.Tests.Census.StructuralTrivial"
    let name := `LeanInformationAudit.Tests.Census.StructuralTrivial.member
    let key := #[owner, "ns(ns(ns(ns(ns(n0,20:LeanInformationAudit),5:Tests),6:Census),17:StructuralTrivial),6:member)", theoremStatementIdentity env name]
    let report := Json.mkObj [("schema", "stratalint.truth-export"), ("schema_version", toJson (2 : Nat)),
      ("dialect", "stratalint.truth-export.v2"), ("producer", "TruthExportCommand"),
      ("source_commit", "fixture-head"), ("nodes", toJson #[Json.mkObj [
        ("repo_path", "LeanInformationAudit/Tests/Census/StructuralTrivial.lean"),
        ("freeze_status", "frozen"), ("declarations", toJson #[Json.mkObj [
          ("kind", "theorem"), ("declaration_name_key", toJson key[1]!),
          ("statement_id", toJson key[2]!) ]])]])]
    IO.FS.writeFile reportPath report.compress
    IO.FS.writeFile request (Json.mkObj [("head", "fixture-head"), ("keys", toJson #[key]),
      ("report", toJson reportPath), ("report_sha256", ← CensusReceipt.hashReportBytes report.compress)]).compress
    let named := index.named.toList.flatMap fun (head, names) => names.toList.map fun n =>
      Json.mkObj [("head", toJson head.toString), ("name", nameJson n),
        ("module", toJson (CensusQuery.owningModule env n).toString)]
    IO.FS.writeFile metadata (Json.mkObj [("candidate_keys", toJson #[key]), ("named", toJson named),
      ("assignment", Json.mkObj [(owner, toJson index.root.toString)]),
      ("scopes", toJson #[(index.root.toString, index.modules.map Name.toString)]),
      ("batch_module_bound", toJson (env.header.moduleNames.size + 1)),
      ("batch_key_bound", toJson (1 : Nat))]).compress
  elabCommand (← `(command| #census_validate $(Syntax.mkStrLit request):str using
    $(Syntax.mkStrLit metadata):str output $(Syntax.mkStrLit destination):str))
  let json ← ofExcept <| Json.parse (← IO.FS.readFile destination)
  let rows ← ofExcept <| json.getObjValAs? (Array Json) "entries"
  let sources ← ofExcept <| json.getObjValAs? (Array Json) "source_inputs"
  let keyed ← ofExcept <| json.getObjValAs? (Array (String × Array Json)) "key_source_inputs"
  unless rows.size == 1 && (rows[0]!.getObjValAs? String "class").toOption == some "trivial_in_catalog" &&
      sources.size == 1 && keyed.size == 1 && keyed[0]!.2 == sources do
    throwError "StructuralSources: production command drops trivial source closure"
