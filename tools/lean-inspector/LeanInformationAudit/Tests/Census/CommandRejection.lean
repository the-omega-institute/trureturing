import LeanInformationAudit.Tests.Census.Evidence
import LeanInformationAudit.Tests.Census.Coverage

open Lean LeanInformationAudit DispositionCensus
open Lean.Elab.Command

namespace LeanInformationAudit.Tests.Census

private def censusReportInput (inventory : DispositionInventory) : Json := Json.mkObj [
  ("schema", toJson "stratalint.truth-export"), ("schema_version", toJson (2 : Nat)),
  ("dialect", toJson "stratalint.truth-export.v2"),
  ("producer", toJson "TruthExportCommand"), ("source_commit", toJson inventory.headSha),
  ("nodes", Json.arr #[Json.mkObj [("freeze_status", toJson "frozen"),
    ("declarations", Json.arr <| inventory.entries.map fun row => Json.mkObj [
      ("kind", toJson "theorem"),
      ("declaration_name_key", toJson (encodeNameKey row.1.theoremName)),
      ("statement_id", toJson row.1.statementId)])]])]

/-- Exercise successful publication and inspect its count and kernel certificate. -/
def expectAcceptedCensus (root inventoryName certificate : Name)
    (inventory : DispositionInventory) (structuralCount : Nat)
    (assessmentCounts : Option (Nat × Nat × Nat × Bool) := none) : CommandElabM Unit :=
  IO.FS.withTempDir fun dir => do
    let bytes := (censusReportInput inventory).compress
    let reportPath := dir / "report.json"
    let outputPath := dir / "census.json"
    IO.FS.writeFile reportPath bytes
    let input := Syntax.mkStrLit reportPath.toString
    let destination := Syntax.mkStrLit outputPath.toString
    let head := Syntax.mkStrLit inventory.headSha
    let digest := Syntax.mkStrLit ("sha256:" ++ Sha256.hex bytes.toUTF8)
    let rootId := mkIdent root
    let inventoryId := mkIdent inventoryName
    let certificateId := mkIdent certificate
    elabCommand (← `(command|
      #disposition_census root $rootId report $input head $head report_sha256 $digest
        inventory $inventoryId certificate $certificateId output $destination))
    let projection ← ofExcept <| Json.parse (← IO.FS.readFile outputPath)
    let counts ← ofExcept <| projection.getObjVal? "counts"
    unless (← ofExcept <| counts.getObjValAs? Nat "structural_occurrence") == structuralCount do
      throwError "unexpected structural count: {counts.compress}"
    if let some (accounted, certified, observed, complete) := assessmentCounts then
      for (field, expected) in [("accounted", accounted), ("certified", certified),
          ("observed", observed), ("observed_query_completed", observed),
          ("observed_query_incomplete", 0)] do
        unless (← ofExcept <| counts.getObjValAs? Nat field) == expected do
          throwError "unexpected assessment count: {field} {counts.compress}"
      unless (← ofExcept <| projection.getObjValAs? Bool "certified_complete") == complete do
        throwError "unexpected certified_complete"
    let sources ← ofExcept <| projection.getObjValAs? (Array Json) "source_inputs"
    let env ← getEnv
    let expectedModules := inventory.entries.toList.filterMap fun row =>
      if row.2.className == "structural_occurrence" then
        some (((env.getModuleIdxFor? row.1.theoremName).map
          (env.header.moduleNames[·.toNat]!)).getD env.header.mainModule).toString
      else none
    let modules ← sources.toList.mapM fun (source : Json) =>
      Lean.ofExcept <| source.getObjValAs? String "module"
    unless modules == expectedModules.eraseDups.mergeSort (· < ·) do
      throwError "incorrect structural source input closure"
    for source in sources do
      let path ← ofExcept <| source.getObjValAs? String "path"
      let digest ← ofExcept <| source.getObjValAs? String "sha256"
      unless digest == "sha256:" ++ Sha256.hex (← IO.FS.readBinFile path) do
        throwError "incorrect structural source hash"
    liftTermElabM do
      let name := (← getCurrNamespace) ++ certificate
      Lean.Meta.checkWithKernel (← Lean.Meta.mkConstWithFreshMVarLevels name)
      unless (← Lean.collectAxioms name).all
          (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
        throwError "unexpected coverage axioms"
    logInfo m!"accepted=true structural={structuralCount} certificate-kernel-checked=true"

/-- Check the public command's diagnostic and both publication boundaries. -/
def expectRejectedCensus (root inventoryName certificate : Name)
    (inventory : DispositionInventory) (expected : String)
    (transformReport : Json → Json := id) : CommandElabM Unit :=
  IO.FS.withTempDir fun dir => do
    let bytes := (transformReport (censusReportInput inventory)).compress
    let reportPath := dir / "report.json"
    let outputPath := dir / "census.json"
    IO.FS.writeFile reportPath bytes
    let input := Syntax.mkStrLit reportPath.toString
    let destination := Syntax.mkStrLit outputPath.toString
    let head := Syntax.mkStrLit inventory.headSha
    let digest := Syntax.mkStrLit ("sha256:" ++ Sha256.hex bytes.toUTF8)
    let rootId := mkIdent root
    let inventoryId := mkIdent inventoryName
    let certificateId := mkIdent certificate
    let before ← get
    elabCommand (← `(command|
      #disposition_census root $rootId report $input head $head report_sha256 $digest
        inventory $inventoryId certificate $certificateId output $destination))
    let messages := (← get).messages.toList.drop before.messages.toList.length
    let errors := messages.filter (·.severity == .error)
    let rejected := errors.length == 1 && (← errors.allM fun message => do
      pure ((← message.data.toString) == expected))
    modify fun state => { state with messages := before.messages }
    let outputAbsent := !(← outputPath.pathExists)
    let certificateName := (← getCurrNamespace) ++ certificate
    let certificateAbsent := !(← getEnv).contains certificateName
    unless outputAbsent do
      let projection ← ofExcept <| Json.parse (← IO.FS.readFile outputPath)
      let counts ← ofExcept <| projection.getObjVal? "counts"
      logInfo m!"accepted-output counts={counts.compress}"
    unless certificateAbsent do
      liftTermElabM do
        Lean.Meta.checkWithKernel (← Lean.Meta.mkConstWithFreshMVarLevels certificateName)
        let axioms ← Lean.collectAxioms certificateName
        unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
          throwError "unexpected coverage axioms: {axioms}"
        logInfo m!"accepted-certificate kernel-checked=true axioms={axioms}"
    unless rejected && outputAbsent && certificateAbsent do
      throwError "rejected={rejected} output-absent={outputAbsent} \
        certificate-absent={certificateAbsent} diagnostics={← errors.mapM (·.data.toString)}"
    logInfo expected
    logInfo "rejected=true output-absent=true certificate-absent=true"

private def replaceReportNodes (nodes : Array Json) (report : Json) : Json :=
  report.setObjVal! "nodes" (Json.arr nodes)

private def expectRejectedReport (certificate : Name) (component expected actual : String)
    (transformReport : Json → Json) : CommandElabM Unit :=
  expectRejectedCensus `LeanInformationAudit.Tests.Census.Evidence
    `LeanInformationAudit.Tests.Census.Evidence.inventory certificate Evidence.inventory
    (censusError "fixture-head" component expected actual) transformReport

run_cmd do
  expectRejectedReport `wrongDialect "dialect" "stratalint.truth-export.v2"
    "unsupported-dialect" (fun report => report.setObjVal! "dialect" (toJson "unsupported-dialect"))

/--
info: IE-C044 DispositionCensusMismatch head=fixture-head component=dialect expected=stratalint.truth-export.v2 actual=stratalint.truth-export.v1
---
info: rejected=true output-absent=true certificate-absent=true
-/
#guard_msgs in
run_cmd do
  expectRejectedReport `legacyDialect "dialect" "stratalint.truth-export.v2"
    "stratalint.truth-export.v1" (fun report =>
      (report.setObjVal! "dialect" (toJson "stratalint.truth-export.v1")).setObjVal!
        "schema_version" (toJson (1 : Nat)))

/--
info: IE-C044 DispositionCensusMismatch head=fixture-head component=schema_version expected=2 actual=0
---
info: rejected=true output-absent=true certificate-absent=true
-/
#guard_msgs in
run_cmd do
  expectRejectedReport `wrongSchema "schema_version" "2" "0"
    (fun report => report.setObjVal! "schema_version" (toJson (0 : Nat)))

/--
info: IE-C044 DispositionCensusMismatch head=fixture-head component=freeze_status expected=frozen|proven-not-yet-frozen actual=missing-or-invalid
---
info: rejected=true output-absent=true certificate-absent=true
-/
#guard_msgs in
run_cmd do
  expectRejectedReport `missingFreezeStatus "freeze_status"
    "frozen|proven-not-yet-frozen" "missing-or-invalid"
    (replaceReportNodes #[Json.mkObj [("declarations", Json.arr #[])]])

/--
info: IE-C044 DispositionCensusMismatch head=fixture-head component=freeze_status expected=frozen|proven-not-yet-frozen actual=unknown
---
info: rejected=true output-absent=true certificate-absent=true
-/
#guard_msgs in
run_cmd do
  expectRejectedReport `unknownFreezeStatus "freeze_status"
    "frozen|proven-not-yet-frozen" "unknown"
    (replaceReportNodes #[Json.mkObj [("freeze_status", toJson "unknown"),
      ("declarations", Json.arr #[])]])

/--
info: IE-C044 DispositionCensusMismatch head=fixture-head component=freeze_status expected=frozen|proven-not-yet-frozen actual=missing-or-invalid
---
info: rejected=true output-absent=true certificate-absent=true
-/
#guard_msgs in
run_cmd do
  expectRejectedReport `invalidFreezeStatus "freeze_status"
    "frozen|proven-not-yet-frozen" "missing-or-invalid"
    (replaceReportNodes #[Json.mkObj [("freeze_status", toJson (0 : Nat)),
      ("declarations", Json.arr #[])]])

private def duplicateReportNodes (secondName : Name) : Array Json :=
  #[`Fixture.duplicate, secondName].map fun name => Json.mkObj [
    ("freeze_status", toJson "frozen"),
    ("declarations", Json.arr #[Json.mkObj [("kind", toJson "theorem"),
      ("declaration_name_key", toJson (encodeNameKey name)),
      ("statement_id", toJson "sha256:000000000000000000000000000000000000000000000000000000000000001d")]])]

run_cmd do
  expectRejectedReport `duplicateFrozenKey "frozen_keys" "unique"
    (toJson (StatementKey.mk `Fixture.duplicate "sha256:000000000000000000000000000000000000000000000000000000000000001d")).compress
    (replaceReportNodes (duplicateReportNodes `Fixture.duplicate))

run_cmd do
  expectRejectedReport `duplicateFrozenId "frozen_keys" "unique"
    (toJson (StatementKey.mk `Fixture.other "sha256:000000000000000000000000000000000000000000000000000000000000001d")).compress
    (replaceReportNodes (duplicateReportNodes `Fixture.other))

private def repeatedNameInventory : DispositionInventory := ⟨"fixture-head", #[
  ⟨⟨`Fixture.repeated, "sha256:0000000000000000000000000000000000000000000000000000000000000040"⟩, .certified <| .unreachable ⟨.noCanonicalObjectCarrier, `Evidence⟩⟩,
  ⟨⟨`Fixture.repeated, "sha256:0000000000000000000000000000000000000000000000000000000000000041"⟩, .certified <| .unreachable ⟨.noCanonicalObjectCarrier, `Evidence⟩⟩]⟩

/-- info: Except.ok 2 -/
#guard_msgs in
#eval do
  let bytes := (censusReportInput repeatedNameInventory).compress
  let report ← parseReport "fixture-head" ("sha256:" ++ Sha256.hex bytes.toUTF8) bytes
  return report.theorems.size

/-- info: Except.ok () -/
#guard_msgs in
#eval checkCoverage "fixture-head" repeatedNameInventory.keys.toArray repeatedNameInventory

run_cmd liftTermElabM do
  let report : FrozenReport := ⟨"fixture-head", "digest", repeatedNameInventory.keys.toArray⟩
  discard <| coverageProof report repeatedNameInventory

end LeanInformationAudit.Tests.Census
