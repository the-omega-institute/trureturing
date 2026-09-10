import LeanInformationAudit.Census.Publish

open Lean Meta Elab Command LeanInformationAudit DispositionCensus CensusManifest CensusProjection

/-- B1 isolates key accounting from classification/query work. Its row authority
is parseReport's validated frozen set; the emitter separately reads the export
for the report side. This receipt makes no classification or Name-level theorem claim. -/
elab "#census_certificate_benchmark" &"report" reportPath:str &"head" head:str
    &"digest" sha:str &"directory" directory:str : command => do
  let destination : System.FilePath := directory.getString
  let phase (label : String) := IO.FS.writeFile (destination / "benchmark.phase") label
  phase "emission"
  let report ← parseReportDataIO (← IO.FS.readFile reportPath.getString)
  ofExcept <| checkReportBinding head.getString sha.getString report
  ofExcept <| checkFrozenKeys report.headSha report.theorems
  let bindings := destination / "bindings.json"
  IO.FS.writeFile bindings (toJson report.theorems).compress
  let repository ← IO.currentDir
  let emission ← IO.Process.output { cmd := "python3", args := #[
    (repository / "tools/lean-inspector/Census/Certificate/certificate_benchmark.py").toString,
    "--report", reportPath.getString, "--bindings", bindings.toString, "--directory", directory.getString] }
  unless emission.exitCode == 0 do throwError "emission failed: {emission.stderr}"
  let source := destination / "CensusRun/Root.lean"
  let input ← IO.FS.readFile source
  let options := (← getOptions).setBool `Elab.async false
  let checked := source.withExtension "checked.lean"
  let certificate := `CensusRun.accountingCertificate
  phase "compile_kernel"
  let staged ← elaborateBoundSource input (certificateSource input `CensusRun.manifestKeys
      `CensusRun.reportKeys certificate report.theorems.size) source checked `CensusRun.Root options fun env => do
    phase "boundary_axioms"
    liftTermElabM <| checkFinalEnvironment env (some `CensusRun.Root)
    withEnv env <| liftTermElabM do
      bindEmittedManifest report `CensusRun.Root report.theorems `CensusRun.manifest `CensusRun.reportKeys
  phase "boundary_axioms"
  let (data, _) ← readModuleData (checked.withExtension "olean")
  let axioms ← withEnv staged <| collectAxioms certificate
  unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
    throwError "unapproved certificate axioms {axioms}"
  let proposition ← withEnv staged <| liftTermElabM do
    let info ← getConstInfo certificate
    unless info matches .thmInfo _ do throwError "expected serialized kernel theorem"
    let expected ← mkAppM ``CensusKeyManifest.Certificate
      #[mkConst `CensusRun.manifestKeys, toExpr report.theorems.size, mkConst `CensusRun.reportKeys]
    unless ← isDefEq info.type expected do throwError "wrong certificate proposition"
    return toString (← ppExpr info.type)
  withEnv staged <| elabCommand (← `(command| #print axioms $(mkIdent certificate)))
  phase "json"
  let fields := [
    ("head_sha", toJson report.headSha), ("report_sha256", toJson report.reportSha256),
    ("keys", toJson report.theorems.size),
    ("certificate", Json.mkObj [("name", toJson certificate.toString), ("proposition", toJson proposition),
      ("axioms", toJson (axioms.map Name.toString))]),
    ("final_env_imports", toJson (data.imports.map (·.module.toString))),
    ("transitive_imports", toJson (staged.header.moduleNames.filter (· != `CensusRun.Root) |>.map Name.toString))]
  copyFinalArtifacts checked source `CensusRun.Root
  -- Match the publisher's bounded row serialization; the full row JSON need
  -- not coexist with the imported, checked environment in the driver heap.
  let handle ← IO.FS.Handle.mk (destination / "certificate.json.tmp") .write
  handle.putStr "{"
  for (field, value) in fields do
    handle.putStr ((toJson field).compress ++ ":" ++ value.compress ++ ",")
  handle.putStr "\"rows\":["
  for i in [:report.theorems.size] do
    if i > 0 then handle.putStr ","
    handle.putStr (toJson report.theorems[i]!).compress
  handle.putStr "]}\n"
  handle.flush
  IO.FS.rename (destination / "certificate.json.tmp") (destination / "certificate.json")
