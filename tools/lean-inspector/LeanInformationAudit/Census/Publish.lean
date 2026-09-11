import LeanInformationAudit.Census.Manifest
import LeanInformationAudit.Census.Transport

namespace LeanInformationAudit.CensusProjection

open Lean Meta Elab Command DispositionCensus CensusManifest

private def isBucketModule (root module : Name) : Bool :=
  let modulePrefix := root.getPrefix.toString ++ ".Range"
  let suffix := (module.toString.drop modulePrefix.length).toString
  module.toString.startsWith modulePrefix && !suffix.isEmpty &&
    suffix.toList.all (fun c => c.isDigit || c == '_')

/-- Check the source boundary and the complete imported closure. A compiled
source is loaded through its own module; only that exact module is excluded
from the dependency closure, after its direct imports have been checked. -/
def checkFinalEnvironment (env : Environment) (compiledRoot : Option Name := none) : CoreM Unit := do
  let expected := #[compiledRoot.getD `LeanInformationAudit.Census.Certificate]
  unless (env.header.imports.map (·.module)).filter (· != `Init) == expected do
    throwError "finalEnvironmentImports: final source must import only Census.Certificate"
  for module in env.header.moduleNames do
    if module.getRoot != `Init && module != `LeanInformationAudit.Census.Certificate &&
        some module != compiledRoot && !(compiledRoot.any (isBucketModule · module)) then
      throwError "finalEnvironmentImports: payload import {module}"

private def checkSourceImports (imports : Array Import) (root : Name) : IO Unit := do
  let names := (imports.map (·.module)).filter (· != `Init)
  unless !names.isEmpty && names.all
      (fun m => m == `LeanInformationAudit.Census.Certificate || isBucketModule root m) do
    throw <| IO.userError "finalEnvironmentImports: final source must import only Census.Certificate"

/-- Compile each bounded leaf and each two-child composition separately from the
driver's Mathlib/Lean heap. Import the exported tree; the binder reads private
leaf declarations one leaf at a time. The source and olean remain reviewable. -/
def elaborateFinalSource (input : String) (fileName : String) (root : Name)
    (options : Options) (dataOnly : Bool := false) : IO Environment := do
  let input := input
  let (imports, _, messages) ← Elab.parseImports input fileName
  if messages.hasErrors then throw <| IO.userError "finalEnvironmentImports: invalid import header"
  checkSourceImports imports root
  let source : System.FilePath := fileName
  let directory := source.withExtension "compile"
  let compiledSource := directory / (System.mkFilePath (root.components.map Name.toString)).withExtension "lean"
  IO.FS.createDirAll compiledSource.parent.get!
  let dataInput := String.intercalate "\n" <| (input.splitOn "\n").filter (!·.startsWith "public theorem ")
  IO.FS.writeFile compiledSource (if dataOnly then dataInput else input)
  let target := compiledSource.withExtension "olean"
  -- Resolve Certificate once, then avoid probing every Mathlib/package path
  -- for each Init import in the compiler and exported-environment reader.
  let certificateModule := `LeanInformationAudit.Census.Certificate
  let mut certificateDirectory ← findOLean certificateModule
  for _ in certificateModule.components do
    certificateDirectory := certificateDirectory.parent.get!
  let finalSearchPath : SearchPath := [← getLibDir (← getBuildDir), certificateDirectory]
  -- The invoking Lean process already has the warm toolchain and LEAN_PATH.
  -- Its child needs only the compiler, not a second Lake environment startup.
  let repository ← IO.currentDir
  let mut inputDirectory := source
  for _ in root.components do inputDirectory := inputDirectory.parent.get!
  let result ← IO.Process.output {
    cmd := "python3"
    args := #[ (repository / "tools/lean-inspector/Census/Certificate/buckets.py").toString,
      "--source", compiledSource.toString, "--root", root.toString,
      "--inputs", inputDirectory.toString, "--certificate-directory", certificateDirectory.toString ] ++
      (if dataOnly then #["--data-only"] else #[]) }
  IO.FS.writeFile (source.withExtension "compiler.log") (result.stdout ++ result.stderr)
  unless result.exitCode == 0 do
    throw <| IO.userError s!"census certificate: final source failed elaboration: {result.stdout}{result.stderr}"
  let (data, _) ← readModuleData target
  checkSourceImports data.imports root
  -- Serialized output is the standalone compiler's environment, including its
  -- kernel-checked theorem, never the IO driver's environment.
  for suffix in ["olean", "olean.server", "olean.private", "ir"] do
    let artifact := compiledSource.withExtension suffix
    if ← artifact.pathExists then
      IO.FS.writeBinFile (source.withExtension suffix) (← IO.FS.readBinFile artifact)
  IO.FS.writeFile (source.withExtension "build.json")
    (← IO.FS.readFile (compiledSource.withExtension "build.json"))
  let previous ← searchPathRef.get
  try
    searchPathRef.set (directory :: finalSearchPath)
    -- Only Root exposes its private theorem. Children keep their exported
    -- interfaces; Lean's serialized axiom closures avoid replaying their proofs.
    unsafe enableInitializersExecution
    return (← importModules #[{ module := root, importAll := true }] options
      (loadExts := true) (level := .exported)).setExporting false
  finally
    searchPathRef.set previous

/-- Emit the actual proposition over ids, with a literal requested count.
Reflexivity is cheaper than decide for equality of the independently bound chunks. -/
def certificateSource (input : String) (ids reportIds certificate : Name) (requested : Nat) : String :=
  input ++ "\npublic theorem " ++ certificate.toString ++ " :\n  LeanInformationAudit.CensusKeyManifest.Certificate " ++
    ids.toString ++ " " ++ toString requested ++ " " ++ reportIds.toString ++
    " := by\n  exact LeanInformationAudit.certificate_of_range " ++ ids.getPrefix.toString ++ ".facts\n"

/-- A valid certificate needs one imported environment. Both the kernel theorem
and its constructor graph are checked before publication. If its proof fails,
elaborate the data alone so the binder reports identity before missing rows;
the original compiler failure is rethrown if the data passes all checks. -/
def elaborateBoundSource (input checkedInput : String) (source checked : System.FilePath)
    (root : Name) (options : Options) (check : Environment → CommandElabM Unit) :
    CommandElabM Environment := do
  let staged ← try elaborateFinalSource checkedInput checked.toString root options
    catch error => do
      let data ← elaborateFinalSource input source.toString root options (dataOnly := true)
      let previous ← searchPathRef.get
      try
        searchPathRef.set (source.withExtension "compile" :: previous)
        check data
      finally
        searchPathRef.set previous
      throw error
  let previous ← searchPathRef.get
  try
    searchPathRef.set (checked.withExtension "compile" :: previous)
    check staged
  finally
    searchPathRef.set previous
  return staged

/-- Keep all serialized module levels together. The private level is needed by
the binder and audit tools; ordinary `module` imports load only public interfaces. -/
def copyFinalArtifacts (checked source : System.FilePath) (root : Name) : IO Unit := do
  for suffix in ["olean", "olean.server", "olean.private", "ir"] do
    if ← (checked.withExtension suffix).pathExists then
      IO.FS.writeBinFile (source.withExtension suffix) (← IO.FS.readBinFile (checked.withExtension suffix))
  let directory := checked.withExtension "compile" /
    System.mkFilePath (root.getPrefix.components.map Name.toString)
  for entry in ← directory.readDir do
    if entry.fileName.startsWith "Range" && !entry.fileName.endsWith ".lean" &&
        !entry.fileName.endsWith ".compiler.log" then
      IO.FS.writeBinFile (source.parent.get! / entry.fileName) (← IO.FS.readBinFile entry.path)

private def phase (destination label : String) : IO Unit :=
  IO.FS.writeFile (destination ++ ".phase") label

/-- Selection depends only on the immutable report and explicit requested prefix. -/
def selectReport (report : FrozenReport) (bytes selectionPrefix : String) : Except String FrozenReport := do
  let json ← Json.parse bytes
  let mut ids : Std.HashSet String := {}
  for node in ← json.getObjValAs? (Array Json) "nodes" do
    if (← stringField node "freeze_status") != "frozen" then continue
    let path ← stringField node "repo_path"
    let owner := String.intercalate "." ((path.dropEnd 5).toString.splitOn "/")
    unless owner == selectionPrefix || owner.startsWith (selectionPrefix ++ ".") do continue
    for row in ← node.getObjValAs? (Array Json) "declarations" do
      if (← stringField row "kind") == "theorem" then
        ids := ids.insert (← stringField row "statement_id")
  return { report with theorems := report.theorems.filter (fun key => ids.contains key.statementId) }

def summaryFields (report : FrozenReport) (inventory : DispositionInventory)
    (sources : Array ProvenanceSource) : List (String × Json) :=
  let counts := count inventory
  let complete := counts.accounted == report.theorems.size
  [
    ("schema", toJson "lean-information-disposition-census"),
    ("head_sha", toJson report.headSha), ("report_sha256", toJson report.reportSha256),
    ("source_inputs", toJson sources), ("theorem_count", toJson report.theorems.size),
    ("requested_keys", toJson report.theorems.size),
    ("input_kind", toJson (if report.headSha == "fixture-head" then "synthetic_fixture" else "production")),
    ("query_verification", toJson "lean_streaming_query"),
    ("status", toJson (if complete then "complete" else "partial")),
    ("coverage_theorem_count", toJson counts.accounted),
    ("counts", toJson counts), ("certified_complete", toJson (complete && counts.observed == 0))]

/-- The query lane supplies one whole-stream artifact and receipt. The kernel
claim is over ids; Name binding and handoff metadata are elaborator obligations. -/
elab "#disposition_census" &"projection" &"root" root:ident &"source" sourcePath:str &"report" reportPath:str
    &"head" head:str &"report_sha256" reportSha:str &"prefix" selectionPrefix:str
    &"manifest" manifestName:ident &"report_keys" reportKeysName:ident &"rows" rowsPath:str
    &"receipt" receiptPath:str &"receipt_digest" receiptDigest:str
    generate:(" generate")?
    &"certificate" certificate:ident " output " outputPath:str : command => do
  let destination := outputPath.getString
  phase destination "report_binding"
  let bytes ← IO.FS.readFile reportPath.getString
  let report ← parseReportDataIO bytes
  let selected ← ofExcept <| selectReport report bytes selectionPrefix.getString
  let manifestName := manifestName.getId.eraseMacroScopes
  let reportKeysName := reportKeysName.getId.eraseMacroScopes
  phase destination "handoff_read_and_emission"
  let source := System.FilePath.mk sourcePath.getString
  let rows ← CensusTransport.readHandoff rowsPath.getString receiptPath.getString receiptDigest.getString report
    (if generate.isSome then some (source.parent.get!.parent.get!.toString,
      reportPath.getString, selectionPrefix.getString) else none)
  ofExcept <| checkIdentityInputs report.headSha report.theorems rows
  ofExcept <| checkReportBinding head.getString reportSha.getString report
  phase destination "bucket_build_and_assembly"
  let options := ((← getOptions).erase `maxRecDepth).setBool `Elab.async false
  let input ← IO.FS.readFile sourcePath.getString
  let checkedPath := source.withExtension "checked.lean"
  let certificateName := (← getCurrNamespace) ++ certificate.getId.eraseMacroScopes
  let checkedInput := certificateSource input (manifestName.appendAfter "Keys") reportKeysName
    certificateName selected.theorems.size
  let staged ← elaborateBoundSource input checkedInput source checkedPath root.getId options fun env => do
    phase destination "boundary_and_binding"
    liftTermElabM <| checkFinalEnvironment env (some root.getId)
    withEnv env <| liftTermElabM <| withOptions (fun _ => options) do
      bindEmittedManifest selected root.getId rows manifestName reportKeysName
  let (data, _) ← readModuleData (checkedPath.withExtension "olean")
  let imports := data.imports.map (·.module.toString)
  let closure := staged.header.moduleNames.filter (· != root.getId) |>.map Name.toString
  IO.FS.writeFile (destination ++ ".environment.json") ((Json.mkObj [
    ("imports", toJson imports), ("transitive_imports", toJson closure)]).pretty ++ "\n")
  let ids := mkConst (manifestName.appendAfter "Keys")
  let reportKeysExpr := mkConst reportKeysName
  phase destination "axioms"
  let proposition ← withEnv staged <| liftTermElabM do
    let expected ← mkAppM ``CensusKeyManifest.Certificate #[ids, toExpr selected.theorems.size, reportKeysExpr]
    let actual ← getConstInfo certificateName
    unless actual matches .thmInfo _ do throwError "census certificate: expected a kernel theorem"
    unless ← isDefEq actual.type expected do throwError "census certificate: incorrect proposition"
    return actual.type
  let axioms ← withEnv staged <| collectAxioms certificateName
  unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
    throwError "census certificate: unapproved axioms {axioms}"
  let typeText ← withEnv staged <| liftTermElabM <| return toString (← ppExpr proposition)
  let certificateJson := Json.mkObj [("name", toJson certificateName.toString),
    ("type", toJson typeText), ("axioms", toJson (axioms.map Name.toString))]
  copyFinalArtifacts checkedPath (System.FilePath.mk sourcePath.getString) root.getId
  if ← (System.FilePath.mk destination).pathExists then
    for authority in [reportPath.getString, rowsPath.getString, receiptPath.getString] do
      let same ← IO.Process.output { cmd := "/bin/test", args := #[authority, "-ef", destination] }
      unless same.exitCode == 1 do throwError "census projection: output aliases handoff authority"
  phase destination "json_emission"
  CensusTransport.publish destination <| Json.mkObj [
    ("certificate", certificateJson), ("query_receipt_digest", toJson receiptDigest.getString)]
  phase destination "axioms"
  withEnv staged <| elabCommand (← `(command| #print axioms $(mkIdent certificateName)))

end LeanInformationAudit.CensusProjection
