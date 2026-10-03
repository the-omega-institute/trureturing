import Lake
import Lake.CLI.Build
import Lake.Util.StoreInsts
open Lake DSL System
open Lean (Json)

package leanInspector where
  packagesDir := "../../.lake/packages"
  buildDir := "../../.lake/build/lean-inspector/producer"
  leanOptions := #[⟨`pp.unicode.fun, true⟩, ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩, ⟨`maxSynthPendingDepth, 3⟩]

require trureturing from "../.."
require leanInspectorInterface from "../lean-inspector-interface"

@[default_target]
lean_lib LeanInformationAudit where
  globs := #[.submodules `LeanInformationAudit]

lean_lib LeanInformationAuditAnalysis where
  globs := #[.submodules `LeanInformationAuditAnalysis]

lean_lib InformationSourceFixture

target nativeImage pkg : FilePath := do
  buildLeanO (pkg.buildDir / "c" / "native_image.o")
    (← inputFile (pkg.dir / "native_image.c") true) #[] #["-O3", "-DLEAN_EXPORTING"]

lean_exe reportInspector where
  root := `Inspector
  supportInterpreter := true
  moreLinkObjs := #[{key := .mk (.packageTarget .anonymous `nativeImage)}]

-- Resolve Lake's current package at runtime; copied config oleans contain no host root.
private partial def repositoryDir (pkg : Package) : IO FilePath := do
  let rec ascend (dir : FilePath) : IO FilePath := do
    if (← (dir / "lakefile.toml").pathExists) &&
        (← (dir / "lean-toolchain").pathExists) then return dir
    if let some parent := dir.parent then
      if parent != dir then return ← ascend parent
    throw <| IO.userError "Inspector repository root not found"
  ascend (← IO.FS.realPath pkg.dir)

private def nativeCommand (pkg : Package) (args : Array String) : IO IO.Process.SpawnArgs := do
  let root ← repositoryDir pkg
  return {
    cmd := "python3", args := #[(root / "tools/lean-inspector/native.py").toString] ++ args
    cwd := some root }
-- Direct phase observations survive a cache-writer process that buffers Lake's
-- output. They never participate in traces, reuse or admission decisions.
private def observePhase (phase boundary : String) : IO Unit := do
  if let some path ← IO.getEnv "STRATALINT_INSPECTOR_PHASES" then
    let now ← IO.monoMsNow
    IO.FS.withFile path .append fun out => out.putStrLn <| (Lean.Json.mkObj [
      ("phase", Lean.toJson phase), ("boundary", Lean.toJson boundary),
      ("monotonic_ms", Lean.toJson now)]).compress

private structure ReportState where
  started : IO.Ref Lean.NameSet
  batch : IO.Ref (Option (Lean.NameSet × Job Unit))
  sourcePaths : IO.Ref (Std.HashMap String (Option String))

package_facet reportBatch (_pkg : Package) : ReportState := do
  Job.async do return ⟨← IO.mkRef {}, ← IO.mkRef none, ← IO.mkRef {}⟩

-- A compiler import is shared by many report targets. Resolve its source path
-- once in this Lake invocation, including paths excluded from the whitelist.
-- This memo is never persisted or mixed into an artifact trace.
private def reportSourcePath (root : FilePath)
    (memo : IO.Ref (Std.HashMap String (Option String)))
    (source : FilePath) : IO (Option String) := do
  let key := source.toString
  if let some path := (← memo.get)[key]? then return path
  let path := (relPathFrom root (← IO.FS.realPath source)).toString
  let result := if path.startsWith ".lake/" || path.startsWith "../" then none else some path
  memo.modify (·.insert key result)
  return result

/-- Utility input is generated once per invocation by its existing .NET owner.
This job deliberately has no content trace: each module traces its own record. -/
package_facet reportInputs (pkg : Package) : FilePath := do
  Job.async do
    proc (← nativeCommand pkg #["prepare", (← repositoryDir pkg).toString])
    return (← repositoryDir pkg) / ".lake/build/lean-inspector" / "inputs.json"

private def readJson (path : FilePath) : IO Json := do
  IO.ofExcept (Json.parse (← IO.FS.readFile path))

private def writeBinFileIfChanged (path : FilePath) (contents : ByteArray) : IO Unit := do
  let unchanged ← try
    pure ((← IO.FS.readBinFile path) == contents)
  catch _ =>
    pure false
  unless unchanged do
    IO.FS.writeBinFile path contents

private def strings (json : Json) (key : String) : IO (Array String) :=
  IO.ofExcept (json.getObjValAs? (Array String) key)

package_facet reportSourceModules (pkg : Package) : Lean.NameSet := do
  (← fetch <| pkg.facet `reportInputs).mapM fun path => do
    let names ← strings (← readJson path) "modules"
    return names.foldl (fun set name => set.insert name.toName) {}

/-- Trace semantic compatibility after validating registered inputs.
Raw configuration identity belongs to the aggregate; module exports carry
Lake's compiler dependencies. Producer compilation is a separate obligation. -/
package_facet reportProducer (pkg : Package) : Unit := withCurrPackage pkg do
  discard <| (← fetch <| pkg.facet `reportInputs).await
  return Job.nil.mix (← inputBinFile ((← repositoryDir pkg) / ".lake/build/lean-inspector" / "compatibility"))

/-- A native report artifact. Production validates it completely before it is
written; like an olean, a traced artifact is afterwards reused as is. -/
private structure ReportArtifact where
  path : FilePath
  outputTrace : BuildTrace

private def buildArtifact (file : FilePath) (build : JobM PUnit) : JobM ReportArtifact := do
  let art ← buildArtifactUnlessUpToDate file build (ext := "zip") (restore := true)
  return ⟨art.path, ← getTrace⟩

/-- Ask Lake itself whether a native artifact can be reused/restored. A native
`noBuild` miss is data for a subsequent dependency job, not a blocked worker.
All other failures (and a caller's actual `--no-build`) propagate unchanged. -/
private def probeArtifact (file : FilePath) (build : JobM PUnit) :
    JobM (Option ReportArtifact) := .ofFn fun fetch pkg? stack store ctx state => do
  let result ← (buildArtifact file build).toFn fetch pkg? stack store
    {ctx with noBuild := true} state
  match result with
  | .ok row next => return .ok (some row) next
  | .error err next =>
    if next.wantsRebuild && !ctx.noBuild then
      return .ok none state
    else
      return .error err next

private structure PreparedArtifact where
  file : FilePath
  args : Array String
  env : Array (String × Option String)
  inputTrace : BuildTrace
  artifact? : Option ReportArtifact
  prepareProduction : JobM Unit

-- These private jobs are interned in Lake's invocation store.
module_data inspectorPreparedReport : PreparedArtifact
module_data inspectorModuleReport : ReportArtifact

private def prepareNativeModuleReport (mod : Module) : FetchM (Job PreparedArtifact) := withCurrPackage mod.pkg do
  let pkg := (← getWorkspace).root
  discard <| (← fetch <| pkg.facet `reportInputs).await
  let root ← repositoryDir pkg
  let utility := root / ".lake/build/lean-inspector" / "inputs" / s!"{mod.name}.json"
  let record ← readJson utility
  let claims ← strings record "claims"
  let mut deps ← fetch <| pkg.facet `reportProducer
  deps := deps.mix (← inputBinFile mod.leanFile)
  deps := deps.mix (← inputBinFile utility)
  let mut exports := #[(← mod.exportInfo.fetch)]
  let mut sourceModules := #[mod]
  -- Inspector loads this fixed judge even for an empty registration inventory.
  -- Demand its build without making this program a report data dependency.
  let some driver := (← getWorkspace).findModule? `LeanInformationAudit.SealCommand
    | error "IE-C050 reason=incomplete_closure rule=dtr.report_producer"
  let driverBuild ← driver.exportInfo.fetch
  for name in claims do
    let some claim := (← getWorkspace).findModule? name.toName
      | error s!"utility claim module is not in the Lake workspace: {name}"
    exports := exports.push (← claim.exportInfo.fetch)
    sourceModules := sourceModules.push claim
  -- Only production consumes this source whitelist. Warm artifacts still trace
  -- the complete compiler exports below. Missing artifacts prepare the same
  -- Lake-owned closure before extraction; no dependency parser or additional
  -- cache chooses its members.
  let prepareProduction : JobM Unit := do
    let reported ← (← JobM.runFetchM <| fetch <| pkg.facet `reportSourceModules).await
    let reportState ← (← JobM.runFetchM <| fetch <| pkg.facet `reportBatch).await
    let mut dependencies := #[]
    for source in sourceModules do
      dependencies := dependencies.push source ++
        (← (← JobM.runFetchM source.transImports.fetch).await)
    let mut sourcePaths : Array String := #[]
    for dependency in dependencies do
      if dependency.name != mod.name && reported.contains dependency.name then continue
      if let some path ← reportSourcePath root reportState.sourcePaths dependency.leanFile then
        sourcePaths := sourcePaths.push path
    writeBinFileIfChanged (utility.addExtension "sources.json")
      (String.toUTF8 (Lean.toJson sourcePaths).compress)
  -- Await without mixing: recompilation must succeed, but its implementation
  -- identity is not a report-semantic dependency.
  let inspector ← reportInspector.fetch
  let workspace ← getWorkspace
  let env := workspace.augmentedEnvVars
  let file := root / ".lake/build/lean-inspector" / "modules" / s!"{mod.name}.zip"
  (deps.add (Job.mixArray exports) |>.add inspector |>.add driverBuild).mapM fun _ => do
    -- Inspector's private import mode reads transitive private values, also
    -- through public imports. Lake's legacy trace follows that same closure;
    -- allTransTrace follows each import's visibility and can omit those values.
    -- Apply this to the module and every external utility claim.
    for exportJob in exports do
      let info ← exportJob.await
      addTrace (info.allArtsTrace.mix info.legacyTransTrace)
    let executable ← inspector.await
    let args := #[root.toString, mod.name.toString, (← IO.FS.realPath mod.leanFile).toString,
      utility.toString, executable.toString, file.toString]
    let build := do
      prepareProduction
      proc { (← nativeCommand pkg (#["module"] ++ args)) with env }
      pure PUnit.unit
    let inputTrace ← getTrace
    let artifact? ← probeArtifact file build
    return ⟨file, args, env, inputTrace, artifact?, prepareProduction⟩

private def preparedModuleReport (mod : Module) : FetchM (Job PreparedArtifact) := do
  let key := (mod.facet `inspectorPreparedReport).key
  let job : Job (BuildData key) ← fetchOrCreate key do
    let job ← prepareNativeModuleReport mod
    return cast (by simp [key]) job
  return cast (by simp [key]) job

private def buildNativeModuleReport (mod : Module) : FetchM (Job ReportArtifact) := withCurrPackage mod.pkg do
  let pkg := (← getWorkspace).root
  let reportState ← (← fetch <| pkg.facet `reportBatch).await
  reportState.started.modify (·.insert mod.name)
  let prepared ← preparedModuleReport mod
  let batch? ← reportState.batch.get
  let batch? := batch?.filter fun (members, _) => members.contains mod.name
  let ready := match batch? with | some (_, batch) => prepared.add batch | none => prepared
  ready.mapM fun request => do
    setTrace request.inputTrace
    if let some row := request.artifact? then
      setTrace row.outputTrace
      return row
    let pending := request.file.addExtension "pending"
    let build := if batch?.isSome then do
        IO.FS.rename pending request.file
        pure PUnit.unit
      else do
        request.prepareProduction
        proc { (← nativeCommand pkg (#["module"] ++ request.args)) with env := request.env }
        pure PUnit.unit
    try
      buildArtifact request.file build
    finally
      if batch?.isSome then removeFileIfExists pending

private def nativeModuleReport (mod : Module) : FetchM (Job ReportArtifact) := do
  let key := (mod.facet `inspectorModuleReport).key
  let job : Job (BuildData key) ← fetchOrCreate key do
    let job ← withRegisterJob s!"{mod.name}:report (internal native artifact)" <| buildNativeModuleReport mod
    return cast (by simp [key]) job
  return cast (by simp [key]) job

module_facet report (mod : Module) : FilePath := withCurrPackage mod.pkg do
  (← nativeModuleReport mod).mapM fun row => do
    setTrace row.outputTrace
    return row.path

private def runBatch (pkg : Package) (requests : Array (String × Array String)) : JobM Unit := do
  let requestFile := (← repositoryDir pkg) / ".lake/build/lean-inspector" / "batch.json"
  IO.FS.writeFile requestFile (Lean.toJson requests).compress
  let env := (← getWorkspace).augmentedEnvVars
  try
    let result ← IO.Process.output { (← nativeCommand pkg #["batch", requestFile.toString]) with env }
    unless result.stdout.isEmpty do logInfo result.stdout
    unless result.stderr.isEmpty do logInfo result.stderr
    unless result.exitCode == 0 do error s!"Inspector batch exited with code {result.exitCode}"
  finally
    removeFileIfExists requestFile

-- Bound the continuation depth when collecting thousands of module jobs.
private def collectModuleJobs {α : Type} (jobs : Array (Job α)) : Job (Array α) := Id.run do
  let mut level : Array (Job (Array α)) := #[]
  let mut start := 0
  while start < jobs.size do
    level := level.push (Job.collectArray (jobs.extract start (min (start + 64) jobs.size)))
    start := start + 64
  if level.isEmpty then
    return Job.collectArray #[]
  while level.size > 1 do
    let mut next : Array (Job (Array α)) := #[]
    let mut i := 0
    while i < level.size do
      if i + 1 < level.size then
        next := next.push ((level[i]!).zipWith (sync := true) (· ++ ·) (level[i + 1]!))
        i := i + 2
      else
        next := next.push level[i]!
        i := i + 1
    level := next
  return level[0]?.getD (Job.collectArray #[])

package_facet report (owner : Package) : FilePath := withCurrPackage owner do
  let pkg := (← getWorkspace).root
  observePhase "lake-inputs" "start"
  let reportState ← (← fetch <| pkg.facet `reportBatch).await
  let inputs ← (← fetch <| pkg.facet `reportInputs).await
  let config ← readJson inputs
  let names ← strings config "modules"
  observePhase "lake-inputs" "finish"
  -- The report owns registered modules. The caller supplies program targets
  -- from its resource selection in the same Lake invocation.
  -- Shared native dependency jobs compose continuations; no per-miss promise
  -- wait, readiness polling, or independent dependency/freshness planner.
  let alreadyStarted ← reportState.started.get
  let mut members : Lean.NameSet := {}
  let mut prepared := #[]
  observePhase "lake-prepare" "start"
  try observePhase "lake-prepare-register" "start" catch _ => pure ()
  for name in names do
    let some mod := (← getWorkspace).findModule? name.toName
      | error s!"registered report module is not in the Lake workspace: {name}"
    unless alreadyStarted.contains mod.name do
      members := members.insert mod.name
      prepared := prepared.push (← preparedModuleReport mod)
  try observePhase "lake-prepare-register" "finish" catch _ => pure ()
  let batch ← (collectModuleJobs prepared).mapM fun artifacts => do
    observePhase "lake-prepare" "finish"
    try observePhase "lake-source-whitelists" "start" catch _ => pure ()
    let requests ← artifacts.filterMapM fun request => do
      if request.artifact?.isSome then return none
      request.prepareProduction
      return some ("produce", request.args.set! 5 (request.file.addExtension "pending").toString)
    try observePhase "lake-source-whitelists" "finish" catch _ => pure ()
    unless requests.isEmpty do
      runBatch pkg requests
  let batch ← registerJob "Inspector native production batch" batch
  reportState.batch.set (some (members, batch))
  let mut rows := #[]
  for name in names do
    let some mod := (← getWorkspace).findModule? name.toName
      | error s!"registered report module is not in the Lake workspace: {name}"
    rows := rows.push (← nativeModuleReport mod)
  let membership ← inputBinFile inputs
  ((collectModuleJobs rows).zipWith (fun artifacts _ => artifacts) membership).mapM fun artifacts => do
    let root ← repositoryDir pkg
    let file := root / ".lake/build/lean-inspector" / "report.zip"
    let mut trace := BuildTrace.nil "<collection>"
    for row in artifacts do
      trace := trace.mix row.outputTrace.withoutInputs
    setTrace (mixTrace trace membership.getTrace)
    -- Concatenating traced, production-validated rows needs no further check.
    let build := do
      runBatch pkg #[("aggregate", #[root.toString, file.toString] ++ artifacts.map (·.path.toString))]
      pure PUnit.unit
    return (← buildArtifact file build).path
