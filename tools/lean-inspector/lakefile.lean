import Lake
import Lake.CLI.Build
import Lake.Util.StoreInsts
import Std.Sync.Mutex
open Lake DSL System
open Lean (Json)

package leanInspector where
  buildDir := "../../.lake/build/lean-inspector/producer"

lean_exe reportInspector where
  root := `Inspector

private def inspectorDir (pkg : Package) : FilePath := pkg.dir / "tools" / "lean-inspector"

private def nativeCommand (pkg : Package) (args : Array String) : IO.Process.SpawnArgs :=
  { cmd := "python3", args := #[((inspectorDir pkg) / "native.py").toString] ++ args,
    cwd := some pkg.dir }

private structure RowRequest where
  kind : String
  args : Array String
  done : IO.Promise UInt32

private abbrev PendingRows := IO.Ref (Option (IO.Ref (Array RowRequest)))

private structure ReportState where
  pending : PendingRows
  validation : Std.Mutex Unit

package_facet reportBatch (_pkg : Package) : ReportState := do
  Job.async do return ⟨← IO.mkRef none, ← Std.Mutex.new ()⟩

private def enqueueRow (queue : IO.Ref (Array RowRequest)) (kind : String)
    (args : Array String) : JobM UInt32 := do
  let done ← IO.Promise.new
  queue.modify (·.push ⟨kind, args, done⟩)
  let some status ← IO.wait done.result?
    | error "Inspector batch abandoned"
  return status

private def produceRow (pendingRows : PendingRows) (pkg : Package) (args : Array String)
    (env : Array (String × Option String)) : JobM PUnit := do
  if let some queue ← pendingRows.get then
    let status ← enqueueRow queue "produce" args
    unless status == 0 do error "Inspector batch failed"
  else
    proc { (nativeCommand pkg (#["module"] ++ args)) with env }
  pure PUnit.unit

private def validateArtifact (pkg : Package) (args : Array String) : JobM UInt32 := do
  return (← IO.Process.output (nativeCommand pkg (#["validate"] ++ args))).exitCode

/-- Utility input is generated once per invocation by its existing .NET owner.
This job deliberately has no content trace: each module traces its own record. -/
package_facet reportInputs (pkg : Package) : FilePath := do
  Job.async do
    proc (nativeCommand pkg #["prepare", pkg.dir.toString])
    return pkg.buildDir / "lean-inspector" / "inputs.json"

private def readJson (path : FilePath) : IO Json := do
  IO.ofExcept (Json.parse (← IO.FS.readFile path))

private def strings (json : Json) (key : String) : IO (Array String) :=
  IO.ofExcept (json.getObjValAs? (Array String) key)

/-- Trace semantic compatibility and registered content configuration.
Producer compilation remains a separate native obligation. -/
package_facet reportProducer (pkg : Package) : Unit := withCurrPackage pkg do
  let config ← readJson (← (← fetch <| pkg.facet `reportInputs).await)
  let configs ← strings config "configs"
  let mut deps := Job.nil.mix (← inputBinFile (pkg.buildDir / "lean-inspector" / "compatibility"))
  for path in configs do
    deps := deps.mix (← inputBinFile (pkg.dir / path))
  return deps

/-- A completed native build, not yet accepted by the canonical validator.
Only private jobs carry this value; it is never a public report facet. -/
private structure UnvalidatedArtifact where
  file : FilePath
  path : FilePath
  inputTrace : BuildTrace
  outputTrace : IO.Ref BuildTrace
  build : JobM PUnit
  check : Array String

private def uncheckedArtifact (file : FilePath) (build : JobM PUnit)
    (check : Array String) : JobM UnvalidatedArtifact := do
  let inputTrace ← getTrace
  let art ← buildArtifactUnlessUpToDate file build (ext := "zip") (restore := true)
  return ⟨file, art.path, inputTrace, ← IO.mkRef (← getTrace), build, check⟩

/-- Rejected optional artifacts are rebuilt exactly once through Lake, with
cache reads disabled for that reconstruction. Never write through a restored
hard link or evict a blob. Required build and validation failures propagate. -/
private def rebuildRejectedArtifact (pkg : Package) (row : UnvalidatedArtifact) : JobM FilePath := do
  logWarning s!"inspector artifact rejected; rebuilding privately: {row.file}"
  removeFileIfExists row.file
  removeFileIfExists (row.file.addExtension "trace")
  clearFileHash row.file
  setTrace row.inputTrace
  let recovered ← withCurrPackage? none <|
    buildArtifactUnlessUpToDate row.file row.build (ext := "zip") (restore := true)
  unless (← validateArtifact pkg (row.check ++ #[recovered.path.toString])) == 0 do
    error s!"reconstructed Inspector artifact is invalid: {row.file}"
  row.outputTrace.set (← getTrace)
  return recovered.path

private def acceptArtifact (pkg : Package) (row : UnvalidatedArtifact) : JobM FilePath := do
  if (← validateArtifact pkg (row.check ++ #[row.path.toString])) != 0 then
    return ← rebuildRejectedArtifact pkg row
  setTrace (← row.outputTrace.get)
  return row.path

private def checkedArtifact (pkg : Package) (file : FilePath)
    (build : JobM PUnit) (check : Array String) : JobM FilePath := do
  acceptArtifact pkg (← uncheckedArtifact file build check)

-- The data key interns the private job in Lake's invocation build store. No
-- module_facet is registered for this key, so it cannot be requested as a
-- public target or used to return an unvalidated report.
module_data inspectorUnvalidatedReport : UnvalidatedArtifact

private def buildNativeModuleReport (mod : Module) : FetchM (Job UnvalidatedArtifact) := withCurrPackage mod.pkg do
  let pkg := mod.pkg
  let reportState ← (← fetch <| pkg.facet `reportBatch).await
  discard <| (← fetch <| pkg.facet `reportInputs).await
  let utility := pkg.buildDir / "lean-inspector" / "inputs" / s!"{mod.name}.json"
  let record ← readJson utility
  let claims ← strings record "claims"
  let mut deps ← fetch <| pkg.facet `reportProducer
  deps := deps.mix (← inputBinFile mod.leanFile)
  deps := deps.mix (← inputBinFile utility)
  let mut exports := #[(← mod.exportInfo.fetch)]
  for name in claims do
    let some claim := (← getWorkspace).findModule? name.toName
      | error s!"utility claim module is not in the Lake workspace: {name}"
    exports := exports.push (← claim.exportInfo.fetch)
  -- Await without mixing: recompilation must succeed, but its implementation
  -- identity is not a report-semantic dependency.
  let inspector ← reportInspector.fetch
  let workspace ← getWorkspace
  let env := #[ ("LEAN_PATH", some workspace.leanPath.toString) ]
  let file := pkg.buildDir / "lean-inspector" / "modules" / s!"{mod.name}.zip"
  (deps.add (Job.mixArray exports) |>.add inspector).mapM fun _ => do
    -- Inspector reads private declarations and values, including the complete
    -- transitive closure of external utility claims.
    for exportJob in exports do
      let info ← exportJob.await
      addTrace (info.allArtsTrace.mix info.allTransTrace)
    let executable ← inspector.await
    let args := #[pkg.dir.toString, mod.name.toString, mod.leanFile.toString,
      utility.toString, executable.toString, file.toString]
    let row ← uncheckedArtifact file (produceRow reportState.pending pkg args env)
      #["module", pkg.dir.toString, mod.name.toString, utility.toString]
    -- Reconstruction also serves separately requested public module facets;
    -- it must not re-enter the package's initial production barrier.
    return {row with build := do
      proc { (nativeCommand pkg (#["module"] ++ args)) with env }
      pure PUnit.unit}

private def nativeModuleReport (mod : Module) : FetchM (Job UnvalidatedArtifact) := do
  let key := (mod.facet `inspectorUnvalidatedReport).key
  let job : Job (BuildData key) ← fetchOrCreate key do
    let job ← withRegisterJob s!"{mod.name}:report (internal native artifact)" <| buildNativeModuleReport mod
    return cast (by simp [key]) job
  return cast (by simp [key]) job

module_facet report (mod : Module) : FilePath := withCurrPackage mod.pkg do
  let reportState ← (← fetch <| mod.pkg.facet `reportBatch).await
  (← nativeModuleReport mod).mapM fun row =>
    reportState.validation.atomically do acceptArtifact mod.pkg row

private def runBatch (pkg : Package) (requests : Array (String × Array String)) : JobM (Array Nat) := do
  let requestFile := pkg.buildDir / "lean-inspector" / "batch.json"
  let resultFile := pkg.buildDir / "lean-inspector" / "batch-results.json"
  IO.FS.writeFile requestFile (Lean.toJson requests).compress
  let env := #[("LEAN_PATH", some (← getWorkspace).leanPath.toString)]
  try
    let result ← IO.Process.output { (nativeCommand pkg #["batch", requestFile.toString, resultFile.toString]) with env }
    unless result.stdout.isEmpty do logInfo result.stdout
    unless result.stderr.isEmpty do logInfo result.stderr
    unless result.exitCode == 0 do error s!"Inspector batch exited with code {result.exitCode}"
    let statuses : Array Nat ← IO.ofExcept (Lean.fromJson? (← readJson resultFile))
    unless statuses.size == requests.size && statuses.all (· ≤ 1) do
      error "Inspector batch result mismatch"
    return statuses
  finally
    removeFileIfExists requestFile
    removeFileIfExists resultFile

package_facet report (pkg : Package) : FilePath := withCurrPackage pkg do
  let reportState ← (← fetch <| pkg.facet `reportBatch).await
  let pendingRows := reportState.pending
  let inputs ← (← fetch <| pkg.facet `reportInputs).await
  let config ← readJson inputs
  let names ← strings config "modules"
  -- Demand ordinary defaults independently of row traces. Audit/default-only
  -- changes still fail the invocation without invalidating unrelated rows.
  let defaults ← match ← (parseTargetSpec (← getWorkspace) s!"@{pkg.baseName}").toBaseIO with
    | .ok specs => pure specs
    | .error err => error err.toString
  discard <| (← buildSpecs defaults).await
  -- Native artifact builders enqueue only actual misses/rejected artifacts.
  -- Coalescing their execution shares imports/SCC work, never invalidation.
  let queue ← IO.mkRef (#[] : Array RowRequest)
  pendingRows.set (some queue)
  let mut rows := #[]
  try
    for name in names do
      let some mod := (← getWorkspace).findModule? name.toName
        | error s!"registered report module is not in the Lake workspace: {name}"
      rows := rows.push (← nativeModuleReport mod)
    repeat
      let mut finished := 0
      for row in rows do
        if ← IO.hasFinished row.task then finished := finished + 1
      if finished == rows.size then break
      if finished + (← queue.get).size != rows.size then
        IO.sleep 1
        continue
      let requests ← queue.get
      queue.set #[]
      try
        let statuses ← runBatch pkg (requests.map fun r => (r.kind, r.args))
        for (request, status) in requests.zip statuses do request.done.resolve status.toUInt32
      finally
        for request in requests do request.done.resolve 1
  finally
    pendingRows.set none
    for request in (← queue.get) do request.done.resolve 1
  -- Validate actual completed Lake results together. Reusable rows never wait
  -- on the synchronous producer barrier. Only real misses enter that queue.
  let validated ← (Job.collectArray rows).mapM fun artifacts => reportState.validation.atomically do
    let statuses ← runBatch pkg (artifacts.map fun row =>
      ("validate", #[pkg.dir.toString] ++ row.check ++ #[row.path.toString]))
    let mut paths := #[]
    let mut trace := BuildTrace.nil "<collection>"
    for (row, status) in artifacts.zip statuses do
      let path ← if status == 0 then do
          setTrace (← row.outputTrace.get)
          pure row.path
        else
          rebuildRejectedArtifact pkg row
      paths := paths.push path
      trace := trace.mix (← getTrace).withoutInputs
    -- Preserve the native collection trace shape, replacing a rejected row's
    -- trace with the trace of its actual private reconstruction.
    setTrace trace
    return paths
  let membership ← inputBinFile inputs
  (validated.zipWith (fun paths _ => paths) membership).mapM fun rowPaths => do
    let paths := rowPaths.map (·.toString)
    let file := pkg.buildDir / "lean-inspector" / "report.zip"
    checkedArtifact pkg file (do
      proc (nativeCommand pkg (#["aggregate", pkg.dir.toString, file.toString] ++ paths))
      pure PUnit.unit) #["report", pkg.dir.toString]
