import Lake
import Lake.CLI.Build
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

package_facet reportBatch (pkg : Package) : PendingRows := do
  Job.async do IO.mkRef none

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

private def validateArtifact (pendingRows : PendingRows) (pkg : Package) (args : Array String) : JobM UInt32 := do
  if let some queue ← pendingRows.get then
    enqueueRow queue "validate" (#[pkg.dir.toString] ++ args)
  else
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

/-- Hash the shared producer/config input bytes once in Lake's job graph. -/
package_facet reportProducer (pkg : Package) : Unit := withCurrPackage pkg do
  let config ← readJson (← (← fetch <| pkg.facet `reportInputs).await)
  let producers ← strings config "producers"
  let configs ← strings config "configs"
  let mut deps := Job.nil
  for path in producers ++ configs do
    deps := deps.mix (← inputBinFile (pkg.dir / path))
  return deps

/-- Native artifacts are optional inputs. A rejected local/restored artifact is
rebuilt exactly once in the private build tree, with cache reads disabled for
that reconstruction. Never write through a restored hard link or evict a blob. -/
private def checkedArtifact (pendingRows : PendingRows) (pkg : Package) (file : FilePath)
    (build : JobM PUnit) (check : Array String) : JobM FilePath := do
  let trace ← getTrace
  let art ← buildArtifactUnlessUpToDate file build (ext := "zip") (restore := true)
  let status ← validateArtifact pendingRows pkg (check ++ #[art.path.toString])
  if status == 0 then return art.path
  logWarning s!"inspector artifact rejected; rebuilding privately: {file}"
  removeFileIfExists file
  removeFileIfExists (file.addExtension "trace")
  clearFileHash file
  setTrace trace
  let recovered ← withCurrPackage? none <|
    buildArtifactUnlessUpToDate file build (ext := "zip") (restore := true)
  unless (← validateArtifact pendingRows pkg (check ++ #[recovered.path.toString])) == 0 do
    error s!"reconstructed Inspector artifact is invalid: {file}"
  return recovered.path

module_facet report (mod : Module) : FilePath := withCurrPackage mod.pkg do
  let pkg := mod.pkg
  let pendingRows ← (← fetch <| pkg.facet `reportBatch).await
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
  let inspector ← reportInspector.fetch
  deps := deps.mix inspector
  let workspace ← getWorkspace
  let env := #[ ("LEAN_PATH", some workspace.leanPath.toString) ]
  let file := pkg.buildDir / "lean-inspector" / "modules" / s!"{mod.name}.zip"
  deps.mapM fun _ => do
    -- Inspector reads private declarations and values, including the complete
    -- transitive closure of external utility claims.
    for exportJob in exports do
      let info ← exportJob.await
      addTrace (info.allArtsTrace.mix info.allTransTrace)
    let executable ← inspector.await
    checkedArtifact pendingRows pkg file
      (produceRow pendingRows pkg #[pkg.dir.toString, mod.name.toString, mod.leanFile.toString,
        utility.toString, executable.toString, file.toString] env)
      #["module", pkg.dir.toString, mod.name.toString, utility.toString]

package_facet report (pkg : Package) : FilePath := withCurrPackage pkg do
  let pendingRows ← (← fetch <| pkg.facet `reportBatch).await
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
      rows := rows.push (← fetch <| mod.facet `report)
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
      let requestFile := pkg.buildDir / "lean-inspector" / "batch.json"
      let resultFile := pkg.buildDir / "lean-inspector" / "batch-results.json"
      IO.FS.writeFile requestFile (Lean.toJson (requests.map fun r => (r.kind, r.args))).compress
      let env := #[("LEAN_PATH", some (← getWorkspace).leanPath.toString)]
      try
        let result ← IO.Process.output { (nativeCommand pkg #["batch", requestFile.toString, resultFile.toString]) with env }
        unless result.stdout.isEmpty do logInfo result.stdout
        unless result.stderr.isEmpty do logInfo result.stderr
        unless result.exitCode == 0 do error s!"Inspector batch exited with code {result.exitCode}"
        let statuses : Array Nat ← IO.ofExcept (Lean.fromJson? (← readJson resultFile))
        unless statuses.size == requests.size do error "Inspector batch result count mismatch"
        for (request, status) in requests.zip statuses do request.done.resolve status.toUInt32
        removeFileIfExists requestFile
        removeFileIfExists resultFile
      finally
        for request in requests do request.done.resolve 1
  finally
    pendingRows.set none
    for request in (← queue.get) do request.done.resolve 1
  let membership ← inputBinFile inputs
  (Job.collectArray rows |>.zipWith (fun paths _ => paths) membership).mapM fun rowPaths => do
    let paths := rowPaths.map (·.toString)
    let file := pkg.buildDir / "lean-inspector" / "report.zip"
    checkedArtifact pendingRows pkg file (do
      proc (nativeCommand pkg (#["aggregate", pkg.dir.toString, file.toString] ++ paths))
      pure PUnit.unit) #["report", pkg.dir.toString]
