import Lake
import Lake.CLI.Build
import Lake.Load.Manifest
import Lake.Util.StoreInsts
import Std.Sync.Mutex
open Lake DSL System
open Lean (Json)

package leanInspector where
  buildDir := "../../.lake/build/lean-inspector/producer"

target nativeImage pkg : FilePath := do
  buildLeanO (pkg.buildDir / "c" / "native_image.o")
    (← inputFile (pkg.dir / "native_image.c") true) #[] #["-O3", "-DLEAN_EXPORTING"]

lean_exe reportInspector where
  root := `Inspector
  supportInterpreter := true
  moreLinkObjs := #[{key := .mk (.packageTarget .anonymous `nativeImage)}]

private def inspectorDir (pkg : Package) : FilePath := pkg.dir / "tools" / "lean-inspector"

private def nativeCommand (pkg : Package) (args : Array String) : IO.Process.SpawnArgs :=
  { cmd := "python3", args := #[((inspectorDir pkg) / "native.py").toString] ++ args,
    cwd := some pkg.dir }

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
  validation : Std.Mutex Unit

package_facet reportBatch (_pkg : Package) : ReportState := do
  Job.async do return ⟨← IO.mkRef {}, ← IO.mkRef none, ← Std.Mutex.new ()⟩

private def validateArtifact (pkg : Package) (args : Array String) : JobM UInt32 := do
  return (← IO.Process.output (nativeCommand pkg (#["validate"] ++ args))).exitCode

private def readJson (path : FilePath) : IO Json := do
  IO.ofExcept (Json.parse (← IO.FS.readFile path))

private def writeBinFileIfChanged (path : FilePath) (contents : ByteArray) : IO Unit := do
  IO.FS.createDirAll (path.parent.getD ".")
  let unchanged ← try
    pure ((← IO.FS.readBinFile path) == contents)
  catch _ =>
    pure false
  unless unchanged do
    IO.FS.writeBinFile path contents

private def strings (json : Json) (key : String) : IO (Array String) :=
  IO.ofExcept (json.getObjValAs? (Array String) key)

private def packageInputDescriptor (ws : Workspace) (pkg : Package)
    (manifest : Manifest) : IO Json := do
  let mut modules : Array Json := #[]
  let mut names : Lean.NameSet := {}
  for lib in pkg.leanLibs do
    let candidates ← IO.mkRef (← lib.getModuleArray)
    -- Library globs select build defaults, whereas roots also own imported
    -- submodules outside those globs (for example Batteries.CodeAction).
    for name in lib.roots do
      if let some mod := lib.findModule? name then
        if ← mod.leanFile.pathExists then candidates.modify (·.push mod)
      if ← (Lean.modToFilePath lib.srcDir name "").isDir then
        (Glob.submodules name).forEachModuleIn lib.srcDir fun name => do
          if let some mod := lib.findModule? name then
            candidates.modify (·.push mod)
    for mod in (← candidates.get) do
      if names.contains mod.name then continue
      names := names.insert mod.name
      if (ws.findModules mod.name).size != 1 then
        throw <| IO.userError s!"ambiguous native module owner: {mod.name}"
      modules := modules.push <| Lean.Json.mkObj [
        ("name", Lean.toJson mod.name.toString),
        ("path", Lean.toJson mod.relLeanFile.normalize.toString)]
  let mut sourceRoots : Array FilePath := #[]
  for lib in pkg.leanLibs do
    -- Keep the lexical path supplied to Lake. pkg.dir/lib.srcDir have already
    -- resolved/normalized aliases; the source validator must see every hop.
    let sourceDir := pkg.relDir / pkg.config.srcDir / lib.config.srcDir
    for name in lib.roots do
      sourceRoots := sourceRoots.push (Lean.modToFilePath sourceDir name "lean")
      sourceRoots := sourceRoots.push (Lean.modToFilePath sourceDir name "")
    for glob in lib.config.globs do
      match glob with
      | .one name => sourceRoots := sourceRoots.push (Lean.modToFilePath sourceDir name "lean")
      | .submodules name => sourceRoots := sourceRoots.push (Lean.modToFilePath sourceDir name "")
      | .andSubmodules name =>
        sourceRoots := sourceRoots.push (Lean.modToFilePath sourceDir name "lean")
        sourceRoots := sourceRoots.push (Lean.modToFilePath sourceDir name "")
  -- Producer executables retain their existing registered input population.
  -- An executable default is unaccounted for the entry shortcut below.
  let roots := sourceRoots.map fun path => Lean.toJson path.toString
  pure <| Lean.Json.mkObj [
    ("owner", Lean.toJson pkg.baseName.toString),
    ("dir", Lean.toJson pkg.relDir.toString),
    ("source_roots", Lean.Json.arr roots),
    ("config_paths", Lean.toJson #[pkg.relConfigFile.toString,
      pkg.relManifestFile.toString, defaultLeanConfigFile.toString,
      defaultTomlConfigFile.toString, "lean-toolchain"]),
    ("remote_url", Lean.toJson pkg.remoteUrl),
    ("scope", Lean.toJson pkg.scope),
    ("pin", Lean.toJson (manifest.packages.find? (·.name == pkg.baseName))),
    ("modules", Lean.Json.arr modules)]

private def writeNativeInputDescriptor (ws : Workspace) (pkg : Package) (path : FilePath) : IO Unit := do
  let manifest ← Manifest.load ws.root.manifestFile
  let mut packages : Array Json := #[]
  for candidate in ws.packages do
    if candidate.isRoot || !candidate.leanLibs.isEmpty then
      packages := packages.push (← packageInputDescriptor ws candidate manifest)
  -- Only ordinary native Lean library defaults have a complete file population
  -- here. Custom targets keep their normal Lake obligation on every entry.
  let accounted (lib : LeanLib) :=
    lib.pkg.config.extraDepTargets.isEmpty && lib.config.needs.isEmpty &&
    lib.config.extraDepTargets.isEmpty && lib.moreLinkObjs.isEmpty &&
    lib.moreLinkLibs.isEmpty && lib.plugins.isEmpty && lib.dynlibs.isEmpty &&
    lib.defaultFacets.all (fun facet => #[LeanLib.leanArtsFacet, LeanLib.staticFacet,
      LeanLib.sharedFacet].contains facet) &&
    (lib.nativeFacets false).all (·.name == Module.oFacet) &&
    (lib.nativeFacets true).all (·.name == Module.oExportFacet)
  let complete := (ws.packages.all fun candidate => candidate.leanLibs.all accounted) &&
    pkg.config.extraDepTargets.isEmpty && pkg.defaultTargets.all fun name =>
    match pkg.findLeanLib? name with
    | none => false
    | some lib => accounted lib
  let excluded := ws.packages.flatMap fun candidate =>
    #[Lean.toJson (relPathFrom ws.dir candidate.buildDir).normalize.toString,
      Lean.toJson (relPathFrom ws.dir candidate.lakeDir).normalize.toString]
  let value := Lean.Json.mkObj [
    ("kind", Lean.toJson ("lake-fetched" : String)),
    ("complete_defaults", Lean.toJson complete),
    -- Workspace.pkgsDir is rooted at ws.root.dir. Preserve the configured
    -- spelling before Package.relPkgsDir.normalize can erase aliases.
    ("packages_dir", Lean.toJson ws.root.config.packagesDir.toString),
    ("workspace_overrides", Lean.toJson (relPathFrom ws.dir ws.packageOverridesFile).toString),
    ("excluded_dirs", Lean.Json.arr excluded),
    ("packages", Lean.Json.arr packages)]
  writeBinFileIfChanged path (String.toUTF8 value.compress)

/-- Utility input is generated once per invocation by its existing .NET owner.
This job deliberately has no content trace: each module traces its own record. -/
package_facet reportInputs (pkg : Package) : FilePath := do
  let ws ← getWorkspace
  Job.async do
    let descriptor := pkg.buildDir / "lean-inspector" / "lake-inputs.json"
    writeNativeInputDescriptor ws pkg descriptor
    proc (nativeCommand pkg #["prepare", pkg.dir.toString, "--lake-inputs", descriptor.toString])
    return pkg.buildDir / "lean-inspector" / "inputs.json"

package_facet reportSourceModules (pkg : Package) : Lean.NameSet := do
  (← fetch <| pkg.facet `reportInputs).mapM fun path => do
    let names ← strings (← readJson path) "modules"
    return names.foldl (fun set name => set.insert name.toName) {}

/-- Trace semantic compatibility after validating registered inputs.
Raw configuration identity belongs to the aggregate; module exports carry
Lake's compiler dependencies. Producer compilation is a separate obligation. -/
package_facet reportProducer (pkg : Package) : Unit := withCurrPackage pkg do
  discard <| (← fetch <| pkg.facet `reportInputs).await
  return Job.nil.mix (← inputBinFile (pkg.buildDir / "lean-inspector" / "compatibility"))

/-- A completed native build, not yet accepted by the canonical validator.
Only private jobs carry this value; it is never a public report facet. -/
private structure UnvalidatedArtifact where
  file : FilePath
  path : FilePath
  inputTrace : BuildTrace
  outputTrace : IO.Ref BuildTrace
  build : JobM PUnit
  check : Array String
  productionArgs? : Option (Array String) := none

private def uncheckedArtifact (file : FilePath) (build : JobM PUnit)
    (check : Array String) : JobM UnvalidatedArtifact := do
  let inputTrace ← getTrace
  let art ← buildArtifactUnlessUpToDate file build (ext := "zip") (restore := true)
  return ⟨file, art.path, inputTrace, ← IO.mkRef (← getTrace), build, check, none⟩

/-- Validator rejection also requires a rebuild. Preserve Lake's native job
decision before scheduling repair production or removing rejected outputs. -/
private def requireRebuildAllowed : JobM Unit := do
  if (← getNoBuild) then
    modify ({· with wantsRebuild := true})
    error "target is out-of-date and needs to be rebuilt"

/-- Rejected optional artifacts are rebuilt exactly once through Lake, with
cache reads disabled for that reconstruction. Never write through a restored
hard link or evict a blob. Required build and validation failures propagate. -/
private def rebuildRejectedArtifact (pkg : Package) (row : UnvalidatedArtifact)
    (build? : Option (JobM PUnit) := none) (validated := false) : JobM FilePath := do
  requireRebuildAllowed
  logWarning s!"inspector artifact rejected; rebuilding privately: {row.file}"
  removeFileIfExists row.file
  removeFileIfExists (row.file.addExtension "trace")
  clearFileHash row.file
  setTrace row.inputTrace
  let recovered ← withCurrPackage? none <|
    buildArtifactUnlessUpToDate row.file (build?.getD row.build) (ext := "zip") (restore := true)
  unless validated do
    unless (← validateArtifact pkg (row.check ++ #[recovered.path.toString])) == 0 do
      error s!"reconstructed Inspector artifact is invalid: {row.file}"
  row.outputTrace.set (← getTrace)
  return recovered.path

private def acceptArtifact (pkg : Package) (row : UnvalidatedArtifact) : JobM FilePath := do
  if (← validateArtifact pkg (row.check ++ #[row.path.toString])) != 0 then
    return ← rebuildRejectedArtifact pkg row
  setTrace (← row.outputTrace.get)
  return row.path

/-- Ask Lake itself whether a native artifact can be reused/restored. A native
`noBuild` miss is data for a subsequent dependency job, not a blocked worker.
All other failures (and a caller's actual `--no-build`) propagate unchanged. -/
private def probeArtifact (file : FilePath) (build : JobM PUnit)
    (check : Array String) : JobM (Option UnvalidatedArtifact) := .ofFn fun fetch pkg? stack store ctx state => do
  let result ← (uncheckedArtifact file build check).toFn fetch pkg? stack store
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
  artifact? : Option UnvalidatedArtifact

-- These private jobs are interned in Lake's invocation store. Neither data
-- key is a public facet capable of returning an unchecked artifact.
module_data inspectorPreparedReport : PreparedArtifact
module_data inspectorUnvalidatedReport : UnvalidatedArtifact

private def prepareNativeModuleReport (mod : Module) : FetchM (Job PreparedArtifact) := withCurrPackage mod.pkg do
  let pkg := mod.pkg
  discard <| (← fetch <| pkg.facet `reportInputs).await
  let utility := pkg.buildDir / "lean-inspector" / "inputs" / s!"{mod.name}.json"
  let record ← readJson utility
  let claims ← strings record "claims"
  let reported ← (← fetch <| pkg.facet `reportSourceModules).await
  let mut deps ← fetch <| pkg.facet `reportProducer
  deps := deps.mix (← inputBinFile mod.leanFile)
  deps := deps.mix (← inputBinFile utility)
  let mut exports := #[(← mod.exportInfo.fetch)]
  let mut sourceModules := #[mod]
  sourceModules := sourceModules ++ (← (← mod.transImports.fetch).await)
  -- Inspector loads this fixed judge even for an empty registration inventory.
  -- Demand and trace its native closure independently of the reported module.
  let some driver := (← getWorkspace).findModule? `LeanInformationAudit.Registry
    | error "IE-C050 reason=incomplete_closure rule=dtr.report_producer"
  exports := exports.push (← driver.exportInfo.fetch)
  sourceModules := sourceModules.push driver ++ (← (← driver.transImports.fetch).await)
  for name in claims do
    let some claim := (← getWorkspace).findModule? name.toName
      | error s!"utility claim module is not in the Lake workspace: {name}"
    exports := exports.push (← claim.exportInfo.fetch)
    sourceModules := sourceModules.push claim ++ (← (← claim.transImports.fetch).await)
  -- Bind the complete native import, fixed judge and utility claim closures.
  let mut sourcePaths : Array String := #[]
  let mut externalSources : Array Json := #[]
  let ws ← getWorkspace
  let mut seen : Lean.NameSet := {}
  for dependency in sourceModules do
    if seen.contains dependency.name then continue
    seen := seen.insert dependency.name
    unless (ws.findModules dependency.name).size == 1 do
      error s!"ambiguous native module owner: {dependency.name}"
    if dependency.name != mod.name && reported.contains dependency.name then continue
    if dependency.pkg.isRoot then
      let path := (relPathFrom pkg.dir dependency.leanFile).toString
      sourcePaths := sourcePaths.push path
    else
      externalSources := externalSources.push <| Lean.Json.mkObj [
        ("owner", Lean.toJson dependency.pkg.baseName.toString),
        ("module", Lean.toJson dependency.name.toString),
        ("path", Lean.toJson dependency.relLeanFile.toString)]
  writeBinFileIfChanged (utility.addExtension "sources.json")
    (String.toUTF8 (Lean.Json.mkObj [
      ("local", Lean.toJson sourcePaths), ("external", Lean.Json.arr externalSources)]).compress)
  -- Await without mixing: recompilation must succeed, but its implementation
  -- identity is not a report-semantic dependency.
  let inspector ← reportInspector.fetch
  let workspace ← getWorkspace
  let env := workspace.augmentedEnvVars
  let file := pkg.buildDir / "lean-inspector" / "modules" / s!"{mod.name}.zip"
  (deps.add (Job.mixArray exports) |>.add inspector).mapM fun _ => do
    -- Inspector's private import mode reads transitive private values, also
    -- through public imports. Lake's legacy trace follows that same closure;
    -- allTransTrace follows each import's visibility and can omit those values.
    -- Apply this to the module and every external utility claim.
    for exportJob in exports do
      let info ← exportJob.await
      addTrace (info.allArtsTrace.mix info.legacyTransTrace)
    let executable ← inspector.await
    let args := #[pkg.dir.toString, mod.name.toString, mod.leanFile.toString,
      utility.toString, executable.toString, file.toString]
    let build := do
      proc { (nativeCommand pkg (#["module"] ++ args)) with env }
      pure PUnit.unit
    let inputTrace ← getTrace
    let artifact? ← probeArtifact file build
      #["module", pkg.dir.toString, mod.name.toString, utility.toString]
    return ⟨file, args, env, inputTrace, artifact?.map fun row => {row with productionArgs? := some args}⟩

private def preparedModuleReport (mod : Module) : FetchM (Job PreparedArtifact) := do
  let key := (mod.facet `inspectorPreparedReport).key
  let job : Job (BuildData key) ← fetchOrCreate key do
    let job ← prepareNativeModuleReport mod
    return cast (by simp [key]) job
  return cast (by simp [key]) job

private def buildNativeModuleReport (mod : Module) : FetchM (Job UnvalidatedArtifact) := withCurrPackage mod.pkg do
  let pkg := mod.pkg
  let reportState ← (← fetch <| pkg.facet `reportBatch).await
  reportState.started.modify (·.insert mod.name)
  let prepared ← preparedModuleReport mod
  let batch? ← reportState.batch.get
  let batch? := batch?.filter fun (members, _) => members.contains mod.name
  let ready := match batch? with | some (_, batch) => prepared.add batch | none => prepared
  ready.mapM fun request => do
    setTrace request.inputTrace
    if let some row := request.artifact? then
      setTrace (← row.outputTrace.get)
      return row
    let direct := do
      proc { (nativeCommand pkg (#["module"] ++ request.args)) with env := request.env }
      pure PUnit.unit
    let pending := request.file.addExtension "pending"
    let build := if batch?.isSome then do
        IO.FS.rename pending request.file
        pure PUnit.unit
      else direct
    try
      let row ← uncheckedArtifact request.file build
        #["module", pkg.dir.toString, mod.name.toString, request.args[3]!]
      -- A rejected optional output reconstructs through the same native owner,
      -- outside the initial shared production job, with cache reads disabled.
      return {row with build := direct, productionArgs? := some request.args}
    finally
      if batch?.isSome then removeFileIfExists pending

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
  let env := (← getWorkspace).augmentedEnvVars
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
  observePhase "lake-inputs" "start"
  let reportState ← (← fetch <| pkg.facet `reportBatch).await
  let inputs ← (← fetch <| pkg.facet `reportInputs).await
  let config ← readJson inputs
  let names ← strings config "modules"
  observePhase "lake-inputs" "finish"
  -- Demand ordinary defaults independently of row traces. Audit/default-only
  -- changes still fail the invocation without invalidating unrelated rows.
  let defaults ← match ← (parseTargetSpec (← getWorkspace) s!"@{pkg.baseName}").toBaseIO with
    | .ok specs => pure specs
    | .error err => error err.toString
  observePhase "lake-defaults" "start"
  discard <| (← buildSpecs defaults).await
  observePhase "lake-defaults" "finish"
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
  let batch ← (Job.collectArray prepared).mapM fun artifacts => do
    observePhase "lake-prepare" "finish"
    let requests := artifacts.filterMap fun request =>
      if request.artifact?.isSome then none else
        some ("produce", request.args.set! 5 (request.file.addExtension "pending").toString)
    unless requests.isEmpty do
      discard <| runBatch pkg requests
  let batch ← registerJob "Inspector native production batch" batch
  reportState.batch.set (some (members, batch))
  let mut rows := #[]
  for name in names do
    let some mod := (← getWorkspace).findModule? name.toName
      | error s!"registered report module is not in the Lake workspace: {name}"
    rows := rows.push (← nativeModuleReport mod)
  let membership ← inputBinFile inputs
  ((Job.collectArray rows).zipWith (fun artifacts _ => artifacts) membership).mapM fun artifacts =>
    reportState.validation.atomically do
    let paths := artifacts.map (·.path.toString)
    let file := pkg.buildDir / "lean-inspector" / "report.zip"
    let pending := file.addExtension "pending"
    let direct := do
      proc (nativeCommand pkg (#["aggregate", pkg.dir.toString, file.toString] ++ paths))
      pure PUnit.unit
    let check := #["report", pkg.dir.toString]
    let mut initialTrace := BuildTrace.nil "<collection>"
    for row in artifacts do
      initialTrace := initialTrace.mix (← row.outputTrace.get).withoutInputs
    setTrace (mixTrace initialTrace membership.getTrace)
    let inputTrace ← getTrace
    let aggregate? ← probeArtifact file direct check
    setTrace inputTrace
    -- A single validator invocation checks every actual row and the reused
    -- aggregate, or constructs the missing aggregate from those rows. Its
    -- material identity memo lives only for this invocation; all bytes are
    -- read, CRC-checked and hashed at every validation boundary.
    let requests := artifacts.map fun row =>
      ("validate", #[pkg.dir.toString] ++ row.check ++ #[row.path.toString])
    let aggregateRequest := match aggregate? with
      | some row => ("validate", #[pkg.dir.toString] ++ check ++ #[row.path.toString])
      | none => ("aggregate", #[pkg.dir.toString, pending.toString] ++ paths)
    let repairFiles ← IO.mkRef (#[] : Array FilePath)
    try
      let statuses ← runBatch pkg (requests.push aggregateRequest)
      let mut repairs := #[]
      for (row, status) in artifacts.zip (statuses.extract 0 artifacts.size) do
        if status != 0 then
          let some args := row.productionArgs?
            | error "rejected module artifact has no native production request"
          let repair := row.file.addExtension "repair"
          repairFiles.modify (·.push repair)
          repairs := repairs.push ("produce", args.set! 5 repair.toString)
      -- Missing legacy bindings and corrupt rows are exact validator rejections.
      -- Share extraction/import work, then let each original module job own its
      -- bounded private reconstruction through Lake, with cache reads disabled.
      unless repairs.isEmpty do
        requireRebuildAllowed
        discard <| runBatch pkg repairs
        -- Share one current namespace/configuration snapshot across repair
        -- validation. The aggregate still validates the adopted rows again.
        let checks := repairs.map fun (_, args) => ("validate", #[pkg.dir.toString,
          "module", pkg.dir.toString, args[1]!, args[3]!, args[5]!])
        unless (← runBatch pkg checks).all (· == 0) do
          error "reconstructed Inspector batch is invalid"
      let mut repaired := false
      let mut trace := BuildTrace.nil "<collection>"
      for (row, status) in artifacts.zip (statuses.extract 0 artifacts.size) do
        if status != 0 then
          discard <| rebuildRejectedArtifact pkg row (some do
            IO.FS.rename (row.file.addExtension "repair") row.file
            pure PUnit.unit) (validated := true)
          repaired := true
        trace := trace.mix (← row.outputTrace.get).withoutInputs
      setTrace (mixTrace trace membership.getTrace)
      if !repaired then
        if let some row := aggregate? then
          if statuses[artifacts.size]! == 0 then
            setTrace (← row.outputTrace.get)
            return row.path
          else
            return ← rebuildRejectedArtifact pkg row
      let build := if aggregate?.isNone && !repaired then do
          IO.FS.rename pending file
          pure PUnit.unit
        else direct
      let row ← uncheckedArtifact file build check
      -- The completed new bundle still crosses the full canonical validator.
      acceptArtifact pkg {row with build := direct}
    finally
      removeFileIfExists pending
      for repair in (← repairFiles.get) do removeFileIfExists repair
