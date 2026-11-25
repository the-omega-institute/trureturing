import Lean
import Lean.Replay
import OmegaChecks.Interface
import OmegaChecks.ProtectedObjects
import OmegaChecks.ModuleSurface

open Lean

private def isStrict (name : Name) : Bool :=
  [`OmegaInit, `OmegaMathlib, `OmegaMath].contains name.getRoot

/-- Lean loads imports before importers. Propagate a D5 path along every compiled import,
including private imports, while allowing D5 modules to consume the publication. -/
private def checkPublicationLayers (env : Environment) : IO Unit := do
  let mut paths : NameMap (List Name) := {}
  for (owner, data) in env.header.moduleNames.zip env.header.moduleData do
    if owner.getRoot == `D5 then
      paths := paths.insert owner [owner]
    else
      for dep in data.imports do
        if let some path := paths.find? dep.module then
          let path := owner :: path
          if [`OmegaMath, `OmegaMathlib].contains owner.getRoot then
            throw <| IO.userError s!"forbidden D5 dependency: {String.intercalate " -> " (path.map Name.toString)}"
          paths := paths.insert owner path
          break

/-- Check every import edge, including private and transitive imports of the selected roots. -/
private def checkLayers (env : Environment) : IO Unit := do
  for (owner, data) in env.header.moduleNames.zip env.header.moduleData do
    if isStrict owner then
      let allowed := if owner.getRoot == `OmegaInit then [`OmegaInit]
        else if owner.getRoot == `OmegaMathlib then [`OmegaInit, `OmegaMathlib]
        else [`OmegaInit, `OmegaMathlib, `OmegaMath]
      for dep in data.imports do
        unless allowed.contains dep.module.getRoot do
          throw <| IO.userError s!"forbidden strict import: {owner} imports {dep.module}"

/-- Compare public names and defining modules in a separate upstream environment. -/
private def checkUpstreamNames (strict publicStrict : Environment) : IO Unit := do
  let sysroot ← findSysroot
  let lib ← getLibDir sysroot
  let mut bindings := #[]
  let mut owners ← OmegaChecks.ModuleSurface.officialModules strict lib
  for (name, _) in strict.constants.toList do
    let some idx := strict.getModuleIdxFor? name | continue
    let owner := strict.header.moduleNames[idx]!
    if !isStrict owner || isPrivateName name || name.isInternal then continue
    unless name.getRoot == `Omega do
      throw <| IO.userError s!"public name outside Omega: {name} in {owner}"
    if owner.getRoot == `OmegaMath then continue
    let upstream := if owner.getRoot == `OmegaInit then `Init else `Mathlib
    let official := owner.replacePrefix owner.getRoot upstream
    bindings := bindings.push (name, official)
    if !owners.contains official then owners := owners.push official
  if owners.isEmpty then
    initSearchPath sysroot [lib]
    discard <| OmegaChecks.ModuleSurface.check publicStrict
    return
  let targets := (owners.filter (·.getRoot == `Mathlib)).map fun name => s!"@mathlib/+{name}:olean"
  let proc ← IO.Process.spawn { cmd := "lake", args := #["build", "+OmegaChecks.Interface.Equations"] ++ targets }
  unless (← proc.wait) == 0 do throw <| IO.userError s!"failed to build upstream interfaces {owners}"
  initSearchPath sysroot [lib]
  owners := owners.push `OmegaChecks.Interface.Equations
  let reference ← importModules (owners.map fun moduleName => {module := moduleName}) {}
  for owner in reference.allImportedModuleNames do
    if isStrict owner then
      throw <| IO.userError s!"standard interface evidence imports a strict implementation: {owner}"
  for (name, owner) in bindings do
    let counterpart := name.replacePrefix `Omega Name.anonymous
    let some idx := reference.getModuleIdxFor? counterpart
      | throw <| IO.userError s!"missing official declaration {counterpart} in {owner} for {name}"
    let actual := reference.header.moduleNames[idx]!
    unless actual == owner do
      throw <| IO.userError s!"official owner of {counterpart} is {actual}, expected {owner}"
  let reexports ← OmegaChecks.ModuleSurface.check publicStrict
  OmegaChecks.Interface.check strict publicStrict reference (bindings ++ reexports)
  IO.println s!"Upstream names and owning modules matched for {bindings.size} declarations in {owners}."

/-- Replay the imported artifacts in an empty kernel environment. -/
private def audit (roots : List String) (path label : String)
    (expected : Option (List String)) : IO (List String) := do
  searchPathRef.set (System.SearchPath.parse path)
  let imports := roots.toArray.map fun name => { module := name.toName : Import }
  let env ← importModules imports {}
  -- Each basis module is independently importable, including privately imported dependencies.
  let basis := env.allImportedModuleNames.filter OmegaChecks.ModuleSurface.isBasis
  let publicStrict ← importModules (basis.map fun name => {module := name}) {} (level := .exported)
  checkPublicationLayers env
  checkLayers env
  let actual := env.allImportedModuleNames.toList.map Name.toString
  if let some modules := expected then
    unless actual.mergeSort == modules.mergeSort do
      throw <| IO.userError s!"module closure differs: found {actual}, expected {modules}"
  else
    for name in actual do
      unless isStrict name.toName do
        throw <| IO.userError s!"unexpected strict library import {name}"
  let check : CoreM Nat := do
    let mut count := 0
    for (name, info) in env.constants.toList do
      if info.isUnsafe || info matches .axiomInfo _ | .quotInfo _ then
        throwError "inadmissible declaration {name}"
      let axioms ← collectAxioms name
      unless axioms.isEmpty do
        throwError "{name} depends on {axioms}"
      count := count + 1
    return count
  let count ← check.toIO' {fileName := "<audit>", fileMap := default} {env}
  discard <| (← mkEmptyEnvironment).toKernelEnv.replay env.constants.map₁
  checkUpstreamNames env publicStrict
  IO.println s!"{label}: {actual.length} modules, {count} declarations, zero axioms, fresh kernel replay passed"
  return actual

/-- Measure the published declarations in the official environment, including proof dependencies. -/
private def reportOfficialAxioms (strict official : Environment) (modules : Array Name) (path : String) : IO Unit := do
  let mut names : NameSet := {}
  for owner in official.header.modules, data in official.header.moduleData do
    if modules.contains owner.module then
      for n in data.constNames do
        unless n.isInternal || isPrivateName n do names := names.insert n
  for owner in strict.header.modules, data in strict.header.moduleData do
    if [`OmegaInit, `OmegaMathlib].contains owner.module.getRoot then
      for n in data.constNames do
        unless n.isInternal || isPrivateName n do names := names.insert (n.replacePrefix `Omega .anonymous)
  let collect : CoreM Json := do
    let mut rows := #[]
    for name in names.toList.mergeSort Name.lt do
      let some idx := official.getModuleIdxFor? name | throwError "missing official declaration {name}"
      rows := rows.push <| Json.mkObj [("name", toJson name.toString),
        ("module", toJson official.header.moduleNames[idx]!.toString),
        ("axioms", toJson ((← collectAxioms name).map Name.toString))]
    return Json.mkObj [("backend", "mathlib"), ("consumerModules", toJson (modules.map Name.toString)),
      ("declarations", toJson rows)]
  let report ← collect.toIO' {fileName := "<official axiom dependencies>", fileMap := default} {env := official}
  IO.FS.writeFile path (report.compress ++ "\n")
  IO.println s!"Measured official axiom dependencies for {names.size} declarations."

private def testLibrary (selected : List String) : IO Unit := do
  let args := #["-B", "src/OmegaChecks/check.py", "--library"] ++ selected.toArray
  let proc ← IO.Process.spawn { cmd := "python3", args }
  unless (← proc.wait) == 0 do throw <| IO.userError "Omega library test failed"

def main (args : List String) : IO Unit := do
  if let "--consumer" :: strictPath :: officialPath :: names := args then
    let clients := names.takeWhile (· != "--basis")
    let modules := clients.toArray.map String.toName
    let ports := (names.drop (clients.length + 1)).toArray.map String.toName
    if modules.isEmpty && ports.isEmpty then
      throw <| IO.userError "consumer comparison requires at least one module or standard port"
    unless ports.all OmegaChecks.ModuleSurface.isBasis do throw <| IO.userError "invalid standard port"
    let imports := (modules ++ ports).map fun moduleName => { module := moduleName : Import }
    let strictSearchPath := System.SearchPath.parse strictPath
    searchPathRef.set strictSearchPath
    let strict ← importModules imports {}
    checkPublicationLayers strict
    -- Public visibility is needed for the foundation equations. Consumers may also
    -- use Lean's legacy format, which cannot be imported in an exported context.
    let basis := strict.allImportedModuleNames.filter fun name =>
      name.getRoot == `OmegaInit || name.getRoot == `OmegaMathlib
    let publicStrict ← importModules (basis.map fun name => {module := name}) {} (level := .exported)
    searchPathRef.set (System.SearchPath.parse officialPath)
    let official ← importModules (imports.push { module := `OmegaChecks.Interface.Equations }) {}
    checkPublicationLayers official
    for (owner, data) in official.header.moduleNames.zip official.header.moduleData do
      if owner.getRoot == `OmegaInit || owner.getRoot == `OmegaMathlib then
        unless data.constants.isEmpty do
          throw <| IO.userError s!"official import adapter {owner} contains declarations"
    let inventory : Array OmegaChecks.Interface.FrozenInventory ←
      if let some path ← IO.getEnv "OMEGA_FROZEN_INVENTORY" then
        -- Strict foundation modules may not be official alias facades.
        checkLayers strict
        IO.ofExcept (Json.parse (← IO.FS.readFile path) >>= fromJson?)
      else pure #[]
    let certified ← OmegaChecks.Interface.checkConsumers strict publicStrict official modules strictSearchPath inventory
    if let some path ← IO.getEnv "OMEGA_FROZEN_CERTIFICATE" then
      IO.FS.writeFile path ((toJson certified).compress ++ "\n")
    if let some report ← IO.getEnv "OMEGA_OFFICIAL_AXIOM_REPORT" then
      reportOfficialAxioms strict official modules report
  else if let "--protected-objects" :: basePath :: candidatePath :: modules := args then
    let base := modules.takeWhile (· != "--")
    let "--" :: remaining := modules.drop base.length | throw <| IO.userError "missing candidate module list"
    let candidate := remaining.takeWhile (· != "--legacy")
    let witnesses := (remaining.drop candidate.length).drop 1
    let load (path : String) (roots : List String) := do
      searchPathRef.set (System.SearchPath.parse path)
      importModules (roots.toArray.map fun name => {module := name.toName}) {}
    let old ← load basePath base
    let new ← load candidatePath candidate
    checkPublicationLayers new
    -- A D5 witness is loaded only in the downstream comparison environment.
    let comparison ← if witnesses.isEmpty then pure new else load candidatePath (candidate ++ witnesses)
    OmegaChecks.ProtectedObjects.check old new (base.toArray.map String.toName)
      (candidate.toArray.map String.toName) comparison (witnesses.toArray.map String.toName)
  else if let "--publication-layers" :: path :: roots := args then
    if roots.isEmpty then throw <| IO.userError "expected publication modules"
    searchPathRef.set (System.SearchPath.parse path)
    let env ← importModules (roots.toArray.map fun n => {module := n.toName}) {}
    checkPublicationLayers env
    IO.println s!"D5 isolation passed for {roots.length} compiled roots."
  else if let "--exact-roots" :: path :: names := args then
    let roots := names.takeWhile (· != "--")
    let "--" :: expected := names.drop roots.length | throw <| IO.userError "missing expected module closure"
    if roots.isEmpty then throw <| IO.userError "expected at least one audit root"
    discard <| audit roots path "Omega" (some expected)
  else if let "--exact" :: root :: path :: expected := args then
    discard <| audit [root] path root (some expected)
  else
    testLibrary args
