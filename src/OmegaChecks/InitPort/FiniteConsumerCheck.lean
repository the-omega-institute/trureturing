module
import all OmegaChecks.InitInventory.OriginalType
import OmegaChecks.InitPort.PublicTypeClient
import OmegaChecks.InitPort.StrictReplay
meta import OmegaChecks.InitInventory.OriginalType
meta import OmegaChecks.InitPort.PublicTypeClient
meta import OmegaChecks.InitPort.StrictReplay

open Lean InitKernelPort OmegaChecks.InitPort OmegaChecks.InitInventory

/-- Retain the input telescope and deliberately change the expected result. -/
private def falseResult : Expr → Expr
  | .forallE n type body bi => .forallE n type (falseResult body) bi
  | _ => mkConst `False

public unsafe def main (args : List String) : IO Unit := do
  let [lib, dir] := args | throw <| IO.userError "expected library and module directories"
  initSearchPath (← findSysroot)
  let officialPath ← searchPathRef.get
  for entry in (← (System.FilePath.mk dir).readDir) do
    let file := entry.path / "sites.txt"
    if !(← file.pathExists) then continue
    let owner := entry.fileName.toName
    let strictOwner := owner.replacePrefix `Init `OmegaInit
    searchPathRef.set officialPath
    let visible ← importModules #[{module := owner}] {} (level := .exported)
    enableInitializersExecution
    let official ← importModules #[{module := owner, importAll := true}] {} (loadExts := true)
    searchPathRef.set [lib]
    let strict ← importModules #[{module := strictOwner}] {} (level := .exported)
    let full ← importModules #[{module := strictOwner, importAll := true}] {}
    let mut clients := #[]
    for mod in [owner, strictOwner] do
      let header := s!"module\nprelude\nimport {mod}\nset_option autoImplicit false\nset_option linter.unusedVariables false\n"
      clients := clients ++ #[header, header]
    let mut roots := #[]
    for line in (← IO.FS.lines file) do
      let name := line.toName
      let some src := official.find? name | throw <| IO.userError s!"missing {name}"
      let some dst := strict.find? (portName name) | throw <| IO.userError s!"missing strict {name}"
      unless src.numLevelParams == dst.numLevelParams && full.getModuleIdxFor? dst.name == full.getModuleIdx? strictOwner do
        throw <| IO.userError s!"universe parameters or defining modules differ for {name}"
      let pinned := src.type.instantiateLevelParams src.levelParams (dst.levelParams.map Level.param)
      let missing := (translate portName pinned).getUsedConstants.filter fun d => !strict.contains d
      let .checked ← checkFiniteConsumer official visible strict owner src pinned dst.type missing
        | throw <| IO.userError s!"unverified finite consumer at {name}"
      let common := translate originalName dst.type
      let lifted := translate portName common
      let wrong := falseResult common
      unless (Kernel.check visible {} common).isOk && Kernel.isDefEqGuarded visible {} common pinned &&
          (Kernel.check strict {} lifted).isOk && Kernel.isDefEqGuarded strict {} lifted dst.type &&
          (Kernel.check visible {} wrong).isOk && !Kernel.isDefEqGuarded visible {} common wrong do
        throw <| IO.userError s!"cannot certify the complete public type for {name}"
      roots := roots.push dst.name
      let statements := #[(common, name), (wrong, name), (lifted, dst.name), (translate portName wrong, dst.name)]
      -- The pinned code generator exposes these elimination rules to logical clients only.
      let logical := (src matches .recInfo _) || (name.getString! == "recOn" &&
        (official.find? (name.getPrefix ++ `rec)).any (fun ci => ci matches .recInfo _))
      for (typ, term) in statements, i in [:4] do
        clients := clients.modify i (· ++ PublicTypeClient.client typ term dst.levelParams (!logical))
    let _ ← replayStrict full.toKernelEnv roots
    for body in clients, filename in ["Official", "OfficialChanged", "Strict", "StrictChanged"] do
      IO.FS.writeFile (entry.path / (filename ++ ".lean")) body
    for name in roots do IO.println (toJson #[owner.toString, (originalName name).toString]).compress
