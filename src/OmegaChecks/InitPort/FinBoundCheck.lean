module
import all OmegaChecks.InitInventory.OriginalType
import OmegaChecks.InitPort.StrictReplay
meta import OmegaChecks.InitInventory.OriginalType
meta import OmegaChecks.InitPort.StrictReplay

open Lean InitKernelPort OmegaChecks.InitPort OmegaChecks.InitInventory

/-- Check the complete public types and replay the equations with their constructive index bounds. -/
public unsafe def main (args : List String) : IO Unit := do
  let [lib] := args | throw <| IO.userError "expected a strict library"
  initSearchPath (← findSysroot)
  let officialPath ← searchPathRef.get
  for carrier in [`List, `Array] do
    let owner := `Init.Data ++ carrier ++ `Find
    let name := carrier ++ `findFinIdx?_eq_pmap_findIdx?
    let strictOwner := owner.replacePrefix `Init `OmegaInit
    let moduleFile := System.FilePath.mk lib / (strictOwner.toString.replace "." "/" ++ ".olean")
    if !(← moduleFile.pathExists) then continue
    searchPathRef.set officialPath
    let visible ← importModules #[{module := owner}] {} (level := .exported)
    let some src := visible.find? name | throw <| IO.userError s!"missing official {name}"
    searchPathRef.set [lib]
    let strict ← importModules #[{module := strictOwner}] {} (level := .exported)
    let some dst := strict.find? (portName name) | continue
    let pinned := src.type.instantiateLevelParams src.levelParams (dst.levelParams.map Level.param)
    unless visible.getModuleIdxFor? name == visible.getModuleIdx? owner &&
        strict.getModuleIdxFor? dst.name == strict.getModuleIdx? strictOwner &&
        src.numLevelParams == dst.numLevelParams && (Kernel.check visible {} pinned).isOk &&
        typeNeedsConstant visible pinned `propext &&
        !strict.contains (portName `propext) && checkedFinBound visible strict owner name pinned dst.type do
      throw <| IO.userError s!"the public types of {name} do not agree after replacing the Fin bound proof"
    let full ← importModules #[{module := strictOwner, importAll := true}] {}
    let _ ← replayStrict full.toKernelEnv #[dst.name]
    IO.println (toJson #[owner.toString, name.toString]).compress
