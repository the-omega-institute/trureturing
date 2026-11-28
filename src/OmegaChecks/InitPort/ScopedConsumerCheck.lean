module
import OmegaChecks.InitPort.StrictReplay
import OmegaChecks.InitPort.PublicTypeClient
meta import OmegaChecks.InitPort.StrictReplay
meta import OmegaChecks.InitPort.PublicTypeClient

open Lean InitKernelPort OmegaChecks.InitPort

private def changedResult : Expr → Expr
  | .forallE n type body bi => .forallE n type (changedResult body) bi
  | _ => mkConst `False

private def converts (env : Environment) (common pinned : Expr) : Bool :=
  (Kernel.check env {} common).isOk && (Kernel.check env {} pinned).isOk && Kernel.isDefEqGuarded env {} common pinned

public unsafe def main (args : List String) : IO Unit := do
  let [lib, dir] := args | throw <| IO.userError "expected the strict library and client directory"
  initSearchPath (← findSysroot)
  let officialPath ← searchPathRef.get
  for entry in (← (System.FilePath.mk dir).readDir) do
    let owner := entry.fileName.toName
    let strictOwner := owner.replacePrefix `Init `OmegaInit
    searchPathRef.set officialPath
    let visible ← importModules #[{module := owner}] {} (level := .exported)
    let expanded ← importModules #[{module := owner, importAll := true}] {}
    searchPathRef.set [lib]
    let strict ← importModules #[{module := strictOwner}] {} (level := .exported)
    let full ← importModules #[{module := strictOwner, importAll := true}] {}
    let mut roots := #[]
    for line in (← IO.FS.lines (entry.path / "sites.txt")) do
      let name := line.toName
      let some src := expanded.find? name | continue
      let some dst := full.find? (portName name) | continue
      unless src.isTheorem && dst.isTheorem && !dst.isUnsafe && !dst.isPartial &&
          expanded.getModuleIdxFor? name == expanded.getModuleIdx? owner &&
          full.getModuleIdxFor? dst.name == full.getModuleIdx? strictOwner &&
          src.numLevelParams == dst.numLevelParams do continue
      let pinned := src.type.instantiateLevelParams src.levelParams (dst.levelParams.map Level.param)
      let common := translate originalName dst.type
      let lifted := translate portName common
      unless (visible.find? name).any (fun s => s.type.equal src.type) &&
          (strict.find? dst.name).any (fun s => s.type.equal dst.type) &&
          !converts visible common pinned && converts expanded common pinned && converts full lifted dst.type do continue
      let ordinary := converts strict lifted dst.type
      let wrong := changedResult common
      unless (Kernel.check expanded {} wrong).isOk && !Kernel.isDefEqGuarded expanded {} common wrong do
        throw <| IO.userError s!"unexpected unchanged result for {name}"
      roots := roots.push dst.name
      let target := entry.path / (if ordinary then "ordinary" else "all")
      IO.FS.createDirAll target
      let modeOf := fun (isStrict : Bool) => if isStrict && ordinary then "import " else "import all "
      for (isStrict, mod, n, ty, bad) in [(false,owner,name,common,wrong),
          (true,strictOwner,dst.name,lifted,translate portName wrong)] do
        let variant := if isStrict then "Strict" else "Official"
        let requiresAll := !isStrict || !ordinary
        for (suffix, formula) in [("",ty), ("Changed",bad), ("Ordinary",ty)] do
          let file := target / (variant ++ suffix ++ ".lean")
          if suffix == "Ordinary" && !requiresAll then continue
          let access := if suffix == "Ordinary" then "import " else modeOf isStrict
          if !(← file.pathExists) then
            IO.FS.writeFile file s!"module\nprelude\n{access}{mod}\nset_option autoImplicit false\nset_option linter.unusedVariables false\n"
          let handle ← IO.FS.Handle.mk file .append
          handle.putStr (PublicTypeClient.client formula n dst.levelParams)
      IO.println (toJson #[owner.toString,name.toString,if ordinary then "ordinary" else "all"]).compress
    let _ ← replayStrict full.toKernelEnv roots
