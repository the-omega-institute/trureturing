module
import OmegaChecks.InitPort.StrictReplay
import OmegaChecks.InitPort.PublicTypeClient
meta import OmegaChecks.InitPort.StrictReplay
meta import OmegaChecks.InitPort.PublicTypeClient

open Lean Meta InitKernelPort OmegaChecks.InitPort

private def changedResult : Expr → Expr
  | .forallE n type body bi => .forallE n type (changedResult body) bi
  | _ => mkConst `False

private def converts (env : Environment) (common pinned : Expr) : Bool :=
  (Kernel.check env {} common).isOk && (Kernel.check env {} pinned).isOk && Kernel.isDefEqGuarded env {} common pinned

/-- Compose the public range theorem with the public description of the slice contents.
The strict proof supplies its own finite collector at the intermediate equality. -/
private def extractedRange (decl : ConstantInfo) (originalType : Expr) (base : Name)
    (port : Name → Name) : MetaM (Expr × Expr × Expr) := do
  forallTelescope decl.type fun xs body => do
    let some (_, _, rhs) := body.eq? | throwError "expected a range equation"
    let some (_, lhs, _) := (originalType.getForallBody.instantiateRev xs).eq?
      | throwError "expected an original range equation"
    unless lhs.getAppFn.isConstOf (port `Std.Slice.toList) do throwError "expected the pinned slice collector"
    let contents ← mkAppOptM (port base) #[none, lhs.getAppArgs.back!]
    let some (_, _, extracted) := (← inferType contents).eq? | throwError "expected a slice contents equation"
    let law := mkAppN (mkConst decl.name (decl.levelParams.map Level.param)) xs
    let inverse ← mkAppM (port `Eq.symm) #[contents]
    let proof ← mkLambdaFVars xs (← mkAppM (port `Eq.trans) #[inverse, law])
    let expected ← mkForallFVars xs (← mkEq extracted rhs)
    let shortened ← mkForallFVars xs (← mkEq extracted (← mkAppM (port `List.tail) #[rhs]))
    return (proof, expected, shortened)

private def rangeContents? (owner name : Name) : Option Name := do
  let (container, base) ← match owner with
    | `Init.Data.Slice.List.Lemmas => some (`List, `ListSlice.toList_eq)
    | `Init.Data.Slice.Array.Lemmas => some (`Array, `Subarray.toList_eq)
    | _ => none
  guard (["rco", "rcc", "rci", "roo", "roc", "roi", "rio", "ric", "rii"].any fun r =>
    name == container.str ("toList_mkSlice_" ++ r))
  return base

private def checkExtractedRange (visible strict : Environment) (src dst : ConstantInfo)
    (pinned : Expr) (base : Name) : IO Unit := do
  let ctx := {fileName := "<slice range>", fileMap := default : Core.Context}
  let (officialProof, expected, wrong) ← ((extractedRange src src.type base id).run').toIO' ctx {env := visible}
  let (strictProof, _, _) ← ((extractedRange dst (translate portName pinned) base portName).run').toIO' ctx {env := strict}
  let specialize := fun (t : Expr) => translate portName
    (t.instantiateLevelParams src.levelParams (dst.levelParams.map Level.param))
  for (env, proof, ty, shortened) in [(visible, officialProof, expected, wrong),
      (strict, strictProof, specialize expected, specialize wrong)] do
    let .ok actual := Kernel.check env {} proof | throw <| IO.userError s!"invalid range proof at {src.name}"
    unless converts env actual ty && (Kernel.check env {} shortened).isOk &&
        !Kernel.isDefEqGuarded env {} actual shortened do
      throw <| IO.userError s!"the extracted range differs at {src.name}"

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
    let collectOwner := `OmegaInit.Data.Iterators.Consumers.Collect
    let withCollect ← if owner == `Init.Data.Slice.Array.Lemmas then
      importModules #[{module := strictOwner}, {module := collectOwner}] {} (level := .exported)
      else pure strict
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
      let ordinaryWithCollect := !ordinary && converts withCollect lifted dst.type
      let mode := if ordinary then "ordinary" else if ordinaryWithCollect then "with-collect" else "all"
      if ordinary || ordinaryWithCollect then
        if let some base := rangeContents? owner name then
          checkExtractedRange visible withCollect src dst pinned base
          roots := roots.push (portName base)
      let wrong := changedResult common
      unless (Kernel.check expanded {} wrong).isOk && !Kernel.isDefEqGuarded expanded {} common wrong do
        throw <| IO.userError s!"unexpected unchanged result for {name}"
      roots := roots.push dst.name
      let target := entry.path / mode
      IO.FS.createDirAll target
      for (isStrict, mod, n, ty, bad) in [(false,owner,name,common,wrong),
          (true,strictOwner,dst.name,lifted,translate portName wrong)] do
        let variant := if isStrict then "Strict" else "Official"
        let singleImport := isStrict && ordinary
        for (suffix, formula) in [("",ty), ("Changed",bad), ("Ordinary",ty)] do
          let file := target / (variant ++ suffix ++ ".lean")
          if suffix == "Ordinary" && singleImport then continue
          let access := if suffix == "Ordinary" || singleImport then s!"import {mod}"
            else if isStrict && ordinaryWithCollect then s!"import {mod}\nimport {collectOwner}"
            else s!"import all {mod}"
          if !(← file.pathExists) then
            IO.FS.writeFile file s!"module\nprelude\n{access}\nset_option autoImplicit false\nset_option linter.unusedVariables false\n"
          let handle ← IO.FS.Handle.mk file .append
          handle.putStr (PublicTypeClient.client formula n dst.levelParams)
      IO.println (toJson #[owner.toString,name.toString,mode]).compress
    let _ ← replayStrict full.toKernelEnv roots
