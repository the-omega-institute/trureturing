module
public import Lean
public import OmegaChecks.InitCompiler.NaturalBootstrap
import OmegaChecks.InitCompiler.RootNames
public import OmegaChecks.InitCompiler.CompilerMarkers

open Lean

namespace OmegaChecks.InitPort.NativeQuot

open InitCompiler.RootNames (quotientPrimitives quotientInterface)
/-- Root names required by the kernel, pattern elaborator and native compiler. -/
public def isSupport (owner name : Name) : Bool :=
  owner == `OmegaInit.Prelude && (quotientPrimitives.contains name || CompilerMarkers.names.contains name)

private def officialSupport : IO (Array ConstantInfo) := do
  let lib ← getLibDir (← findSysroot)
  let path := modToFilePath lib `Init.Prelude "olean"
  let modules ← readModuleDataParts #[path, path.addExtension "server", path.addExtension "private"]
  let data := (modules.map Prod.fst)[0]!
  quotientPrimitives.mapM fun n => do
    let some ci := data.constants.find? (·.name == n)
      | throw <| IO.userError s!"missing pinned quotient declaration {n}"
    return ci

/-- Inspect the normal form itself. Proof irrelevance alone would also prove a
propositional equality between the induction result and its constructor branch. -/
private def checkReduction (env : Environment) (ci : ConstantInfo) : IO Unit := do
  let levels := ci.levelParams.map Level.param
  let check : MetaM Unit := Meta.forallTelescope ci.type fun xs _ =>
    Meta.withLocalDeclD `representative xs[0]! fun a => do
      let mk := mkAppN (mkConst `Omega.Quot.mk [levels.head!]) #[xs[0]!, xs[1]!, a]
      let call := mkAppN (mkConst ci.name levels) (xs.pop.push mk)
      let .ok result := Kernel.whnf env (← getLCtx) call
        | throwError "failed to reduce {ci.name}"
      unless result == mkApp xs[3]! a do throwError "invalid constructor reduction for {ci.name}"
  check.run' |>.toIO' {fileName := "<native quotient>", fileMap := default} {env}

/-- Replay regenerates quotient primitives from their fixed names. Check the serialized
types, kinds and owners too, including every physical copy before replay. -/
public def checkSupport (env : Environment) (level := OLeanLevel.private) : IO Unit := do
  InitCompiler.checkNaturalBasis env level
  CompilerMarkers.check env
  let mut found := #[]
  for owner in env.header.moduleNames, data in env.header.moduleData do
    for n in data.constNames, ci in data.constants do
      if quotientPrimitives.contains n || quotientPrimitives.contains ci.name || ci matches .quotInfo _ then
        unless n == ci.name && isSupport owner n do
          throw <| IO.userError s!"unexpected native quotient support {owner}/{n}"
        found := found.push ci
  if found.isEmpty then return
  let expected ← officialSupport
  unless found.size == expected.size do throw <| IO.userError "incomplete or duplicated native quotient support"
  for standard in expected do
    let some ci := found.find? (·.name == standard.name)
      | throw <| IO.userError s!"missing native quotient support {standard.name}"
    unless ci == standard && ci.type.equal standard.type &&
        (ci.value?.map ExprStructEq.mk) == (standard.value?.map ExprStructEq.mk) do
      throw <| IO.userError s!"invalid native quotient support {ci.name}"
    if let .recInfo a := ci then
      let .recInfo b := standard | throw <| IO.userError s!"invalid recursor {ci.name}"
      unless (a.rules.zip b.rules).all (fun (x,y) => x.rhs.equal y.rhs) do
        throw <| IO.userError s!"invalid native reduction rule {ci.name}"

    if quotientPrimitives.contains standard.name then
      let name := `Omega ++ standard.name
      let some idx := env.getModuleIdxFor? name | throw <| IO.userError s!"missing quotient interface {name}"
      let some (.defnInfo wrapper) := env.find? name | throw <| IO.userError s!"sealed quotient interface {name}"
      unless env.header.moduleNames[idx]! == `OmegaInit.Prelude && wrapper.safety == .safe &&
          wrapper.levelParams == standard.levelParams && wrapper.type.equal (quotientInterface standard).type do
        throw <| IO.userError s!"invalid quotient interface {name}"
      if [`Quot.lift, `Quot.ind].contains standard.name then checkReduction env (.defnInfo wrapper)

/-- The canonical quotients use the same kernel equality as the strict interfaces. -/
public def prepareSeed (dir : System.FilePath) : IO Unit := do
  let official ← officialSupport
  let additions := official ++ CompilerMarkers.names.map CompilerMarkers.declaration ++
    official.map fun ci => ConstantInfo.defnInfo (quotientInterface ci)
  let path := modToFilePath dir `OmegaInit.Prelude "olean"
  let paths := #[path, path.addExtension "server", path.addExtension "private"]
  let old ← readModuleDataParts paths
  let mut parts := #[]
  for (data, _) in old, file in paths do
    let mut terms := data.constants
    for ci in additions do
      if let some prev := terms.find? (·.name == ci.name) then
        unless prev == ci && prev.type.equal ci.type &&
            (prev.value?.map ExprStructEq.mk) == (ci.value?.map ExprStructEq.mk) do
          throw <| IO.userError s!"conflicting seed declaration {ci.name}"
      else terms := terms.push ci
    terms := terms.qsort fun a b => a.name.quickCmp b.name == .lt
    parts := parts.push (file, {data with constants := terms, constNames := terms.map (·.name)})
  saveModuleDataParts `OmegaInit.Prelude parts

end OmegaChecks.InitPort.NativeQuot
