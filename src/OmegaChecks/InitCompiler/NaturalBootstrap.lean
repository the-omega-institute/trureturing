module
import all Lean.Environment
import all Lean.Structure
public import Lean
import Lean.Replay
import OmegaChecks.InitCompiler.Layout
import OmegaChecks.InitCompiler.RootNames

open Lean Elab Command

namespace OmegaChecks.InitCompiler

private structure NaturalBasis where
  terms : Std.HashMap Name ConstantInfo
  exported : NameMap ConstantInfo
  deriving Inhabited

private initialize basisCache : IO.Ref (Option NaturalBasis) ← IO.mkRef none

private def pinnedNaturalBasis : IO NaturalBasis := do
  if let some basis ← basisCache.get then return basis
  let lib ← getLibDir (← findSysroot)
  let p := modToFilePath lib `Init.Prelude "olean"
  let raws ← readModuleDataParts #[p, p.addExtension "server", p.addExtension "private"]
  let src := ((raws.map Prod.fst)[2]!.constants).foldl (init := ({} : NameMap ConstantInfo))
    (fun table ci => table.insert ci.name ci)
  let exported := ((raws.map Prod.fst)[0]!.constants).foldl (init := ({} : NameMap ConstantInfo))
    (fun table ci => table.insert ci.name ci)
  let mut todo := RootNames.natPrimitives
  let mut entries : Std.HashMap Name ConstantInfo := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if entries.contains n then continue
    let some ci := src.find? n | throw <| IO.userError s!"missing official bootstrap object {n}"
    if ci.isUnsafe || ci.isPartial || ci.isAxiom then throw <| IO.userError s!"invalid bootstrap object {n}"
    entries := entries.insert n ci
    todo := todo ++ ci.getUsedConstantsAsSet.toArray
    if let .inductInfo ind := ci then
      todo := todo ++ ind.ctors.toArray ++ ind.all.toArray ++ #[mkRecName n]
  let basis := {terms := entries, exported : NaturalBasis}
  basisCache.set (some basis)
  return basis

public def naturalNames : IO NameSet := do
  return NameSet.ofList (← pinnedNaturalBasis).terms.keys

private def sameEntry (actual expected : ConstantInfo) : Bool := Id.run do
  unless actual == expected && actual.type.equal expected.type &&
      (actual.value? (allowOpaque := true)).map ExprStructEq.mk ==
      (expected.value? (allowOpaque := true)).map ExprStructEq.mk do return false
  if let .recInfo recursor := actual then
    let .recInfo original := expected | return false
    return (recursor.rules.zip original.rules).all fun (a,b) => a.rhs.equal b.rhs
  return true

/-- Every physical bootstrap declaration must be the pinned term at this visibility level. -/
public def checkNaturalBasis (env : Environment) (level : OLeanLevel) : IO Unit := do
  unless env.contains `Nat do return
  let basis ← pinnedNaturalBasis
  let mut seen : NameSet := {}
  for owner in env.header.moduleNames, data in env.header.moduleData do
    for n in data.constNames, ci in data.constants do
      unless basis.terms.contains n || basis.terms.contains ci.name do continue
      let expected := if level == .private then basis.terms[n]? else basis.exported.find? n
      unless owner == `OmegaInit.Prelude && n == ci.name && !seen.contains n &&
          expected.any (sameEntry ci) do
        throw <| IO.userError s!"invalid {repr level} natural bootstrap declaration {owner}/{n}"
      seen := seen.insert n
  for (n, _) in basis.terms do
    unless seen.contains n == (level == .private || basis.exported.contains n) do
      throw <| IO.userError s!"missing {repr level} natural bootstrap declaration {n}"

public def installNaturalBootstrap : CommandElabM Unit := do
  let {terms := entries, exported} ← pinnedNaturalBasis
  let orig ← importModules #[{module := `Init.Prelude}] {}
  let checked ← (← mkEmptyEnvironment).toKernelEnv.replay entries
  let mut env ← getEnv
  let pkg := env.getModulePackage?
  for (n, _) in entries.toList do
    let some ci := checked.find? n | throwError "bootstrap replay omitted {n}"
    if let some existing := env.find? n then
      unless sameEntry existing ci do throwError "bootstrap conflict at {n}"
    else
      let privateEnv := env.lakeAdd ci
      let publicConsts := if let some face := exported.find? n then
        (env.lakeAdd face).asyncConstsMap.public
      else env.asyncConstsMap.public
      env := { privateEnv with asyncConstsMap.public := publicConsts }
  for (n, _) in entries.toList do
    env := (env.registerNamespace n.getPrefix).registerNamespace (`Omega ++ n.getPrefix)
    if isAuxRecursor orig n then env := markAuxRecursor env n
    if isProtected orig n then env := addProtected env n
  let some idx := orig.getModuleIdx? `Init.Prelude | throwError "missing official Prelude"
  for info in structureExt.getModuleEntries orig idx do
    if entries.contains info.structName then env := structureExt.addEntry env info
  for (n, info) in projectionFnInfoExt.getModuleEntries orig idx do
    if entries.contains n then env := projectionFnInfoExt.addEntry (asyncDecl := n) env (n, info)
  for entry in classExtension.getModuleEntries orig idx do
    if entries.contains entry.name then env := classExtension.addEntry env entry
  for (n, status) in reducibilityCoreExt.getModuleEntries orig idx do
    if entries.contains n then env := reducibilityCoreExt.addEntry (asyncDecl := n) env (n, status)
  setEnv (env.setModulePackage pkg)
  liftCoreM <| withExporting do
    for family in #[`Bool, `Nat, `Eq, `PUnit, `PProd, `PULift, `Decidable, `HAdd, `Add, `OfNat, `False, `HEq] do
      let some (.inductInfo ind) := (← getEnv).find? family | continue
      compilerLayouts #[family] ind.ctors.toArray
    for n in #[`Nat.ble, `Nat.beq, `Nat.decEq, `Nat.sub, `Nat.add, `Nat.mul, `Nat.pow] do
      let some attr := getExternAttrData? orig n | throwError "missing pinned extern {n}"
      modifyEnv fun e => externAttr.ext.addEntry (asyncDecl := n) e (n, attr)
      Lean.compileDecls #[n] (logErrors := true)

    for n in #[`id, `Unit.unit, `Decidable.decide, `dite, `PULift.down, `PProd.fst, `PProd.snd, `cond.match_1, `cond, `OfNat.ofNat, `instOfNatNat, `Add.add, `HAdd.hAdd, `instAddNat, `instHAdd] do
      Lean.compileDecls #[n] (logErrors := true)

  for name in RootNames.binderAnnotations ++ RootNames.natPrimitives do
    modifyEnv fun e => addAlias e (`Omega ++ name) name

end OmegaChecks.InitCompiler
