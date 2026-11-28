module
import all OmegaChecks.InitPort.SemiringImage
import OmegaChecks.InitPort.StrictReplay
meta import OmegaChecks.InitPort.StrictReplay

open Lean Meta InitKernelPort OmegaChecks.InitPort

private def origin := `Init.Grind.Ring.CommSemiringAdapter
private def interpreter := ``Grind.CommRing.Expr.denoteSAsRing
private def instanceName := ``Grind.Ring.OfSemiring.ofSemiring

/-- The three constructor equations reduce on the official left side, exposing exactly
the operation on the right. The combined equation retains its matcher at an unknown expression. -/
private def commonType (src casesRule : ConstantInfo) : MetaM Expr := do
  let levels := src.levelParams.map Level.param
  if src.name.getString! == "eq_def" then
    let ty := casesRule.type.instantiateLevelParams casesRule.levelParams levels
    return ← deltaExpand ty (· == ``SemiringImage.constructorCases)
  forallTelescope src.type fun xs body => do
    let some (_, lhs, _) := body.eq? | throwError "expected an arithmetic equation"
    mkForallFVars xs (← mkEq lhs lhs)

/-- On a variable expression the public interpreter must keep its case split. -/
private def checkVariable (equation : Name) : MetaM Unit := do
  let cfg ← getConstInfo equation
  forallTelescope cfg.type fun _ body => do
    let some (_, lhs, rhs) := body.eq? | throwError "expected a variable interpreter equation"
    if Kernel.isDefEqGuarded (← getEnv) (← getLCtx) lhs rhs then
      throwError "variable expression reduced through the image: {equation}"

public def main (args : List String) : IO Unit := do
  let [lib] := args | throw <| IO.userError "expected a strict library"
  let targetOwner := origin.replacePrefix `Init `OmegaInit
  unless ← (modToFilePath lib targetOwner "olean").pathExists do return
  initSearchPath (← findSysroot)
  let visible ← importModules #[{module := origin}] {} (level := .exported)
  let evidence ← importModules #[{module := `OmegaChecks.InitPort.SemiringImage, importAll := true}] {}
  let some combined := evidence.find? ``SemiringImage.constructorCasesEq | throw <| IO.userError "missing cases equation"
  searchPathRef.set [lib]
  let strict ← importModules #[{module := targetOwner}] {} (level := .exported)
  let full ← importModules #[{module := targetOwner, importAll := true}] {}
  -- A previous strict product sealed the interpreter and cannot supply its public reductions.
  unless (strict.find? (portName interpreter)).any (· matches .defnInfo _) do return
  let ctx := {fileName := "<semiring equation>", fileMap := default : Core.Context}
  for (env, n) in [(visible, ``Grind.CommRing.Expr.denoteAsRing_eq),
      (strict, portName ``Grind.CommRing.Expr.denoteAsRing_eq)] do
    ((checkVariable n).run').toIO' ctx {env}
  let mut roots := #[]
  let mut certificates := #[]
  for (suffix, image) in [("eq_4", ``SemiringImage.addImage), ("eq_5", ``SemiringImage.mulImage),
      ("eq_6", ``SemiringImage.powImage), ("eq_def", ``SemiringImage.casesEq)] do
    let name := interpreter.str suffix
    let some dst := strict.find? (portName name) | continue
    let some privateDst := full.find? dst.name | throw <| IO.userError s!"missing strict {name}"
    let some src := visible.find? name | throw <| IO.userError s!"missing {name}"
    let some rule := evidence.find? image | throw <| IO.userError s!"missing computation {image}"
    let levels := src.levelParams.map Level.param
    let normalized ← ((commonType src combined).run').toIO' ctx {env := evidence}
    let imageType := rule.type.instantiateLevelParams rule.levelParams levels
    let target := dst.type.instantiateLevelParams dst.levelParams levels
    let raw := translate portName src.type
    unless src.numLevelParams == 1 && dst.numLevelParams == 1 && privateDst.isTheorem &&
        !privateDst.isUnsafe && !privateDst.isPartial && (privateDst.type.equal dst.type) &&
        strict.getModuleIdxFor? dst.name == strict.getModuleIdx? targetOwner &&
        visible.getModuleIdxFor? name == visible.getModuleIdx? origin &&
        (Kernel.check visible {} src.type).isOk && typeNeedsConstant visible src.type instanceName &&
        raw.getUsedConstants.filter (!strict.contains ·) == #[portName instanceName] &&
        !(Kernel.check strict {} raw).isOk do throw <| IO.userError s!"invalid raw equation {name}"
    unless (Kernel.check visible {} normalized).isOk && Kernel.isDefEqGuarded visible {} normalized src.type do
      throw <| IO.userError s!"official equation does not accept the public constructor form {name}"
    let translated := translate portName normalized
    unless (Kernel.check strict {} translated).isOk && Kernel.isDefEqGuarded strict {} translated target do
      throw <| IO.userError s!"strict equation does not accept the public constructor form {name}"
    -- Successful conversion also has to preserve the arithmetic result on the base semiring.
    unless rule.isTheorem && (Kernel.check visible {} imageType).isOk &&
        (Kernel.check strict {} (translate portName imageType)).isOk &&
        Kernel.isDefEqGuarded strict {} (translate portName imageType) target do
      throw <| IO.userError s!"strict equation does not give the public arithmetic result {image}"
    roots := roots.push dst.name
    certificates := certificates.push #[origin.toString, name.toString, image.toString]
  let _ ← replayStrict full.toKernelEnv roots
  for c in certificates do IO.println (toJson c).compress
