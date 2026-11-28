module
import Lean
import OmegaChecks.InitInventory.EnvelopeOrder
import OmegaChecks.InitPort.StrictReplay
meta import OmegaChecks.InitInventory.EnvelopeOrder
meta import OmegaChecks.InitPort.StrictReplay

open Lean Meta InitKernelPort OmegaChecks.InitPort OmegaChecks.InitBoundaries.EnvelopeOrder

/-- Recover the entire polymorphic operation from its occurrence, including each typeclass argument. -/
private def recover (use : Expr) (name : Name) : MetaM Unit := do
  let args := use.getAppArgs
  unless args.all Expr.isFVar do throwError "specialized arguments to {name}"
  let whole ← mkLambdaFVars args use
  let env ← getEnv
  let actual ← ofExceptKernelException (Kernel.check env {} whole)
  let pin := mkConst name [.zero]
  unless !whole.hasFVar && Kernel.isDefEqGuarded env {} whole pin &&
      Kernel.isDefEqGuarded env {} actual (← inferType pin) do throwError "incomplete occurrence of {name}"

/-- Read the comparison on two fresh quotient variables before either has been replaced by a representative. -/
private def checkLift (use : Expr) (order coherence : Name) : MetaM Unit := do
  let env ← getEnv
  unless use.getAppFn.isConstOf order do throwError "the class has a different order index"
  recover use order
  let instanceBody ← ofExceptKernelException (Kernel.whnf env (← getLCtx) use)
  unless instanceBody.isAppOfArity ``LE.mk 2 do throwError "unexpected order representation"
  lambdaTelescope instanceBody.appArg! fun xs body => do
    unless xs.size == 2 do throwError "expected two quotient inputs"
    let reduced ← ofExceptKernelException (Kernel.whnf env (← getLCtx) body)
    let args := reduced.getAppArgs
    let primitive := reduced.getAppFn.isConstOf ``Quot.lift && reduced.appArg! == xs[0]!
    let binary := reduced.isAppOfArity (order.getPrefix ++ `Q.liftOn₂) 7 &&
      args[3]! == xs[0]! && args[4]! == xs[1]!
    unless primitive || binary do throwError "comparison must retain arbitrary quotient inputs"
    let some proof := reduced.find? (·.getAppFn.isConstOf coherence) | throwError "missing {coherence}"
    recover proof coherence

/-- The pinned class types retain the comparison at arbitrary quotient inputs. -/
private def certify (source : ConstantInfo) (order coherence : Name) : MetaM Unit := do
  forallTelescope (source.type.instantiateLevelParams source.levelParams [.zero]) fun _ conclusion => do
    let use ← if conclusion.isAppOfArity ``Std.IsPreorder 2 then pure conclusion.appArg!
      else if conclusion.isAppOfArity ``Lean.Grind.OrderedAdd 4 then pure conclusion.getAppArgs[2]!
      else throwError "expected a preorder or ordered-addition instance"
    checkLift use order coherence

private def checkOrder (source : ConstantInfo) (coherence : Name) : MetaM Unit := do
  let n := source.name
  let env ← getEnv
  let ty := source.type.instantiateLevelParams source.levelParams [.zero]
  forallTelescope ty fun xs body => do
    checkLift (mkAppN (mkConst n [.zero]) xs) n coherence
    unless body.isAppOfArity ``LE 1 do throwError "expected LE on the quotient"
    let carrier := body.appArg!
    withLocalDeclD `a carrier fun a => withLocalDeclD `b carrier fun b => do
      let relation ← mkLambdaFVars #[a, b] (mkConst ``False)
      let dummy ← mkLambdaFVars xs (← mkAppM ``LE.mk #[relation])
      let actual ← ofExceptKernelException (Kernel.check env {} dummy)
      unless Kernel.isDefEqGuarded env {} actual ty && !Kernel.isDefEqGuarded env {} dummy (mkConst n [.zero]) do
        throwError "the bare order type must also admit a different comparison"

public def main (args : List String) : IO Unit := do
  let [lib] := args | throw <| IO.userError "expected a strict library"
  initSearchPath (← findSysroot)
  let evidence ← importModules #[{module := `OmegaChecks.InitInventory.EnvelopeOrder, importAll := true}] {}
  let systemPath ← searchPathRef.get
  for (owner, envelope, suffix, forward, reverse, build) in [
      (`Init.Grind.Module.Envelope, `Lean.Grind.IntModule.OfNatModule, "_proof_3",
        ``propextFromModuleLift, ``moduleLiftFromPropext, ``moduleOrderFromPropext),
      (`Init.Grind.Ring.Envelope, `Lean.Grind.Ring.OfSemiring, "_proof_1",
        ``propextFromRingLift, ``ringLiftFromPropext, ``ringOrderFromPropext)] do
    let targetOwner := owner.replacePrefix `Init `OmegaInit
    unless ← (modToFilePath lib targetOwner "olean").pathExists do continue
    searchPathRef.set systemPath
    let visible ← importModules #[{module := owner}] {} (level := .exported)
    let pinned ← importModules #[{module := owner, importAll := true}] {}
    let order := envelope.str "instLEQOfOrderedAdd"
    let coherence := order.str suffix
    let some arg := visible.find? coherence | throw <| IO.userError s!"missing {coherence}"
    let some ext := evidence.find? ``propext | throw <| IO.userError "missing extensionality type"
    let needed := arg.type.instantiateLevelParams arg.levelParams [.zero]
    for (witness, type) in [(mkConst forward, .forallE .anonymous needed ext.type .default),
        (mkConst reverse [.zero], .forallE .anonymous ext.type needed .default)] do
      let .ok actual := Kernel.check evidence {} witness | throw <| IO.userError "invalid order witness"
      unless Kernel.isDefEqGuarded evidence {} actual type do throw <| IO.userError "wrong implication"
    searchPathRef.set [lib]
    let strict ← importModules #[{module := targetOwner}] {} (level := .exported)
    if strict.contains (portName order) then continue
    let complete ← importModules #[{module := targetOwner, importAll := true},
      {module := `OmegaInit.Data.Bool, importAll := true}] {}
    let kernel ← restoreEvidence evidence complete.toKernelEnv forward
    let kernel ← restoreEvidence evidence kernel reverse
    let kernel ← restoreEvidence evidence kernel build
    let _ ← replayStrict kernel #[portName forward, portName reverse, portName build]
    let some src := visible.find? order | throw <| IO.userError s!"missing {order}"
    let levels := src.levelParams.map Level.param
    let rebuilt := mkApp (mkConst build levels) (mkConst ``propext)
    let .ok rebuiltType := Kernel.check evidence {} rebuilt | throw <| IO.userError s!"invalid constructor {build}"
    unless visible.getModuleIdxFor? order == visible.getModuleIdx? owner &&
        pinned.getModuleIdxFor? order == pinned.getModuleIdx? owner &&
        (src matches .defnInfo _) && !src.isUnsafe && !src.isPartial &&
        !complete.contains (portName order) && (Kernel.check strict {} (translate portName src.type)).isOk &&
        Kernel.isDefEqGuarded evidence {} rebuiltType src.type &&
        Kernel.isDefEqGuarded evidence {} rebuilt (mkConst order levels) do
      throw <| IO.userError s!"cannot reconstruct the complete pinned operation {order}"
    ((checkOrder src coherence).run').toIO' {fileName := "<quotient comparison>", fileMap := default} {env := visible}
    IO.println (toJson #[owner.toString, order.toString, order.toString, coherence.toString,
      forward.toString, reverse.toString, build.toString]).compress
    for suffix in ["instIsPreorderQ", "instOrderedAddQ"] do
      let name := envelope.str suffix
      if strict.contains (portName name) then continue
      let some src := pinned.find? name | throw <| IO.userError s!"missing {name}"
      unless (visible.find? name).any (fun c => c.type.equal src.type) &&
          visible.getModuleIdxFor? name == visible.getModuleIdx? owner &&
          (src.isTheorem || src matches .defnInfo _) && !src.isUnsafe && !src.isPartial &&
          (Kernel.check visible {} src.type).isOk && typeNeedsConstant visible src.type order &&
          !(Kernel.check strict {} (translate portName src.type)).isOk do
        throw <| IO.userError s!"invalid instance dependency in {name}"
      ((certify src order coherence).run').toIO' {fileName := "<quotient order formation>", fileMap := default}
        {env := visible}
      IO.println (toJson #[owner.toString, name.toString, order.toString, coherence.toString,
        forward.toString, reverse.toString]).compress
