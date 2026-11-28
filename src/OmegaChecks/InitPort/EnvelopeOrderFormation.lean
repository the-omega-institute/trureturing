module
import Lean
import OmegaChecks.InitInventory.EnvelopeOrder
import OmegaChecks.InitInventory.LinearEnvelopeOrder
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
private def liftProof (use : Expr) (order coherence : Name) : MetaM Expr := do
  let env ← getEnv
  unless use.getAppFn.isConstOf order do throwError "the class has a different order index"
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
    unless proof.getAppArgs == use.getAppArgs do throwError "coherence uses different order parameters"
    return proof

private def checkLift (use : Expr) (order coherence : Name) : MetaM Unit := do
  let proof ← liftProof use order coherence
  recover use order
  recover proof coherence

/-- The public strict comparison uses the weak comparison on both permutations. -/
private def checkStrictLift (use : Expr) (order coherence : Name) : MetaM Unit := do
  let env ← getEnv
  let less := order.getPrefix.str "instLTQOfOrderedAdd"
  recover use less
  let body ← ofExceptKernelException (Kernel.whnf env (← getLCtx) use)
  unless body.isAppOfArity ``LT.mk 2 do throwError "expected the pinned strict comparison"
  lambdaTelescope body.appArg! fun xs prop => do
    let #[a, b] := xs | throwError "expected two arbitrary quotient arguments"
    unless prop.isAppOfArity ``And 2 && prop.appArg!.isAppOfArity ``Not 1 do throwError "wrong strict comparison"
    let le := mkAppN (mkConst order [.zero]) use.getAppArgs
    for (rel, x, y) in [(prop.getAppArgs[0]!, a, b), (prop.appArg!.appArg!, b, a)] do
      unless rel.isAppOfArity ``LE.le 4 && rel.getAppArgs[1]! == le && rel.getAppArgs[2]! == x && rel.appArg! == y do
        throwError "lost one of the canonical quotient comparisons"
    checkLift le order coherence

/-- Abstract only the coherence demanded for linear preorders. -/
private def linearCoherence (source : ConstantInfo) (order coherence : Name) : MetaM Expr := do
  forallTelescope (source.type.instantiateLevelParams source.levelParams [.zero]) fun xs conclusion => do
    unless xs.size == 5 && conclusion.isAppOfArity ``Std.IsLinearPreorder 2 do throwError "unexpected linear preorder"
    let use := conclusion.appArg!
    let projected := mkApp3 (mkConst ``Std.IsLinearPreorder.toIsPreorder [.zero]) xs[0]! xs[2]! xs[3]!
    unless use.getAppArgs == #[xs[0]!, xs[1]!, xs[2]!, projected, xs[4]!] do
      throwError "quotient order does not project from the assumed linear preorder"
    let proof ← liftProof use order coherence
    mkForallFVars xs (← inferType proof)

/-- The pinned class types retain the comparison at arbitrary quotient inputs. -/
private def certify (source : ConstantInfo) (order coherence : Name) : MetaM Unit := do
  forallTelescope (source.type.instantiateLevelParams source.levelParams [.zero]) fun _ conclusion => do
    let use ← if conclusion.isAppOfArity ``Std.IsPreorder 2 then pure conclusion.appArg!
      else if conclusion.isAppOfArity ``Lean.Grind.OrderedAdd 4 then pure conclusion.getAppArgs[2]!
      else throwError "expected a preorder or ordered-addition instance"
    checkLift use order coherence

/-- Read the pinned proposition at its two arbitrary quotient arguments. The hypotheses
identify representatives, but neither equality substitutes into the published type. -/
private def checkImplication (source : ConstantInfo) (order coherence : Name) (negated less : Bool) : MetaM Unit := do
  let ty := source.type.instantiateLevelParams source.levelParams [.zero]
  let classes := if less then 7 else 5
  forallBoundedTelescope ty (some (classes + 6)) fun xs rest => do
    let #[a, b, qa, qb, ha, hb] := xs.extract classes xs.size | throwError "unexpected embedding binders"
    let α := xs[0]!
    let moduleInst := xs[1]!
    let base := xs[if less then 3 else 2]!
    if less then
      -- Supply both extra assumptions for every possible base weak comparison.
      let lt := mkApp2 (mkConst ``strictRelation [.zero]) α xs[2]!
      let law := mkApp2 (mkConst ``strictRelationLawful [.zero]) α xs[2]!
      let lawType ← ofExceptKernelException (Kernel.check (← getEnv) (← getLCtx) law)
      let domain := (← inferType xs[4]!).replaceFVar base lt
      unless Kernel.isDefEqGuarded (← getEnv) (← getLCtx) lawType domain do throwError "unsatisfied lawful order premise"
    let .forallE _ premise conclusion _ := rest | throwError "expected implication"
    let relation (prop : Expr) : MetaM Expr := do
      if !negated then return prop
      unless prop.isAppOfArity ``Not 1 do throwError "expected negated comparison"
      return prop.appArg!
    let p ← relation premise
    let q ← relation conclusion
    let projection := if less then ``LT.lt else ``LE.le
    let compares (rel inst left right : Expr) :=
      rel.isAppOfArity projection 4 && rel.getAppArgs[1]! == inst && rel.getAppArgs[2]! == left && rel.appArg! == right
    unless compares p base a b && q.isAppOfArity projection 4 do throwError "unexpected comparison premise or goal"
    let use := q.getAppArgs[1]!
    let params := (xs.extract 0 3) ++ xs.extract (classes - 2) classes
    unless compares q use qa qb && use.getAppArgs == params do throwError "specialized quotient comparison"
    for (value, quotient, equality) in [(a, qa, ha), (b, qb, hb)] do
      let some (_, lhs, rhs) := (← inferType equality).eq? | throwError "expected embedding equality"
      unless lhs.isAppOfArity ``Lean.Grind.IntModule.OfNatModule.toQ 3 &&
          lhs.getAppArgs == #[α, moduleInst, value] && rhs == quotient do throwError "wrong embedding equality"
    if less then checkStrictLift use order coherence else checkLift use order coherence

private def checkImplications (lib : System.FilePath) (systemPath : SearchPath) (evidence : Environment)
    (order coherence forward reverse : Name) : IO Unit := do
  let owner := `Init.Grind.Module.OfNatModule
  let target := owner.replacePrefix `Init `OmegaInit
  unless ← (modToFilePath lib target "olean").pathExists do return
  searchPathRef.set systemPath
  let visible ← importModules #[{module := owner}] {} (level := .exported)
  let pinned ← importModules #[{module := owner, importAll := true}] {}
  searchPathRef.set [lib]
  let strict ← importModules #[{module := target}] {} (level := .exported)
  let full ← importModules #[{module := target, importAll := true}] {}
  for (suffix, negated, less) in [("of_le", false, false), ("of_not_le", true, false),
      ("of_lt", false, true), ("of_not_lt", true, true)] do
    let name := order.getPrefix.str suffix
    let comparison := if less then order.getPrefix.str "instLTQOfOrderedAdd" else order
    if strict.contains (portName name) then continue
    let some src := pinned.find? name | throw <| IO.userError s!"missing theorem {name}"
    let translated := translate portName src.type
    unless src.isTheorem && !src.isUnsafe && !src.isPartial && src.numLevelParams == 1 &&
        (visible.find? name).any (·.type.equal src.type) && visible.getModuleIdxFor? name == visible.getModuleIdx? owner &&
        (Kernel.check visible {} src.type).isOk && typeNeedsConstant visible src.type comparison &&
        translated.getUsedConstants.filter (!strict.contains ·) == #[portName comparison] &&
        !full.contains (portName comparison) && !(Kernel.check strict {} translated).isOk do
      throw <| IO.userError s!"invalid quotient comparison in {name}"
    if less then
      let kernel ← restoreEvidence evidence full.toKernelEnv ``strictRelationLawful
      let _ ← replayStrict kernel #[portName ``strictRelationLawful]
    ((checkImplication src order coherence negated less).run').toIO'
      {fileName := "<quotient order implication>", fileMap := default} {env := if less then evidence else visible}
    IO.println (toJson #[owner.toString, name.toString, order.toString, coherence.toString,
      forward.toString, reverse.toString]).compress

private def checkOrder (source : ConstantInfo) (order coherence : Name) : MetaM Unit := do
  let n := source.name
  let env ← getEnv
  let ty := source.type.instantiateLevelParams source.levelParams [.zero]
  forallTelescope ty fun xs body => do
    let use := mkAppN (mkConst n [.zero]) xs
    let strict := n != order
    if strict then checkStrictLift use order coherence else checkLift use order coherence
    unless body.isAppOfArity (if strict then ``LT else ``LE) 1 do throwError "wrong quotient carrier"
    let carrier := body.appArg!
    withLocalDeclD `a carrier fun a => withLocalDeclD `b carrier fun b => do
      let relation ← mkLambdaFVars #[a, b] (mkConst ``False)
      let dummy ← mkLambdaFVars xs (← mkAppM (if strict then ``LT.mk else ``LE.mk) #[relation])
      let actual ← ofExceptKernelException (Kernel.check env {} dummy)
      unless Kernel.isDefEqGuarded env {} actual ty && !Kernel.isDefEqGuarded env {} dummy (mkConst n [.zero]) do
        throwError "the bare order type must also admit a different comparison"

public def main (args : List String) : IO Unit := do
  let [lib] := args | throw <| IO.userError "expected a strict library"
  initSearchPath (← findSysroot)
  let evidence ← importModules #[{module := `OmegaChecks.InitInventory.LinearEnvelopeOrder, importAll := true}] {}
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
    ((checkOrder src order coherence).run').toIO' {fileName := "<quotient comparison>", fileMap := default} {env := visible}
    IO.println (toJson #[owner.toString, order.toString, order.toString, coherence.toString,
      forward.toString, reverse.toString, build.toString]).compress
    let less := envelope.str "instLTQOfOrderedAdd"
    if !strict.contains (portName less) then
      let builder := if owner == `Init.Grind.Module.Envelope then ``moduleStrictOrderFromPropext else ``ringStrictOrderFromPropext
      let some decl := visible.find? less | throw <| IO.userError s!"missing {less}"
      let rebuilt := mkApp (mkConst builder levels) (mkConst ``propext)
      let .ok actual := Kernel.check evidence {} rebuilt | throw <| IO.userError s!"cannot construct {less}"
      unless (decl matches .defnInfo _) && !decl.isUnsafe && !decl.isPartial && !complete.contains (portName less) &&
          visible.getModuleIdxFor? less == visible.getModuleIdx? owner &&
          (Kernel.check strict {} (translate portName decl.type)).isOk &&
          Kernel.isDefEqGuarded evidence {} actual decl.type &&
          Kernel.isDefEqGuarded evidence {} rebuilt (mkConst less levels) do
        throw <| IO.userError s!"incorrect reconstruction of {less}"
      ((checkOrder decl order coherence).run').toIO' {fileName := "<strict quotient comparison>", fileMap := default} {env := visible}
      let kernel ← restoreEvidence evidence kernel builder
      let _ ← replayStrict kernel #[portName builder]
      IO.println (toJson #[owner.toString, less.toString, order.toString, coherence.toString,
        forward.toString, reverse.toString, builder.toString]).compress
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
    if owner != `Init.Grind.Module.Envelope then continue
    checkImplications lib systemPath evidence order coherence forward reverse
    let name := envelope.str "instIsLinearPreorderQ"
    let natRing := `OmegaInit.GrindInstances.Ring.Nat
    if strict.contains (portName name) || !(← (modToFilePath lib natRing "olean").pathExists) then continue
    let some src := pinned.find? name | throw <| IO.userError s!"missing {name}"
    let translated := translate portName src.type
    unless src.isTheorem && !src.isUnsafe && !src.isPartial && src.numLevelParams == 1 &&
        (visible.find? name).any (·.type.equal src.type) && visible.getModuleIdxFor? name == visible.getModuleIdx? owner &&
        (Kernel.check visible {} src.type).isOk && typeNeedsConstant visible src.type order &&
        translated.getUsedConstants.filter (!strict.contains ·) == #[portName order] &&
        !(Kernel.check strict {} translated).isOk do throw <| IO.userError s!"invalid order index in {name}"
    let needed ← ((linearCoherence src order coherence).run').toIO'
      {fileName := "<linear preorder coherence>", fileMap := default} {env := visible}
    let fwd := ``OmegaChecks.InitBoundaries.LinearEnvelopeOrder.propextFromLinearLift
    let rev := ``OmegaChecks.InitBoundaries.LinearEnvelopeOrder.linearLiftFromPropext
    for (witness, ty) in [(mkConst fwd, .forallE .anonymous needed ext.type .default),
        (mkConst rev [.zero], .forallE .anonymous ext.type needed .default)] do
      let .ok actual := Kernel.check evidence {} witness | throw <| IO.userError "invalid restricted-order witness"
      unless Kernel.isDefEqGuarded evidence {} actual ty do throw <| IO.userError "wrong restricted-order witness"
    searchPathRef.set [lib]
    let full ← importModules #[{module := targetOwner, importAll := true}, {module := natRing, importAll := true},
      {module := `OmegaInit.Data.Nat.Lemmas, importAll := true}] {}
    let kernel ← restoreEvidence evidence full.toKernelEnv fwd
    let kernel ← restoreEvidence evidence kernel rev
    let _ ← replayStrict kernel #[portName fwd, portName rev]
    IO.println (toJson #[owner.toString, name.toString, order.toString, coherence.toString, fwd.toString, rev.toString]).compress
