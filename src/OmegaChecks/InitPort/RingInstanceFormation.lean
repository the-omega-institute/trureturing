module
import all OmegaChecks.InitInventory.Reductions
import OmegaChecks.InitPort.EnvelopeNaturalPremises
meta import OmegaChecks.InitInventory.Reductions
meta import OmegaChecks.InitPort.EnvelopeNaturalPremises

open Lean Meta InitKernelPort OmegaChecks.InitPort OmegaChecks.InitBoundaries
open Lean.Grind

private def owner := `Init.Grind.Ring.Envelope
private def operation := ``Ring.OfSemiring.ofSemiring

/-- The selected class index, equality carrier or powered endpoint contains the whole ring instance. -/
private def endpoint (name : Name) (conclusion : Expr) : MetaM Expr := do
  if name == ``Ring.OfSemiring.instOrderedRingQOfLawfulOrderLTOfExistsAddOfLT then
    unless conclusion.isAppOfArity ``OrderedRing 5 do throwError "wrong ordered ring class"
    let index := conclusion.getAppArgs[1]!
    unless index.isAppOfArity ``Ring.toSemiring 2 && index.appArg!.isAppOfArity operation 2 do
      throwError "expected the semiring projection of the canonical quotient ring"
    return index
  if name == ``Ring.OfSemiring.instNoNatZeroDivisorsQOfAddRightCancel then
    unless conclusion.isAppOfArity ``NoNatZeroDivisors 2 do throwError "wrong scalar cancellation class"
    return conclusion.appArg!
  if name == ``Ring.OfSemiring.instIsCharPQOfAddRightCancel then
    unless conclusion.isAppOfArity ``IsCharP 3 do throwError "wrong characteristic class"
    return conclusion.getAppArgs[1]!
  let some (carrier, left, right) := conclusion.eq? | throwError "expected an embedding equality"
  if name == ``Ring.OfSemiring.toQ_natCast then
    unless carrier.isAppOfArity ``Ring.OfSemiring.Q 2 && carrier.getAppArgs[0]!.isAppOfArity ``Ring.OfSemiring.Q 2 &&
        right.getAppFn.isConstOf ``Ring.OfSemiring.natCast &&
        Kernel.isDefEqGuarded (← getEnv) (← getLCtx) left right do
      throwError "expected the reflexive natural-cast equality in the double envelope"
    return carrier.appArg!
  unless name == ``Ring.OfSemiring.toQ_pow && right.isAppOfArity ``HPow.hPow 6 do throwError "unexpected power"
  return right.getAppArgs[3]!

private def checkInstance (source : ConstantInfo) : MetaM Unit := do
  let env ← getEnv
  let levels := source.levelParams.map Level.param
  forallTelescope source.type fun _ conclusion => do
    if source.name == ``Ring.OfSemiring.toQ_pow then
      let some (_, left, right) := conclusion.eq? | throwError "expected a power equality"
      unless (← whnf left).getAppFn.isConstOf ``Quot.mk && (← whnf right).getAppFn.isConstOf ``Ring.OfSemiring.npow do
        throwError "unexpected public computation of the two power endpoints"
    let index ← endpoint source.name conclusion
    let some use := index.find? (·.isAppOfArity operation 2) | throwError "ring instance absent from index"
    let args := use.getAppArgs
    unless args.all Expr.isFVar do throwError "specialized ring arguments"
    let whole ← mkLambdaFVars args use
    let type ← ofExceptKernelException (Kernel.check env {} whole)
    let expected := (← getConstInfo operation).instantiateTypeLevelParams levels
    unless !whole.hasFVar && Kernel.isDefEqGuarded env {} whole (mkConst operation levels) &&
        Kernel.isDefEqGuarded env {} type expected do throwError "incomplete ring in quotient index"

private def checkNat (strict : Environment) (source : ConstantInfo) : MetaM Unit := do
  let env ← getEnv
  let ty ← EnvelopeNaturalPremises.specialize strict source
  let some use := (← endpoint source.name ty).find? (·.isAppOfArity operation 2)
    | throwError "missing ring in natural specialization"
  unless Kernel.isDefEqGuarded env {} use (mkApp2 (mkConst operation [.zero]) (mkConst ``Nat) EnvelopeNaturalPremises.semiring) do
    throwError "specialized ring does not use the natural semiring"

public def main (args : List String) : IO Unit := do
  let [lib] := args | throw <| IO.userError "expected a strict library"
  let target := owner.replacePrefix `Init `OmegaInit
  unless ← (modToFilePath lib target "olean").pathExists do return
  initSearchPath (← findSysroot)
  let visible ← importModules #[{module := owner}] {} (level := .exported)
  let official ← importModules #[{module := owner, importAll := true}, {module := `Init.GrindInstances.Nat, importAll := true},
    {module := `Init.GrindInstances.Ring.Nat, importAll := true}] {} (level := .private)
  let evidence ← importModules #[{module := `OmegaChecks.InitInventory.Reductions, importAll := true},
    {module := `OmegaChecks.InitInventory.EnvelopeCancellation, importAll := true}] {} (level := .private)
  let some op := official.find? operation | throw <| IO.userError "missing canonical ring"
  let refuter := ``RepresentativeQuotient.refuteEnvelopeCancellation
  RepresentativeQuotient.certify official evidence op refuter
  let some sample := EnvelopeCancellation.observation? owner operation | throw <| IO.userError "missing cancellation test"
  let some (.thmInfo proof) := evidence.find? sample | throw <| IO.userError s!"missing test {sample}"
  let some ring := proof.value.find? (·.isAppOfArity operation 2) | throw <| IO.userError "test does not use the ring"
  unless Kernel.isDefEqGuarded evidence {} ring (mkApp2 (mkConst operation [.zero]) (mkConst ``Nat) EnvelopeNaturalPremises.semiring) do
    throw <| IO.userError "cancellation test and class premises use different natural semirings"
  searchPathRef.set [lib]
  let strict ← importModules #[{module := target}] {} (level := .exported)
  if !strict.contains (portName ``Ring.OfSemiring.Q) || strict.contains (portName operation) then return
  let natRing := `OmegaInit.GrindInstances.Ring.Nat
  unless ← (modToFilePath lib natRing "olean").pathExists do return
  let full ← importModules #[{module := target, importAll := true}, {module := natRing, importAll := true},
    {module := `OmegaInit.GrindInstances.Nat, importAll := true}] {}
  let witnesses := #[``instCommSemiringNat, ``instAddRightCancelNat, ``instNoNatZeroDivisorsNat, ``instIsCharPNatOfNat]
  unless witnesses.all (full.contains ∘ portName) do return
  let cast := ``EnvelopeCancellation.nestedNatCast
  let kernel ← restoreEvidence evidence full.toKernelEnv cast
  let _ ← replayStrict kernel ((witnesses.map portName).push (portName cast))
  for name in [``Ring.OfSemiring.toQ_natCast, ``Ring.OfSemiring.toQ_pow,
      ``Ring.OfSemiring.instNoNatZeroDivisorsQOfAddRightCancel, ``Ring.OfSemiring.instIsCharPQOfAddRightCancel,
      ``Ring.OfSemiring.instOrderedRingQOfLawfulOrderLTOfExistsAddOfLT] do
    if strict.contains (portName name) then continue
    let some src := official.find? name | throw <| IO.userError s!"missing {name}"
    let expected := translate portName src.type
    let missing := expected.getUsedConstants.filter (!strict.contains ·)
    let required := #[operation, ``Ring.OfSemiring.instLEQOfOrderedAdd, ``Ring.OfSemiring.instLTQOfOrderedAdd,
      ``Ring.OfSemiring.instIsPreorderQ].map portName
    let ordered := name == ``Ring.OfSemiring.instOrderedRingQOfLawfulOrderLTOfExistsAddOfLT
    unless src.isTheorem && !src.isUnsafe && !src.isPartial && src.numLevelParams == 1 &&
        (visible.find? name).any (·.type.equal src.type) &&
        visible.getModuleIdxFor? name == visible.getModuleIdx? owner &&
        (Kernel.check visible {} src.type).isOk && typeNeedsConstant visible src.type operation &&
        missing.contains (portName operation) && missing.all (if ordered then required.contains else (· == portName operation)) &&
        !(Kernel.check strict {} expected).isOk do throw <| IO.userError s!"invalid type formation for {name}"
    ((checkInstance src).run').toIO' {fileName := "<ring index>", fileMap := default} {env := visible}
    ((checkNat full src).run').toIO' {fileName := "<natural semiring>", fileMap := default} {env := official}
    IO.println (toJson #[owner.toString, name.toString, operation.toString, refuter.toString]).compress
