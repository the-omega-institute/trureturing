module
public import Lean
import OmegaChecks.InitInventory.Replay
import all Init.Grind.Ring.Envelope
import all Init.Grind.Module.Envelope
import Init.GrindInstances.Ring.Nat

namespace OmegaChecks.InitBoundaries.EnvelopeCancellation
open Lean Lean.Grind Std

private abbrev ringPoint := Ring.OfSemiring.Q.mk (α := Nat) (1, 0)
private abbrev modulePoint := IntModule.OfNatModule.Q.mk (α := Nat) (1, 0)

private theorem ringLaw :
    Ring.OfSemiring.add (Ring.OfSemiring.neg ringPoint) ringPoint = Ring.OfSemiring.natCast 0 := Ring.OfSemiring.neg_add_cancel ringPoint
private theorem moduleLaw :
    IntModule.OfNatModule.add (IntModule.OfNatModule.neg modulePoint) modulePoint = IntModule.OfNatModule.zero := IntModule.OfNatModule.neg_add_cancel modulePoint

private theorem ringProjection : type_of% ringLaw :=
  @Ring.neg_add_cancel _ (Ring.OfSemiring.ofSemiring (α := Nat)) ringPoint

private theorem commRingProjection : type_of% ringLaw :=
  @Ring.neg_add_cancel _ (CommRing.OfCommSemiring.ofCommSemiring (α := Nat)).toRing ringPoint

private theorem moduleProjection : type_of% moduleLaw :=
  @AddCommGroup.neg_add_cancel _ (IntModule.OfNatModule.ofNatModule (α := Nat)).toAddCommGroup modulePoint

private abbrev diagonal := IntModule.OfNatModule.Q.mk (α := Nat) (1, 1)
private abbrev zeroPoint := IntModule.OfNatModule.Q.mk (α := Nat) (0, 0)

/-- Both envelope comparisons on these inputs reduce to the reflexive comparison 1 ≤ 1. -/
private theorem partialAntisymmetry : diagonal = zeroPoint :=
  @IsPartialOrder.le_antisymm _ _ (@IntModule.OfNatModule.instIsPartialOrderQ Nat _ _ _ _)
    diagonal zeroPoint (Nat.le_refl 1) (Nat.le_refl 1)

private theorem linearAntisymmetry : diagonal = zeroPoint :=
  @IsPartialOrder.le_antisymm _ _ (@IntModule.OfNatModule.instIsLinearOrderQ Nat _ _ _ _).toIsPartialOrder
    diagonal zeroPoint (Nat.le_refl 1) (Nat.le_refl 1)

private theorem scalarCancellation :
    IntModule.OfNatModule.add (IntModule.OfNatModule.zsmul 1 modulePoint)
      (IntModule.OfNatModule.zsmul (-1) modulePoint) = IntModule.OfNatModule.zsmul (1 + -1) modulePoint :=
  (IntModule.OfNatModule.add_zsmul 1 (-1) modulePoint).symm

private def observations := [
  (`Init.Grind.Ring.Envelope, ``Ring.OfSemiring.neg_add_cancel, ``ringLaw),
  (`Init.Grind.Module.Envelope, ``IntModule.OfNatModule.neg_add_cancel, ``moduleLaw),
  (`Init.Grind.Ring.Envelope, ``Ring.OfSemiring.ofSemiring, ``ringProjection),
  (`Init.Grind.Ring.Envelope, ``CommRing.OfCommSemiring.ofCommSemiring, ``commRingProjection),
  (`Init.Grind.Module.Envelope, ``IntModule.OfNatModule.ofNatModule, ``moduleProjection),
  (`Init.Grind.Module.Envelope, ``IntModule.OfNatModule.add_zsmul, ``scalarCancellation),
  (`Init.Grind.Module.Envelope, ``IntModule.OfNatModule.instIsPartialOrderQ, ``partialAntisymmetry),
  (`Init.Grind.Module.Envelope, ``IntModule.OfNatModule.instIsLinearOrderQ, ``linearAntisymmetry)]

public def observation? (owner name : Name) : Option Name := do
  let (_, _, observation) ← observations.find? fun (m, n, _) => m == owner && n == name
  return observation

private def pair (a b : Nat) :=
  mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Nat) (mkConst ``Nat) (mkRawNatLit a) (mkRawNatLit b)

private abbrev natRing : Semiring Nat := inferInstance

private theorem relatedAt (n : Nat) : ∃ k : Nat, n + k = n + k := ⟨0, rfl⟩

public def isLiftEquation (owner name : Name) : Bool :=
  owner == `Init.Grind.Ring.Envelope && [``Ring.OfSemiring.add, ``Ring.OfSemiring.sub,
    ``Ring.OfSemiring.mul, ``Ring.OfSemiring.neg].any (fun op => name == op.str "eq_1")

/-- Read the coherence argument required by the right side of the public unfolding equation,
while its quotient arguments are still variables. On two related natural-number pairs it
must identify the classes of (1,1) and (0,0). The inputs to the argument replay without axioms. -/
private def liftEquationClaim (official witnesses : Environment) (source : ConstantInfo) : IO Expr := do
  let some inst := (witnesses.find? ``natRing).bind ConstantInfo.value? | throw <| IO.userError "missing Nat semiring"
  let op := source.name.getPrefix
  let unary := op == ``Ring.OfSemiring.neg
  -- Multiplication fixes (1,0), its unit representative. Addition and subtraction fix (0,0).
  let fixed := if op == ``Ring.OfSemiring.mul then 1 else 0
  let evidence (n : Nat) := mkApp (mkConst ``relatedAt) (mkRawNatLit n)
  let args := if unary then #[pair 1 1, pair 0 0, evidence 1]
    else #[pair 1 1, pair fixed 0, pair 0 0, pair fixed 0, evidence 1, evidence fixed]
  let clean ← replayBoundaryDependencies official witnesses (args.toList.flatMap (·.getUsedConstantsAsSet.toList))
  for arg in args do
    if let .error _ := Kernel.check clean {} arg then throw <| IO.userError "invalid coherence test input"
  let test := do
    let type := (source.type.instantiateLevelParams source.levelParams [0]).bindingBody!.instantiate1 (mkConst ``Nat)
    Meta.forallTelescope (type.bindingBody!.instantiate1 inst) fun qs conclusion => do
      let some (_, lhs, rhs) := conclusion.eq? | throwError "expected an unfolding equality"
      unless qs.size == (if unary then 1 else 2) && lhs == mkAppN (mkApp2 (mkConst op [0]) (mkConst ``Nat) inst) qs &&
          rhs.getAppFn.isConstOf (if unary then ``Quot.liftOn else ``Ring.OfSemiring.Q.liftOn₂) do
        throwError "unexpected unfolding equation for {source.name}"
      let .forallE _ required _ _ ← Meta.whnf (← Meta.inferType rhs.appFn!) | throwError "missing coherence argument"
      let ctx ← getLCtx
      unless Kernel.isDefEqGuarded witnesses ctx (← Meta.inferType rhs.appArg!) required && !required.hasFVar do
        throwError "unexpected coherence type for {source.name}"
      Meta.withLocalDeclD `respect required fun respect => do
        let claim ← ofExceptKernelException (Kernel.check witnesses (← getLCtx) (mkAppN respect args))
        unless !claim.hasFVar do throwError "coherence result depends on the supplied proof"
        return claim
  (Meta.MetaM.run' test).toIO' {fileName := "<envelope lift coherence>", fileMap := default} {env := witnesses}

/-- Obtain an equality by applying the physical declaration or its cancellation field.
Reduce both sides to the pinned quotient constructor and check its relation and payload.
The returned equality is the observation in the representative model. -/
public def counterexample (official witnesses : Environment) (source : ConstantInfo) (modelPoint : Name) : IO Expr := do
  let some idx := official.getModuleIdxFor? source.name | throw <| IO.userError s!"missing owner for {source.name}"
  let owner := official.header.moduleNames[idx]!
  let claim ← if isLiftEquation owner source.name then liftEquationClaim official witnesses source else do
    let some probe := observation? owner source.name
      | throw <| IO.userError s!"unexpected envelope declaration {source.name}"
    let some (.thmInfo template) := witnesses.find? probe | throw <| IO.userError s!"missing {probe}"
    let call := template.value.replace fun e =>
      if [``ringPoint, ``modulePoint, ``diagonal, ``zeroPoint].any e.isConstOf then
        (witnesses.find? e.constName!).bind ConstantInfo.value?
      else none
    unless call.getUsedConstantsAsSet.contains source.name && (official.find? source.name).any (·.type.equal source.type) do
      throw <| IO.userError s!"probe does not use the declared envelope {source.name}"
    IO.ofExcept <| (Kernel.check official {} call).mapError fun _ => s!"failed to specialize {source.name}"
  let .ok claim := Kernel.whnf official {} claim | throw <| IO.userError s!"invalid cancellation type for {source.name}"
  let some (_, lhs, rhs) := claim.eq? | throw <| IO.userError s!"expected cancellation equality for {source.name}"
  let reduce (side : Expr) (value : Nat) := do
    let .ok root := Kernel.whnf official {} side | throw <| IO.userError s!"failed to reduce {source.name}"
    unless root.isAppOfArity ``Quot.mk 3 && Kernel.isDefEqGuarded official {} root.appArg! (pair value value) do
      throw <| IO.userError s!"unexpected cancellation endpoint for {source.name}"
    return root.appFn!
  let leftPoint ← reduce lhs 1
  let rightPoint ← reduce rhs 0
  unless Kernel.isDefEqGuarded official {} leftPoint rightPoint do
    throw <| IO.userError s!"cancellation endpoints of {source.name} use different quotient relations"
  let carrier := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``Nat)
  let relation := Expr.forallE `x carrier (.forallE `y carrier (.sort .zero) .default) .default
  let point := mkApp2 (mkConst modelPoint [1]) carrier (.bvar 0)
  let equality := mkApp3 (mkConst ``Eq [1]) carrier (mkApp point (pair 1 1)) (mkApp point (pair 0 0))
  return .forallE `r relation (.forallE `h equality (mkConst ``False) .default) .default

end OmegaChecks.InitBoundaries.EnvelopeCancellation
