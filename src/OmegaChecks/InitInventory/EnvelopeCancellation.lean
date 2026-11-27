module
public import Lean
import all Init.Grind.Ring.Envelope
import all Init.Grind.Module.Envelope
import Init.GrindInstances.Ring.Nat

namespace OmegaChecks.InitBoundaries.EnvelopeCancellation
open Lean Lean.Grind

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

private def observations := [
  (`Init.Grind.Ring.Envelope, ``Ring.OfSemiring.neg_add_cancel, ``ringLaw),
  (`Init.Grind.Module.Envelope, ``IntModule.OfNatModule.neg_add_cancel, ``moduleLaw),
  (`Init.Grind.Ring.Envelope, ``Ring.OfSemiring.ofSemiring, ``ringProjection),
  (`Init.Grind.Ring.Envelope, ``CommRing.OfCommSemiring.ofCommSemiring, ``commRingProjection),
  (`Init.Grind.Module.Envelope, ``IntModule.OfNatModule.ofNatModule, ``moduleProjection)]

public def observation? (owner name : Name) : Option Name := do
  let (_, _, observation) ← observations.find? fun (m, n, _) => m == owner && n == name
  return observation

private def pair (a b : Nat) :=
  mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Nat) (mkConst ``Nat) (mkRawNatLit a) (mkRawNatLit b)

/-- Obtain an equality by applying the physical declaration or its cancellation field.
Reduce both sides to the pinned quotient constructor and check its relation and payload.
The returned equality is the observation in the representative model. -/
public def counterexample (official witnesses : Environment) (source : ConstantInfo) (modelPoint : Name) : IO Expr := do
  let some idx := official.getModuleIdxFor? source.name | throw <| IO.userError s!"missing owner for {source.name}"
  let some probe := observation? official.header.moduleNames[idx]! source.name
    | throw <| IO.userError s!"unexpected envelope declaration {source.name}"
  let some (.thmInfo template) := witnesses.find? probe | throw <| IO.userError s!"missing {probe}"
  let call := template.value.replace fun e =>
    if e.isConstOf ``ringPoint || e.isConstOf ``modulePoint then (witnesses.find? e.constName!).bind ConstantInfo.value?
    else none
  unless call.getUsedConstantsAsSet.contains source.name && (official.find? source.name).any (·.type.equal source.type) do
    throw <| IO.userError s!"probe does not use the declared envelope {source.name}"
  let .ok claim := Kernel.check official {} call | throw <| IO.userError s!"failed to specialize {source.name}"
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
