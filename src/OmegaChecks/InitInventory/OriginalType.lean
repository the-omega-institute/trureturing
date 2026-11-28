module
public import Lean
import OmegaChecks.InitPort.Translation
import OmegaChecks.InitInventory.EnvelopePublicTypes

open Lean
namespace OmegaChecks.InitInventory

/-- The proof in `fun i h => Fin.mk i proof`, and the single occurrence where it is used. -/
private structure FinBoundSite where
  proof : Expr
  closedProof : Expr
  replaceProof : Expr → Expr

private def finBoundSite? (rename : Name → Name) (type : Expr) : Option FinBoundSite := do
  if let .forallE n d b bi := type then
    let site ← finBoundSite? rename b
    return {site with
      closedProof := .lam n d site.closedProof bi
      replaceProof := fun proof => .forallE n d (site.replaceProof proof) bi}
  let .app lhs rhs := type | none
  guard (type.isAppOfArity (rename ``Eq) 3 && rhs.isAppOfArity (rename ``Option.pmap) 6)
  let args := rhs.getAppArgs
  let .lam i idom (.lam h hdom (.app mkFin proof) hbi) ibi := args[3]! | none
  guard (mkFin.isAppOfArity (rename ``Fin.mk) 2 && mkFin.appArg! == .bvar 1)
  let bind := fun body => Expr.lam i idom (.lam h hdom body hbi) ibi
  let replaceProof := fun p => mkApp lhs (mkAppN rhs.getAppFn (args.set! 3 (bind (.app mkFin p))))
  return { proof, closedProof := bind proof, replaceProof }

/-- The two search equations use choice inside the proof of a Fin bound. Compare the
complete, binder-closed proof types and recheck the single replacement in both kernels. -/
private def checkedFinBound (official strict : Environment) (owner name : Name)
    (pinned target : Expr) : Bool := (Option.isSome <| do
  guard ((owner == `Init.Data.Array.Find && name == ``Array.findFinIdx?_eq_pmap_findIdx?) ||
    (owner == `Init.Data.List.Find && name == ``List.findFinIdx?_eq_pmap_findIdx?))
  let src ← finBoundSite? id pinned
  let dst ← finBoundSite? InitKernelPort.portName target
  let prop ← (Kernel.check official {} src.closedProof).toOption
  let strictProp ← (Kernel.check strict {} dst.closedProof).toOption
  guard ((← (Kernel.check official {} prop).toOption).isProp &&
    (← (Kernel.check strict {} strictProp).toOption).isProp)
  let translate := InitKernelPort.translate InitKernelPort.portName
  guard (Kernel.isDefEqGuarded strict {} (translate prop) strictProp)
  let revised := src.replaceProof (InitKernelPort.translate InitKernelPort.originalName dst.proof)
  guard ((Kernel.check official {} revised).isOk && Kernel.isDefEqGuarded official {} pinned revised)
  let expected := translate revised
  guard ((Kernel.check strict {} expected).isOk && Kernel.isDefEqGuarded strict {} expected target))

/-- The public `npow a 0` branch reduces for an arbitrary `a`. Check the application
in the exported upstream environment, then check both translated endpoints in the strict one. -/
private def checkedEnvelopePowZero (visible strict : Environment) (owner : Name) (source : ConstantInfo)
    (pinned target : Expr) : Bool := (Option.isSome <| do
  guard (owner == `Init.Grind.Ring.Envelope && source.name == `Lean.Grind.Ring.OfSemiring.pow_zero)
  let entry ← visible.find? source.name
  guard (source.isTheorem && entry.levelParams == source.levelParams && entry.type.equal source.type &&
    pinned.getForallArity == 3)
  let (_, lhs, rhs) ← pinned.getForallBody.eq?
  guard (lhs.isAppOfArity `Lean.Grind.Ring.OfSemiring.npow 4 &&
    rhs.isAppOfArity `Lean.Grind.Ring.OfSemiring.natCast 3)
  let args := lhs.getAppArgs
  guard (args.extract 0 3 == #[.bvar 2, .bvar 1, .bvar 0] &&
    rhs.getAppArgs.extract 0 2 == #[.bvar 2, .bvar 1])
  guard (Kernel.isDefEqGuarded visible {} lhs.appArg! (mkRawNatLit 0) &&
    Kernel.isDefEqGuarded visible {} rhs.appArg! (mkRawNatLit 1))
  let reduced := pinned.replace fun e => if e.equal lhs then some rhs else none
  guard ((Kernel.check visible {} pinned).isOk && (Kernel.check visible {} reduced).isOk &&
    Kernel.isDefEqGuarded visible {} pinned reduced)
  let translated := InitKernelPort.translate InitKernelPort.portName reduced
  guard ((Kernel.check strict {} translated).isOk && Kernel.isDefEqGuarded strict {} translated target))

/-- The order of functions uses the pointwise relation. Its antisymmetry proof is
absent from the strict library. A theorem projecting just the relation can still
have a common public type. Reduce only subterms involving the missing instances,
then check the whole type in each exported environment. -/
private def checkedOrderFields (visible strict : Environment) (owner : Name)
    (source : ConstantInfo) (pinned target : Expr) (missing : Array Name) : Bool := Id.run do
  let orderInstances := [`Lean.Order.instOrderPi, `Lean.Order.ImplicationOrder.instOrder,
    `Lean.Order.ReverseImplicationOrder.instOrder, `Lean.Order.instPartialOrderStateT,
    `Lean.Order.instPartialOrderStateRefT', `Lean.Order.instPartialOrderReaderT,
    `Lean.Grind.Ring.OfSemiring.instLEQOfOrderedAdd, `Lean.Grind.Ring.OfSemiring.instLTQOfOrderedAdd]
  let absent := missing.map InitKernelPort.originalName
  unless source.isTheorem && absent.all orderInstances.contains &&
      (visible.find? source.name).any (fun ci => ci.type.equal source.type) &&
      visible.getModuleIdxFor? source.name == visible.getModuleIdx? owner do return false
  let usesMissing := fun (e : Expr) => e.getUsedConstants.any absent.contains
  let mut reduced := pinned
  for _ in [:16] do
    let step := reduced.replace fun e => do
      guard ((e.isApp || e.isProj) && usesMissing e && !e.getAppFn.constName?.any absent.contains)
      let simplified ← (Kernel.whnf visible {} e).toOption
      guard (!simplified.equal e)
      return simplified
    if step.equal reduced then break
    reduced := step
  let translated := InitKernelPort.translate InitKernelPort.portName reduced
  return !usesMissing reduced && (Kernel.check visible {} pinned).isOk &&
    (Kernel.check visible {} reduced).isOk && Kernel.isDefEqGuarded visible {} pinned reduced &&
    (Kernel.check strict {} translated).isOk && Kernel.isDefEqGuarded strict {} translated target

/-- The kernel names a recursor's minor premises after its constructors. Translate those
binder labels alongside the constructor constants when comparing serialized public types. -/
private def recursorBinders (rules : List RecursorRule) : Expr → Expr
  | .forallE label type body bi =>
    let label := if rules.any (·.ctor == label) then InitKernelPort.portName label else label
    .forallE label type (recursorBinders rules body) bi
  | body => body

/-- Check the pinned type in the strict public environment with the original universe
binders. A Fin bound proof may be replaced only after checking proof irrelevance. -/
public def originalTypeGap? (official visible strict : Environment) (owner : Name)
    (source target : ConstantInfo) : Option String := Id.run do
  if source.numLevelParams != target.numLevelParams then return some "universe parameter count"
  let pinned := source.type.instantiateLevelParams source.levelParams (target.levelParams.map Level.param)
  let expected := InitKernelPort.translate InitKernelPort.portName pinned
  if expected.equal target.type then return none
  if let .recInfo recursor := source then
    if (recursorBinders recursor.rules expected).equal target.type then return none
  let missing := (expected.getUsedConstants.filter (fun n => !strict.contains n)).qsort Name.lt
  unless missing.isEmpty do
    if checkedFinBound official strict owner source.name pinned target.type ||
        checkedEnvelopePowZero visible strict owner source pinned target.type ||
        checkedOrderFields visible strict owner source pinned target.type missing ||
        EnvelopePublicTypes.checked visible strict owner source pinned target.type then return none
    return some ("missing type dependencies: " ++ String.intercalate ", " (missing.toList.map Name.toString))
  if (Kernel.check strict {} expected).isOk && Kernel.isDefEqGuarded strict {} expected target.type then
    return none
  return some "pinned type does not check or convert to the exported type"

end OmegaChecks.InitInventory
