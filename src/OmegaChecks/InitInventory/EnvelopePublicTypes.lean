module
public import Lean
import OmegaChecks.InitPort.Translation

open Lean
namespace OmegaChecks.InitInventory.EnvelopePublicTypes

private def supported (owner name : Name) : Bool :=
  (owner == `Init.Grind.Ring.Envelope &&
    name.getPrefix == `Lean.Grind.Ring.OfSemiring &&
    ["ofNat_succ", "toQ_add", "toQ_lt", "toQ_mul", "toQ_ofNat", "toQ_zero"].contains name.getString!) ||
  (owner == `Init.Grind.Ring.CommSemiringAdapter &&
    name.getPrefix == `Lean.Grind.CommRing.Expr.denoteSAsRing &&
    ["eq_1", "eq_2", "eq_7", "eq_8", "eq_9"].contains name.getString!)

private def reduceEndpoint (official strict : Environment) (ctx : LocalContext)
    (term : Expr) : Option Expr := do
  if term.getUsedConstants.all (fun n => strict.contains (InitKernelPort.portName n)) then return term
  let reduced ← (Kernel.whnf official ctx term).toOption
  if reduced.isAppOfArity ``And 2 then
    -- Strict inequality in this envelope is a comparison and the negation of its converse.
    let order ← (Kernel.whnf official ctx reduced.appFn!.appArg!).toOption
    let negation := reduced.appArg!
    guard (negation.isAppOfArity ``Not 1)
    let converse ← (Kernel.whnf official ctx negation.appArg!).toOption
    return mkApp2 reduced.getAppFn order (.app negation.appFn! converse)
  return reduced

/-- Expose the quantified arguments before taking the public normal forms of only the
endpoints that depend on an unavailable envelope operation or projected field. -/
private partial def reduceType (official strict : Environment) (ctx : LocalContext)
    (type : Expr) : Option Expr := do
  if let .forallE name dom body bi := type then
    let id : FVarId := ⟨.num `_envelope ctx.numIndices⟩
    let x := mkFVar id
    let localCtx := ctx.mkLocalDecl id name dom bi
    let result ← reduceType official strict localCtx (body.instantiate1 x)
    return .forallE name dom (result.abstract #[x]) bi
  guard (type.isAppOfArity ``Eq 3 || type.isAppOfArity ``Iff 2)
  return mkAppN type.getAppFn (← type.getAppArgs.mapM (reduceEndpoint official strict ctx))

/-- Reduce the pinned public statement first. Translate that complete statement forwards
and ask the ordinary strict kernel to check and compare it with its exported theorem. -/
public def checked (official strict : Environment) (owner : Name) (source : ConstantInfo)
    (pinned target : Expr) : Bool := (Option.isSome <| do
  guard (supported owner source.name && source.isTheorem)
  let entry ← official.find? source.name
  guard (entry.levelParams == source.levelParams && entry.type.equal source.type)
  let reduced ← reduceType official strict {} pinned
  guard ((Kernel.check official {} pinned).isOk && (Kernel.check official {} reduced).isOk &&
    Kernel.isDefEqGuarded official {} pinned reduced)
  let translated := InitKernelPort.translate InitKernelPort.portName reduced
  guard (translated.getUsedConstants.all strict.contains && (Kernel.check strict {} translated).isOk &&
    Kernel.isDefEqGuarded strict {} translated target))

end OmegaChecks.InitInventory.EnvelopePublicTypes
