module
public import Lean
import OmegaChecks.InitPort.Translation
import OmegaChecks.InitInventory.EnvelopeOrder

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

open Meta in
/-- At universe zero the public reduction of these comparisons retains the whole
representative-coherence argument, including when strict order adds extra binders. -/
public def orderCoherenceGap? (visible strict witnesses : Environment) (owner : Name)
    (source : ConstantInfo) : IO (Option String) := do
  let proof := `Lean.Grind.IntModule.OfNatModule.instLEQOfOrderedAdd._proof_3
  let witness := ``OmegaChecks.InitBoundaries.EnvelopeOrder.propextFromModuleLift
  unless owner == `Init.Grind.Module.Envelope && source.name.getPrefix == `Lean.Grind.IntModule.OfNatModule &&
      ["mk_le_mk", "toQ_le", "toQ_lt"].contains source.name.getString! do return none
  let pinned := source.type.instantiateLevelParams source.levelParams [.zero]
  let some reduced := reduceType visible strict {} pinned | return none
  unless source.isTheorem && visible.getModuleIdxFor? source.name == visible.getModuleIdx? owner &&
      (visible.find? source.name).any (fun e => e.type.equal source.type) &&
      (Kernel.check visible {} reduced).isOk && Kernel.isDefEqGuarded visible {} pinned reduced do return none
  let check := forallTelescope reduced fun _ conclusion => do
    let some (lhs, _) := conclusion.iff? | throwError "expected a comparison equivalence"
    let some call := lhs.find? (fun e => e.getAppFn.isConstOf proof) | throwError "missing comparison coherence"
    let args := call.getAppArgs
    unless args.all Expr.isFVar do throwError "specialized representative-coherence argument"
    let complete ← mkLambdaFVars args call
    let actual ← Lean.ofExceptKernelException (Kernel.check visible {} complete)
    let entry ← getConstInfo proof
    unless !complete.hasFVar && Kernel.isDefEqGuarded visible {} complete (mkConst proof [.zero]) &&
        Kernel.isDefEqGuarded visible {} actual (entry.type.instantiateLevelParams entry.levelParams [.zero]) do
      throwError "the public comparison does not require the complete representative coherence"
    let result ← Lean.ofExceptKernelException (Kernel.check witnesses {} (mkApp (mkConst witness) complete))
    unless Kernel.isDefEqGuarded witnesses {} result (← getConstInfo ``propext).type &&
        (← collectAxioms witness).isEmpty do throwError "invalid reduction to propositional extensionality"
  (check.run' |>.toIO' {fileName := "<module order coherence>", fileMap := default} {env := witnesses})
  return some s!"The public comparison at universe zero requires the full representative coherence. {witness} reduces that argument to propext."

/-- Verify the specialized comparison against the fully reduced pinned representative formula. -/
public def representativeTypeMatches (official strict : Environment) (pinned target : Expr) : Bool :=
  (Option.isSome <| do
    let reduced ← reduceType official strict {} pinned
    guard ((Kernel.check official {} pinned).isOk && (Kernel.check official {} reduced).isOk &&
      Kernel.isDefEqGuarded official {} pinned reduced)
    let translated := InitKernelPort.translate InitKernelPort.portName reduced
    guard ((Kernel.check strict {} translated).isOk && Kernel.isDefEqGuarded strict {} translated target))

/-- Identify the remaining operation in an exported envelope equation. Importing private
bodies can simplify a representative comparison beyond the upstream public interface. -/
public def reductionGap? (official visible strict : Environment) (owner : Name) (source : ConstantInfo)
    (pinned target : Expr) : Option String := do
  let name := source.name
  let moduleLaw := owner == `Init.Grind.Module.Envelope && name.getPrefix == `Lean.Grind.IntModule.OfNatModule &&
    ["mk_le_mk", "toQ_add", "toQ_le", "toQ_lt", "toQ_smul", "toQ_zero"].contains name.getString!
  let ringEquation := owner == `Init.Grind.Ring.CommSemiringAdapter &&
    name.getPrefix == `Lean.Grind.CommRing.Expr.denoteSAsRing &&
    ["eq_4", "eq_5", "eq_6", "eq_def"].contains name.getString!
  guard ((moduleLaw || ringEquation) && source.isTheorem && (Kernel.check strict {} target).isOk)
  let entry ← visible.find? name
  guard (entry.levelParams == source.levelParams && entry.type.equal source.type)
  let reduced ← reduceType visible strict {} pinned
  guard ((Kernel.check visible {} pinned).isOk && (Kernel.check visible {} reduced).isOk &&
    Kernel.isDefEqGuarded visible {} pinned reduced)
  let translated := InitKernelPort.translate InitKernelPort.portName reduced
  let absent := (translated.getUsedConstants.filter (!strict.contains ·)).qsort Name.lt
  guard (!absent.isEmpty && !(Kernel.check strict {} translated).isOk)
  let original := (InitKernelPort.translate InitKernelPort.portName pinned).getUsedConstants
  let message := if absent.all original.contains then
      "Public reduction of the pinned statement retains the unavailable instance."
    else
      "Public reduction of the pinned statement still requires " ++
        String.intercalate ", " (absent.toList.map Name.toString) ++ "."
  if representativeTypeMatches official strict pinned target then
    return message ++ " The private representative reduction converts to the exported strict statement."
  return message

end OmegaChecks.InitInventory.EnvelopePublicTypes
