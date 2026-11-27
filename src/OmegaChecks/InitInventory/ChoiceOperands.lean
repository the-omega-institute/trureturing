module
public import Lean
import all Init.Classical
import all Init.WFExtrinsicFix
import all Init.While
import all Init.Data.Option.Lemmas
import all Init.Control.Lawful.MonadAttach.Lemmas
public import OmegaChecks.InitInventory.Logic
import all OmegaChecks.InitInventory.Logic

open Lean
namespace OmegaChecks.InitBoundaries.ChoiceOperands

/-- An implementation of the public selector supplies a choice function on every nonempty sort. -/
public def fromChoice (select : type_of% @Classical.choice.{u}) : type_of% @Classical.choice.{u} := @select

-- The congruence equation needs only reflexivity once a selector is supplied.
example (select : type_of% @Classical.choice.{u}) {α : Sort u} (h : Nonempty α) : select h = select h := rfl

/-- The value-producing head of an official equation and its reduction to choice. -/
public structure Operand where
  name : Name
  witness : Name
  levels : List Level

private def fixWitness? : Name → Option Name
  | ``WellFounded.extrinsicFix | ``WellFounded.partialExtrinsicFix => some ``choiceFromFix
  | ``WellFounded.extrinsicFix₂ | ``WellFounded.partialExtrinsicFix₂ => some ``choiceFromFix₂
  | ``WellFounded.extrinsicFix₃ | ``WellFounded.partialExtrinsicFix₃ => some ``choiceFromFix₃
  | _ => none

private def congruenceWitness? (operand : Name) : Option Name :=
  match operand with
  | ``Classical.choice => some ``fromChoice
  | ``Classical.ofNonempty => some ``choiceFromOfNonempty
  | ``Classical.choose => some ``choiceFromChoose
  | ``Exists.choose => some ``choiceFromExistsChoose
  | other => fixWitness? other

/-- Read the left value of the concluding equality directly from the defining module's type.
The witness consumes the complete polymorphic operation used to state the equation. -/
public def operand? (owner : Name) (source : ConstantInfo) : Option Operand := do
  guard (owner.getRoot == `Init)
  guard source.isTheorem
  let congruence := source.name matches .str _ "congr_simp"
  guard (owner == `Init.WFExtrinsicFix || congruence)
  let mut conclusion := source.type
  while conclusion.isForall do conclusion := conclusion.bindingBody!
  guard (conclusion.isAppOfArity ``Eq 3)
  let args := conclusion.getAppArgs
  guard args[0]!.getAppFn.isBVar
  let .const name levels := args[1]!.getAppFn | none
  let witness? := if congruence && source.name.getPrefix == name then congruenceWitness? name
    else if owner == `Init.WFExtrinsicFix then fixWitness? name else none
  let witness ← witness?
  return ⟨name, witness, levels⟩

private def check (env : Environment) (owner : Name) (source : ConstantInfo) (operand : Operand) : Except String Unit := do
  let ⟨name, witness, levels⟩ := operand
  let some op := env.find? name | throw s!"missing operand {name} in {owner}/{source.name}"
  let some proof := env.find? witness | throw s!"missing choice witness {witness}"
  let some target := env.find? ``Classical.choice | throw "missing official choice type"
  let some (.param targetLevel) := levels.getLast?
    | throw s!"choice at a fixed universe in {owner}/{source.name}"
  unless source.levelParams.contains targetLevel && levels.length == op.numLevelParams &&
      levels.length == proof.numLevelParams && target.isAxiom do
    throw s!"incompatible operand universes in {owner}/{source.name}"
  let domain := op.type.instantiateLevelParams op.levelParams levels
  let codomain := target.type.instantiateLevelParams target.levelParams [.param targetLevel]
  let expected := Expr.forallE .anonymous domain codomain .default
  unless proof.type.instantiateLevelParams proof.levelParams levels == expected do
    throw s!"incorrect choice witness type for {owner}/{source.name}"

open Meta in
/-- Specialize a congruence using the arguments of the existing reduction. Under an arbitrary
implementation of its operator, each of the two resulting endpoints is a complete choice function. -/
private def checkCongruenceEndpoints (source : ConstantInfo) (operand : Operand) : MetaM Unit := do
  let u := Level.param `u
  let sourceLevels := source.levelParams.map fun param =>
    if operand.levels.getLast? == some (.param param) then u else Level.one
  let opLevels := operand.levels.map fun level => level.instantiateParams source.levelParams sourceLevels
  let op ← getConstInfo operand.name
  let choice ← getConstInfo ``Classical.choice
  let env ← getEnv
  let choiceType := choice.type.instantiateLevelParams choice.levelParams [u]
  withLocalDeclD `op (op.type.instantiateLevelParams op.levelParams opLevels) fun port => do
    let siteType := (source.type.instantiateLevelParams source.levelParams sourceLevels).replace fun term =>
      if term == mkConst operand.name opLevels then some port else none
    forallTelescope choiceType fun params _ => do
      let selected ← withTransparency .all <| whnf (mkAppN (mkApp (mkConst operand.witness opLevels) port) params)
      let (args, _, eqn) ← forallMetaTelescope siteType
      let some (_, lhs, rhs) := eqn.eq? | throwError "expected equality"
      unless lhs.getAppFn == port && selected.getAppFn == port &&
          lhs.getAppNumArgs == selected.getAppNumArgs do
        throwError "unexpected application {lhs} / {selected}"
      -- Match the left endpoint to the self-loop or selector application in the constructive witness.
      for (arg, value) in lhs.getAppArgs.zip selected.getAppArgs do
        let arg ← instantiateMVars arg
        if arg.isMVar then arg.mvarId!.assign value
        else unless ← isDefEq arg value do throwError "cannot specialize {arg} to {value}"
      -- A congruence now needs only equality of identical predicates or recursion steps.
      for arg in args do
        unless ← arg.mvarId!.isAssigned do
          discard <| observing? arg.mvarId!.refl
      let args ← args.mapM instantiateMVars
      if args.any (·.hasMVar) then throwError "unresolved arguments for {source.name}: {args}"
      -- Check the whole specialization, including the argument types and equality hypotheses.
      withLocalDeclD `law siteType fun law => do
        let app ← mkLambdaFVars (#[port] ++ params ++ #[law]) (mkAppN law args)
        discard <| Lean.ofExceptKernelException (Kernel.check env {} app)
      let expected ← mkForallFVars #[port] choiceType (usedOnly := false)
      for endpoint in #[lhs, rhs] do
        let abstracted ← mkLambdaFVars (#[port] ++ params) (← instantiateMVars endpoint)
        let actual ← Lean.ofExceptKernelException (Kernel.check env {} abstracted)
        unless Kernel.isDefEqGuarded env {} actual expected do
          throwError "{source.name} has a specialized endpoint of unexpected type {actual}"

run_cmd
  let env ← getEnv
  for (owner, data) in env.header.moduleNames.zip env.header.moduleData do
    unless owner.getRoot == `Init do continue
    for source in data.constants do
      unless isPrivateName source.name || source.name.isInternalOrNum || source.name.hasMacroScopes do
        if let some operand := operand? owner source then
          if let .error msg := check env owner source operand then throwError "{msg}"
          if source.name.getPrefix == operand.name then
            Elab.Command.liftCoreM <| Meta.MetaM.run' (checkCongruenceEndpoints source operand)

end OmegaChecks.InitBoundaries.ChoiceOperands
