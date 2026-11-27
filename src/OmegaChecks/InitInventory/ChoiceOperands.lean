module
public import Lean
import all Init.WFExtrinsicFix
import all Init.While
import all Init.Data.Option.Lemmas
public import OmegaChecks.InitInventory.Logic

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

run_cmd
  let env ← getEnv
  for (owner, data) in env.header.moduleNames.zip env.header.moduleData do
    unless owner.getRoot == `Init do continue
    for source in data.constants do
      unless isPrivateName source.name || source.name.isInternalOrNum || source.name.hasMacroScopes do
        if let some operand := operand? owner source then
          if let .error msg := check env owner source operand then throwError "{msg}"

end OmegaChecks.InitBoundaries.ChoiceOperands
