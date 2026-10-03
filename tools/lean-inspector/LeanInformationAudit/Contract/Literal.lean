import LeanInformationAuditInterface.Contract.Core

namespace LeanInformationAudit.Contract.Literal
open Lean

/-- No reduction, user constants, metavariable instantiation or native execution. -/
def closed (e : Expr) : Bool :=
  !e.hasFVar && !e.hasMVar && !e.hasLooseBVars && !e.hasLevelMVar

def reject {α : Type} (field : String) (e : Expr) : Except String α :=
  .error s!"contract.literal:{field}:nonliteral:{e.getAppFn.constName?.getD .anonymous}"

def constructor (name : Name) (count : Nat) (field : String)
    (e : Expr) : Except String (Array Expr) := do
  let e := e.consumeMData
  unless closed e && e.getAppFn.constName? == some name do reject field e
  let args := e.getAppArgs
  unless args.size == count do
    throw s!"contract.literal:{field}:arity:{name}"
  return args

partial def nat (field : String) (e : Expr) : Except String Nat := do
  let e := e.consumeMData
  if let .lit (.natVal n) := e then return n
  if e.isConstOf ``Nat.zero then return 0
  if e.isAppOfArity ``Nat.succ 1 then return (← nat field e.getAppArgs[0]!) + 1
  if e.isAppOfArity ``OfNat.ofNat 3 then
    let args := e.getAppArgs
    if args[0]!.isConstOf ``Nat && args[2]!.isAppOfArity ``instOfNatNat 1 &&
        args[2]!.getAppArgs[0]! == args[1]! then
      return ← nat field args[1]!
  reject field e

def string (field : String) (e : Expr) : Except String String := do
  let .lit (.strVal s) := e.consumeMData | reject field e
  return s

def bool (field : String) (e : Expr) : Except String Bool := do
  let e := e.consumeMData
  if e.isConstOf ``Bool.true then return true
  if e.isConstOf ``Bool.false then return false
  reject field e

partial def name (field : String) (e : Expr) : Except String Name := do
  let e := e.consumeMData
  if e.isConstOf ``Name.anonymous then return .anonymous
  if e.isAppOfArity ``Name.str 2 then
    return .str (← name field e.getAppArgs[0]!) (← string field e.getAppArgs[1]!)
  if e.isAppOfArity ``Name.num 2 then
    return .num (← name field e.getAppArgs[0]!) (← nat field e.getAppArgs[1]!)
  -- Lean's quotation compiler uses these fixed constructor shorthands.
  for n in [1:9] do
    if e.isAppOfArity (.str ``Lean.Name s!"mkStr{n}") n then
      let mut result := Name.anonymous
      for arg in e.getAppArgs do result := result.str (← string field arg)
      return result
  reject field e

def optional (field : String) (e : Expr) : Except String (Option Expr) := do
  let e := e.consumeMData
  if e.isAppOfArity ``Option.none 1 then return none
  if e.isAppOfArity ``Option.some 2 then return some e.getAppArgs[1]!
  reject field e

partial def list (field : String) (e : Expr) : Except String (Array Expr) := do
  let e := e.consumeMData
  if e.isAppOfArity ``List.nil 1 then return #[]
  if e.isAppOfArity ``List.cons 3 then
    return #[e.getAppArgs[1]!] ++ (← list field e.getAppArgs[2]!)
  reject field e

def array (field : String) (e : Expr) : Except String (Array Expr) := do
  let e := e.consumeMData
  if e.isAppOfArity ``List.toArray 2 || e.isAppOfArity ``Array.mk 2 then
    return ← list field e.getAppArgs[1]!
  reject field e

def strings (field : String) (e : Expr) : Except String (Array String) := do
  (← array field e).mapM (string field)

def sourceSelection (e : Expr) : Except String Contract.SourceSelection := do
  let fs ← constructor ``Contract.SourceSelection.mk 4 "source_selection" e
  let definition ← (← optional "source_definition" fs[1]!).mapM fun value => do
    let ds ← constructor ``Contract.DefinitionSelection.mk 3 "source_definition" value
    return { owner := ← name "definition.owner" ds[0]!, name := ← name "definition.name" ds[1]!
             path := ← strings "definition.path" ds[2]! : Contract.DefinitionSelection }
  let readouts ← (← array "readouts" fs[3]!).mapM fun value => do
    let rs ← constructor ``Contract.ReadoutSelection.mk 5 "readout_selection" value
    return { path := ← strings "readout.path" rs[0]!, stateBinder := ← nat "state_binder" rs[1]!
             functionOperand := ← bool "function_operand" rs[2]!
             stateOperand := ← (← optional "state_operand" rs[3]!).mapM (strings "state_operand")
             booleanPredicate := ← bool "boolean_predicate" rs[4]! : Contract.ReadoutSelection }
  return { owner := ← name "source.owner" fs[0]!, definition
           coordinates := ← (← array "coordinates" fs[2]!).mapM (nat "coordinate"), readouts }

/-- Decode only fixed core numeral and negation instances, without reduction. -/
partial def int (field : String) (e : Expr) : Except String Int := do
  let e := e.consumeMData
  if e.isAppOfArity ``Int.ofNat 1 then
    return .ofNat (← nat field e.getAppArgs[0]!)
  if e.isAppOfArity ``Int.negSucc 1 then
    return .negSucc (← nat field e.getAppArgs[0]!)
  if e.isAppOfArity ``OfNat.ofNat 3 then
    let args := e.getAppArgs
    if args[0]!.isConstOf ``Int && args[2]!.isAppOfArity ``instOfNat 1 &&
        args[2]!.getAppArgs[0]! == args[1]! then return .ofNat (← nat field args[1]!)
  if e.isAppOfArity ``Neg.neg 3 then
    let args := e.getAppArgs
    if args[0]!.isConstOf ``Int && args[1]!.isConstOf ``Int.instNegInt then
      return -(← int field args[2]!)
  reject field e

def optionValue (e : Expr) : Except String DataValue := do
  let e := e.consumeMData
  let args := e.getAppArgs
  unless args.size == 1 do reject "option.value" e
  let value := args[0]!
  match e.getAppFn.constName? with
  | some ``Contract.OptionValue.bool => return .ofBool (← bool "option.bool" value)
  | some ``Contract.OptionValue.nat => return .ofNat (← nat "option.nat" value)
  | some ``Contract.OptionValue.string => return .ofString (← string "option.string" value)
  | some ``Contract.OptionValue.name => return .ofName (← name "option.name" value)
  | some ``Contract.OptionValue.int => return .ofInt (← int "option.int" value)
  | _ => reject "option.value" e

def options (e : Expr) : Except String Options := do
  let mut result : Options := {}
  let mut seen : NameSet := {}
  for row in ← array "options" e do
    let fs ← constructor ``Contract.OptionSetting.mk 2 "option_setting" row
    let key ← name "option.key" fs[0]!
    if seen.contains key then throw s!"contract.literal:options:duplicate:{key}"
    seen := seen.insert key
    result := result.insert key (← optionValue fs[1]!)
  return result

end LeanInformationAudit.Contract.Literal
