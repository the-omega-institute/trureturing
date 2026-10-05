import LeanInformationAuditInterface.Contract.Core

namespace LeanInformationAudit.Contract.Literal
open Lean

/-- No user constant unfolding, metavariable instantiation or native execution. -/
def closed (e : Expr) : Bool :=
  !e.hasFVar && !e.hasMVar && !e.hasLooseBVars && !e.hasLevelMVar

/-- Decode bare constant references inside metadata constructor trees. Applied
functions remain opaque; no beta, zeta, projection or recursor evaluation runs. -/
def resolveReferences (find : Name → Option ConstantInfo)
    (e : Expr) (seen : NameSet := {}) (work : Nat := 4096) : Except String Expr :=
  match work with
  | 0 => throw "contract.cannot_decode:metadata:reference_work"
  | work + 1 => do
    match e with
    | .const name levels =>
      match find name with
      | some (.defnInfo info) =>
        unless info.safety == .safe && info.levelParams.length == levels.length do
          throw s!"contract.cannot_decode:metadata:{name}:unsafe_or_invalid_reference"
        if seen.contains name then throw s!"contract.cannot_decode:metadata:{name}:reference_cycle"
        resolveReferences find (info.value.instantiateLevelParams info.levelParams levels)
          (seen.insert name) work
      | some _ => return e
      | none => throw s!"contract.cannot_decode:metadata:{name}:missing_constant"
    | .app .. =>
      let args ← e.getAppArgs.mapM fun arg => resolveReferences find arg seen work
      return mkAppN e.getAppFn args
    | .mdata data body => return .mdata data (← resolveReferences find body seen work)
    | .letE name type value body nondep =>
      if closed body then return ← resolveReferences find body seen work
      return .letE name type (← resolveReferences find value seen work)
        (← resolveReferences find body seen work) nondep
    | .lam .. | .proj .. => throw "contract.cannot_decode:metadata:computation_required"
    | _ => return e
termination_by work

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

def nat (field : String) (e : Expr) : Except String Nat := do
  match e with
  | .mdata _ inner => nat field inner
  | .lit (.natVal n) => pure n
  | .const name _ => if name == ``Nat.zero then pure 0 else reject field e
  | .app (.const name _) value =>
    if name == ``Nat.succ then return (← nat field value) + 1
    else reject field e
  | .app (.app (.app (.const name _) type) value) numeralInstance =>
    if name == ``OfNat.ofNat && type.isConstOf ``Nat &&
        numeralInstance.isAppOfArity ``instOfNatNat 1 &&
        numeralInstance.getAppArgs[0]! == value then
      nat field value
    else reject field e
  | _ => reject field e

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

private def listWithTails (field : String) (e : Expr)
    (tails : Array (Array Expr)) : Except String (Array Expr) := do
  match e with
  | .mdata _ inner => listWithTails field inner tails
  | .letE _ type value body _ =>
    unless type.isAppOfArity ``List 1 && closed type do reject field e
    let tail ← listWithTails field value tails
    return ← listWithTails field body (tails.push tail)
  | .bvar index =>
    if index < tails.size then return tails[tails.size - 1 - index]!
    reject field e
  | .app (.const name _) _ =>
    if name == ``List.nil then pure #[] else reject field e
  | .app (.app (.app (.const name _) _) value) rest =>
    unless name == ``List.cons && closed value do reject field e
    return #[value] ++ (← listWithTails field rest tails)
  | _ => reject field e

/-- Decode the pinned compiler's literal list constructors and shared tails
without substituting, reducing or evaluating expressions. -/
def list (field : String) (e : Expr) : Except String (Array Expr) :=
  listWithTails field e #[]

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
