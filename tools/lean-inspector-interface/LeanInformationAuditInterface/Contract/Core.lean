import Lean

namespace LeanInformationAudit.Contract
open Lean
universe u

/-- The value is kernel checked; its source identity is checked by the report. -/
structure Ref (T : Sort u) : Type u where
  name : Name
  value : T

inductive OptionValue where
  | bool (value : Bool)
  | nat (value : Nat)
  | int (value : Int)
  | string (value : String)
  | name (value : Name)

structure OptionSetting where
  name : Name
  value : OptionValue

structure ReadoutSelection where
  path : Array String
  stateBinder : Nat
  functionOperand : Bool
  stateOperand : Option (Array String)
  booleanPredicate : Bool

structure DefinitionSelection where
  owner : Name
  name : Name
  path : Array String

structure SourceSelection where
  owner : Name
  definition : Option DefinitionSelection
  coordinates : Array Nat
  readouts : Array ReadoutSelection

inductive Continuation (T : Sort u) : Type u where
  | absent
  | unknown
  | evidence (value : Ref T)

end LeanInformationAudit.Contract
