import Lean

namespace LeanInformationAudit.Contract
open Lean
universe u

/-- The value is kernel checked; its source identity is checked by the report. -/
structure Ref (T : Sort u) : Type u where
  value : T

/-- The evidence constructor has identical type and value indices. Literal
evidence therefore requires the same definitional correspondence as the raw
input binding; incomplete submissions impose no such correspondence. -/
inductive ExactMatch {T : Sort u} (expected : T) : {S : Sort u} → S → Type u where
  | evidence : ExactMatch expected expected
  | unknown {S : Sort u} {actual : S} : ExactMatch expected actual
  | absent {S : Sort u} {actual : S} : ExactMatch expected actual
  | unsupported {S : Sort u} {actual : S} (input : Name) : ExactMatch expected actual

/-- A raw mathematical obligation. Only `evidence` carries a proof of the
indexed proposition; the other constructors preserve incomplete submissions. -/
inductive Obligation (P : Prop) : Type where
  | evidence {Submitted : Prop} (input : Ref Submitted) (proof : P)
  | unknown
  | absent
  | unsupported (input : Name)

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
