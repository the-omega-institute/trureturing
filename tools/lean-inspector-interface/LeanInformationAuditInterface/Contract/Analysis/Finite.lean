import LeanInformationAuditInterface.Contract.Analysis.Source
import D5.S3.ConceptDynamics.InformationEscapeCounting.Fused

namespace LeanInformationAudit.Analysis
open D5.S3.ConceptDynamics.InformationEscape
universe u t s r o a v

/-- Scope is mathematical evidence. Restriction counts its complete subtype;
quotient counts its classes. Neither is the original domain's cardinality.
All roles descend, so the selected total task and every layer descend as well. -/
inductive DomainScope {S : DependentFamily.Signature.{t,s,r,o,a}}
    (actual : DependentFamily.Realization S) (parameter : S.Params)
    (State : Type v) (readout : ∀ role, State → S.Output role parameter) where
  | whole (equiv : State ≃ S.State parameter)
      (commutes : ∀ role x, readout role x = actual.readout role parameter (equiv x))
  | restriction (predicate : S.State parameter → Prop)
      (equiv : State ≃ {x // predicate x})
      (commutes : ∀ role x, readout role x = actual.readout role parameter (equiv x).val)
  | quotient (project : S.State parameter → State)
      (surjective : Function.Surjective project)
      (commutes : ∀ role x, readout role (project x) = actual.readout role parameter x)

/-- A finite request selects an explicit parameter fiber. No witness here
asserts finiteness of other fibers or supplies a source probability law. -/
structure Domain {Statement : Sort u} {occurrence : Statement}
    (source : Source.{u,t,s,r,o,a} occurrence) where
  parameter : source.signature.Params
  State : Type v
  readout : ∀ role, State → source.signature.Output role parameter
  scope : DomainScope source.actual parameter State readout

/-- Identity presentation of the whole selected fiber. -/
abbrev Domain.fiber {Statement : Sort u} {occurrence : Statement}
    (source : Source.{u,t,s,r,o,a} occurrence) (parameter : source.signature.Params) :
    Domain source where
  parameter := parameter
  State := source.signature.State parameter
  readout := fun role => source.actual.readout role parameter
  scope := .whole (Equiv.refl _) (fun _ _ => rfl)

/-- Constructor data that can be reported without evaluating author functions. -/
inductive Value where
  | unit
  | bool (value : Bool)
  | nat (value : Nat)
  | int (value : Int)
  | text (value : String)
  | none
  | some (value : Value)
  | pair (first second : Value)
  deriving DecidableEq, Repr

/-- Complete SPEC 8.1 acquisition. Row positions refer to the actual enumerated
states. Both kernel directions are certified separately from reported-value
and total-task decoding; no injective encoding of an infinite output is needed.
Every initial and subsequent layer is retained by its original plan index. -/
structure FinitePresentation {Statement : Sort u} {occurrence : Statement}
    {source : Source.{u,t,s,r,o,a} occurrence} (plan : Plan source)
    (domain : Domain.{u,t,s,r,o,a,v} source) where
  stateFintype : Fintype domain.State
  stateDecidableEq : DecidableEq domain.State
  enumeration : Arena.StateEnumeration
    { State := domain.State, stateFintype := stateFintype,
      stateDecidableEq := stateDecidableEq }
  values : source.signature.Role → Fin enumeration.states.length → Value
  decode : ∀ role, Value → Option (source.signature.Output role domain.parameter)
  values_correct : ∀ role row, decode role (values role row) =
    some (domain.readout role (enumeration.states.get row))
  kernel : source.signature.Role → Fin enumeration.states.length →
    Fin enumeration.states.length → Bool
  kernel_correct : ∀ role left right, kernel role left right = true ↔
    domain.readout role (enumeration.states.get left) =
      domain.readout role (enumeration.states.get right)
  taskValues : Fin enumeration.states.length → Value
  task_correct : ∀ row, decode plan.task (taskValues row) =
    some (domain.readout plan.task (enumeration.states.get row))
  layers : Fin (plan.additions.length + 1) → Fin enumeration.states.length →
    Fin enumeration.states.length → Bool
  layers_correct : ∀ position left right, layers position left right = true ↔
    ∀ role ∈ plan.selected position.val,
      domain.readout role (enumeration.states.get left) =
        domain.readout role (enumeration.states.get right)

/-- Availability of numerical acquisition is separate from typed source ingress.
`infinite` has evidence; `unavailable` makes no cardinality or rate assertion. -/
inductive Acquisition {Statement : Sort u} {occurrence : Statement}
    {source : Source.{u,t,s,r,o,a} occurrence} (plan : Plan source) where
  | unavailable (reason : String)
  | infinite (parameter : source.signature.Params)
      (evidence : Infinite (source.signature.State parameter))
  | finite (domain : Domain.{u,t,s,r,o,a,v} source)
      (presentation : FinitePresentation plan domain)

/-- A complete generic author client, indexed by the actual theorem occurrence.
Raw occurrence/operand validation is still required at compiler acquisition. -/
structure Client {Statement : Sort u} (occurrence : Statement) where
  source : Source.{u,t,s,r,o,a} occurrence
  plan : Plan source
  acquisition : Acquisition.{u,t,s,r,o,a,v} plan

end LeanInformationAudit.Analysis
