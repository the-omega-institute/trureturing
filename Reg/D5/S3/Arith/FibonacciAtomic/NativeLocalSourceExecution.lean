import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.NativeLocalSourceExecution
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution composition)
open _root_.D5.S3.Arith.FibonacciAtomic.NativeLocalSourceExecution
open _root_.D5.S3.Arith.FibonacciAtomic.NativeLocalSourceExecution
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.NativeLocalSourceExecution
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option Source
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature := realize signature (fun _ _ t => replay t (oldFrontier t)) (fun e => nomatch e)
abbrev rejected : Realization signature := realize signature (fun _ _ _ => none) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law A := (∀ t : Source, A.readout () () t = some (substitution t) ∧
      (oldFrontier t).length = t.length ∧ Native (substitution t)) ∧
    (∀ t : Source, Native t →
      edit t (leftmost t) false = some (splitLeft t) ∧ Native (splitLeft t) ∧
      composition (splitLeft t) = composition t + (1,0)) ∧
    (∀ (t u : Source) (es : List Event), replay t es = some u →
      eventIndex u = eventIndex t + es.length) ∧
    (∀ t : Source, Native t →
      eventIndex (substitution t) = eventIndex t + t.length ∧
      eventIndex (splitLeft t) = eventIndex t + 1 ∧
      (eventIndex t = 1 ↔ t = .of false)) ∧
    (∀ t : Source, (∃ es : List Event, replay (.of true) es = some t) ↔
      native true t = true) ∧
    (∀ t : Source, Native t ↔
      (∃ es : List Event, replay (.of true) es = some t) ∧ t ≠ .of true)

private theorem actual_law : arena.Law actual := by exact native_execution

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have impossible := (law (.of true)).1
  change (none : Option Source) = some (substitution (.of true)) at impossible
  cases impossible

def evidence : Registration arena (type_of% (@native_execution)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), .of true, .of false, ?_⟩
    intro eq
    change (some (.of false) : Option Source) = some (.mul (.of false) (.of true)) at eq
    cases eq

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_execution) (Realization signature) (Unit → Type) Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.NativeLocalSourceExecution.native_execution.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.NativeLocalSourceExecution.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence,objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => replay t (oldFrontier t)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.NativeLocalSourceExecution
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn","arg","body","fn","arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms registration

end Reg.D5.S3.Arith.FibonacciAtomic.NativeLocalSourceExecution
