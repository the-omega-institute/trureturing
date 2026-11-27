import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.LocalWiring.BoundedBinaryRecurrenceSharpness
import Reg.Support.DependentFamily

/-! Read the chosen actual witness's output at their first divergent index. -/

namespace Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.BoundedBinaryRecurrenceSharpness

open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring.BoundedBinaryRecurrenceSharpness
open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring.BoundedBinaryRecurrence (Legal)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Σ _ : Nat, Nat
  State _ := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p side => witnessOutput p.1 p.2 side) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law F := ∀ (d : Nat) (_hd : 1 ≤ d),
    (∀ (v : Nat), v < 2*d →
      (∀ side : Bool, F.readout () ⟨d, v⟩ side = side) ∧
      Legal d (witnesses d v).1 ∧ Legal d (witnesses d v).2 ∧
      (∀ i < v, (witnesses d v).1 i = (witnesses d v).2 i) ∧
      (witnesses d v).1 v ≠ (witnesses d v).2 v) ∧
    (∀ v : Nat, UniformlySeparates d v ↔ 2*d ≤ v)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := ((h 1 (by decide)).1 1 (by decide)).1 true
  change false = true at bad
  cases bad

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨⟨1, 1⟩, false, true, ?_⟩
  change witnessOutput 1 1 false ≠ witnessOutput 1 1 true
  decide

def family : Registration arena (type_of% bounded_binary_recurrence_sharpness) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨bounded_binary_recurrence_sharpness, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bounded_binary_recurrence_sharpness) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.BoundedBinaryRecurrenceSharpness.unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.BoundedBinaryRecurrenceSharpness.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.LocalWiring.BoundedBinaryRecurrenceSharpness
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "body", "fn", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.BoundedBinaryRecurrenceSharpness
