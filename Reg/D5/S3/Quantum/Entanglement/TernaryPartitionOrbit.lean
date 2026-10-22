import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.TernaryPartitionOrbit
import Reg.Support.DependentFamily

/-! The observed operand is the original anchored colouring, with its entire
arbitrary index type retained as a parameter. -/

namespace Reg.D5.S3.Quantum.Entanglement.TernaryPartitionOrbit

open _root_.D5.S3.Quantum.Entanglement.TernaryPartitionOrbit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

abbrev signature : Signature where
  Params := Type u
  State α := α → ZMod 3
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ α := Option α → ZMod 3
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ u => anchored u) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (α : Type u) (P : Set (α → ZMod 3)),
    (∀ u : α → ZMod 3, u ≠ 0 → (u ∈ P ↔ -u ∉ P)) →
    ∀ (u : α → ZMod 3), u ≠ 0 →
      ∃! v : α → ZMod 3, v ∈ P ∧
        SamePartition (R.readout () α u) (anchored v)

private theorem sample_representatives :
    ∀ u : PUnit.{u+1} → ZMod 3, u ≠ 0 →
      (u PUnit.unit = 1 ↔ (-u) PUnit.unit ≠ 1) := by
  intro u hu
  have hn : u PUnit.unit ≠ 0 := by
    intro h
    apply hu
    funext i
    cases i
    exact h
  have h : ∀ a : ZMod 3, a ≠ 0 → (a = 1 ↔ -a ≠ 1) := by decide
  exact h _ hn

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let P : Set (PUnit.{u+1} → ZMod 3) := {v | v PUnit.unit = 1}
  have hP : ∀ v : PUnit.{u+1} → ZMod 3, v ≠ 0 → (v ∈ P ↔ -v ∉ P) :=
    sample_representatives
  have hne : (fun _ : PUnit.{u+1} => (1 : ZMod 3)) ≠ 0 := by
    intro he
    have hf := congrFun he PUnit.unit
    norm_num at hf
  obtain ⟨v, hv, _⟩ := h PUnit P hP (fun _ => 1) hne
  have hv1 : v PUnit.unit = 1 := hv.1
  have he := (hv.2 none (some PUnit.unit)).mp rfl
  simpa [anchored, hv1] using he

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨PUnit, 0, (fun _ => 1), ?_⟩
  intro h
  have he := congrFun h (some PUnit.unit)
  norm_num [actual, realize, anchored] at he
  exact (by decide : (0 : ZMod 3) ≠ 1) he

def source_registration : Registration arena.{u}
    (∀ {α : Type u} (P : Set (α → ZMod 3)),
      (∀ u : α → ZMod 3, u ≠ 0 → (u ∈ P ↔ -u ∉ P)) →
      ∀ (u : α → ZMod 3), u ≠ 0 →
        ∃! v : α → ZMod 3, v ∈ P ∧ SamePartition (anchored u) (anchored v)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result.{u}, rejected, rejected_law⟩
  sensitivity := by
    letI : Subsingleton arena.signature.Role := by
      change Subsingleton Unit
      infer_instance
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.TernaryPartitionOrbit.result.{u})
      (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.TernaryPartitionOrbit.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.TernaryPartitionOrbit.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ _ u => anchored u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.TernaryPartitionOrbit
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.TernaryPartitionOrbit
