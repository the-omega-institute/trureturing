import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurements.FiniteLabelRecordDilation
import Reg.Support.DependentFamily

/-! The rounded class cost observes the pure environment dimension. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurements.FiniteLabelRecordDilation
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Quantum.Measurements.FiniteLabelRecordDilation

universe u v

@[reducible] def signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ e => e) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun a => nomatch a)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {B : Type u} {J : Type v} [Fintype B] [DecidableEq B] [Fintype J]
    {P : Set B} (label : P → J) {d e : ℕ}, 0 < e →
    (HasPerfectLabelRecord label d e ↔
      Fintype.card B ≤ d * e ∧ memorySlots label (R.readout () () e) ≤ d)

private theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  let B := ULift.{u} (Fin 2)
  let J := ULift.{v} Unit
  let label : ↥(Set.univ : Set B) → J := fun _ => ⟨()⟩
  have hFiber : Nat.card {b : ↥(Set.univ : Set B) // label b = (⟨()⟩ : J)} = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hSlots (e : ℕ) : memorySlots label e = 2 ⌈/⌉ e := by
    unfold memorySlots
    rw [Fintype.sum_unique]
    exact congrArg (· ⌈/⌉ e) hFiber
  have hRecord : HasPerfectLabelRecord label 1 2 :=
    (perfectLabelRecord_iff label (by decide)).mpr ⟨by decide, by rw [hSlots]; decide⟩
  have hFalse := ((h label (d := 1) (e := 2) (by decide)).mp hRecord).2
  change memorySlots label 1 ≤ 1 at hFalse
  rw [hSlots] at hFalse
  exact (by decide : ¬ 2 ⌈/⌉ 1 ≤ 1) hFalse

def family : Registration arena.{u, v} (type_of% @perfectLabelRecord_iff.{u, v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@perfectLabelRecord_iff.{u, v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change (1 : ℕ) ≠ 2
    decide

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@perfectLabelRecord_iff.{u, v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Measurements.FiniteLabelRecordDilation.perfectLabelRecord_iff.audit
  realizationName := `Reg.D5.S3.Quantum.Measurements.FiniteLabelRecordDilation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v}⟩
  objectArena := .source ⟨arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, v} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ e => e) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurements.FiniteLabelRecordDilation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

end Reg.D5.S3.Quantum.Measurements.FiniteLabelRecordDilation
