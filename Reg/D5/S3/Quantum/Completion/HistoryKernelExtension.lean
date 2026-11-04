import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Completion.HistoryKernelExtension
import Reg.Support.DependentFamily

/-! Source-family audit candidates for primitive history-kernel positivity. -/

namespace Reg.D5.S3.Quantum.Completion.HistoryKernelExtension
open _root_.D5.S3.Quantum.Completion.HistoryKernelExtension
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ComplexOrder

universe u
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

abbrev signature : Signature where
  Params := Type u
  State X := X → X → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

private theorem zero_law (X : Type u) : KernelExtensionLaw (fun _ _ : X => (0 : ℂ)) := by
  intro n L h
  refine ⟨0, 0, ?_⟩
  simp [finiteGram, residualExtension]

namespace Finite

def actual : Realization signature :=
  realize signature (fun _ X K => ∀ (n : ℕ) (L : Fin n → X), (finiteGram K L).PosSemidef) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {X : Type u} (K : X → X → ℂ),
    KernelExtensionLaw K → R.readout () X K

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (fun _ _ : ULift.{u} Unit => (0 : ℂ)) (zero_law _)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨ULift.{u} Unit, (fun _ _ => 0), (fun _ _ => -1), ?_⟩
  intro he
  have hz := extensionLaw_finiteGram_posSemidef (fun _ _ : ULift.{u} Unit => (0 : ℂ)) (zero_law _)
  have hn := Eq.mp he hz
  have hd := (hn 1 (fun _ => ⟨()⟩)).diag_nonneg (i := 0)
  norm_num [finiteGram] at hd

def source_registration : Registration arena (type_of% @extensionLaw_finiteGram_posSemidef.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@extensionLaw_finiteGram_posSemidef.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration
    (@extensionLaw_finiteGram_posSemidef.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.Quantum.Completion.HistoryKernelExtension.extensionLaw_finiteGram_posSemidef.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Completion.HistoryKernelExtension.Finite.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ X K => ∀ (n : ℕ) (L : Fin n → X), (finiteGram K L).PosSemidef) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Completion.HistoryKernelExtension
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body"]
      stateBinder := 1
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Finite

namespace Kernel

def actual : Realization signature :=
  realize signature (fun _ X K => (Matrix.of K).PosSemidef) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {X : Type u} (K : X → X → ℂ),
    KernelExtensionLaw K → R.readout () X K

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (fun _ _ : ULift.{u} Unit => (0 : ℂ)) (zero_law _)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨ULift.{u} Unit, (fun _ _ => 0), (fun _ _ => -1), ?_⟩
  intro he
  have hz := extensionLaw_kernel_posSemidef (fun _ _ : ULift.{u} Unit => (0 : ℂ)) (zero_law _)
  have hn := Eq.mp he hz
  have hd := hn.diag_nonneg (i := ⟨()⟩)
  norm_num [finiteGram] at hd

def source_registration : Registration arena (type_of% @extensionLaw_kernel_posSemidef.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@extensionLaw_kernel_posSemidef.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration
    (@extensionLaw_kernel_posSemidef.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.Quantum.Completion.HistoryKernelExtension.extensionLaw_kernel_posSemidef.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Completion.HistoryKernelExtension.Kernel.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ X K => (Matrix.of K).PosSemidef) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Completion.HistoryKernelExtension
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body"]
      stateBinder := 1
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Kernel

end Reg.D5.S3.Quantum.Completion.HistoryKernelExtension
