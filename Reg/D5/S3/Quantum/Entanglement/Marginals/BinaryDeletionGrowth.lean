import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionGrowth
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionGrowth

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionGrowth
open _root_.D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionDimension

noncomputable section

private abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State _ := ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun a => nomatch a)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun a => nomatch a)

private abbrev dim (k length : ℕ) : ℚ :=
  Module.finrank ℂ (SupportedKernel (NoRun (n := k + 2) length))

private abbrev dimensionArena : Arena where
  signature := signature
  Law R := ∀ k length : ℕ, 4 ≤ length →
    R.readout () ⟨k, length⟩ ((9 / 4) ^ k) (dim k length)

private abbrev ratioArena : Arena where
  signature := signature
  Law R := ∀ k length : ℕ, 4 ≤ length →
    R.readout () ⟨k, length⟩ ((9 / 8) ^ k / 4) (dim k length / allowedCount (k + 2) length)

private theorem actual_dependence (i : Unit) :
    ∃ p : signature.Params, ∃ x y : signature.State p,
      actual.readout i p x ≠ actual.readout i p y := by
  refine ⟨⟨0, 4⟩, 0, 1, ?_⟩
  intro h
  exact not_le_of_gt (by trivial : (0 : ℚ) < 1) (Eq.mp (congrFun h 0) le_rfl)

private theorem dimension_rejected : ¬ dimensionArena.Law rejected :=
  fun h => h 0 4 le_rfl

private theorem ratio_rejected : ¬ ratioArena.Law rejected :=
  fun h => h 0 4 le_rfl

def dimensionFamily : Registration dimensionArena (type_of% @kernelDimension_lower) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kernelDimension_lower, rejected, dimension_rejected⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, dimension_rejected⟩, fun a => nomatch a⟩
  dependence := actual_dependence

def ratioFamily : Registration ratioArena (type_of% @kernelDimension_to_allowedCount) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kernelDimension_to_allowedCount, rejected, ratio_rejected⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, ratio_rejected⟩, fun a => nomatch a⟩
  dependence := actual_dependence

def dimensionAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@kernelDimension_lower) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionGrowth.kernelDimension_lower.audit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionGrowth.dimensionFamily
  realizationSource := none
  generated := false
  arena := .source ⟨dimensionArena⟩
  objectArena := .source ⟨dimensionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source dimensionArena ⟨dimensionFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionGrowth
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def ratioAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@kernelDimension_to_allowedCount) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionGrowth.kernelDimension_to_allowedCount.audit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionGrowth.ratioFamily
  realizationSource := none
  generated := false
  arena := .source ⟨ratioArena⟩
  objectArena := .source ⟨ratioArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ratioArena ⟨ratioFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionGrowth
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionGrowth
