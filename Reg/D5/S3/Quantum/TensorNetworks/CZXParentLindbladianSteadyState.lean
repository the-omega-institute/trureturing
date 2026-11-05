import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.CZXParentLindbladianSteadyState
import Reg.Support.DependentFamily

/-! Source-bound audit of the CZX steady-state normalization. -/

namespace Reg.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianSteadyState
open _root_.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianSteadyState
open _root_.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianWindowChannel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Filter
open scoped Topology

/-- Observe the normalization coefficient in the limiting matrix. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => ((2 : ℂ) ^ n)⁻¹) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, Even n → 4 ≤ n →
    Tendsto (fun t : ℝ => evolution n t (((2 : ℂ) ^ n)⁻¹ • (1 + tensorX n))) atTop
      (𝓝 (R.readout () () n •
        (1 + (2 : ℂ) ^ (1 - (n / 2 : ℕ) : ℤ) • czxUnitary n)))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 4 (by decide) (by omega)
  have htrue := result 4 (by decide) (by omega)
  have heq := tendsto_nhds_unique htrue hbad
  have hentry := congrArg (fun M : Matrix (Fin 4 → Fin 2) (Fin 4 → Fin 2) ℂ =>
    M (fun _ => 0) (fun _ => 0)) heq
  norm_num [rejected, realize, czxUnitary, cz, Matrix.diagonal_mul, tensorX,
    Matrix.one_apply, funext_iff] at hentry

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change ((2 : ℂ) ^ 0)⁻¹ ≠ ((2 : ℂ) ^ 1)⁻¹
  norm_num

def source_registration : Registration arena (claim) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

#print _root_.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianSteadyState.claim
#print axioms _root_.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianSteadyState.result

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianSteadyState.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianSteadyState.unit
  realizationName :=
    `Reg.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianSteadyState.source_registration
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
    (realize signature (fun _ _ n => ((2 : ℂ) ^ n)⁻¹) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.CZXParentLindbladianSteadyState
    definition := some {
      owner := `D5.S3.Quantum.TensorNetworks.CZXParentLindbladianSteadyState
      name := `D5.S3.Quantum.TensorNetworks.CZXParentLindbladianSteadyState.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianSteadyState
