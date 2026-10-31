import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.ExponentialKernel.InverseQuadraticForm
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Entanglement.ExponentialKernel.InverseQuadraticForm

open _root_.D5.S3.Quantum.Entanglement.ExponentialSectorKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (ℕ × (ℕ → ℝ))
    (fun p => Fin (p.1 + 1) → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p x =>
    x ⬝ᵥ ((fun i j : Fin (p.1 + 1) => kernel p.2 i j)⁻¹ *ᵥ x))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p x => actual.readout () p x + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (loss : ℕ → ℝ),
    (∀ i < n, loss i < loss (i + 1)) →
    let K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun i j => kernel loss i j
    K.det ≠ 0 ∧ K * K⁻¹ = 1 ∧
      ∀ x : Fin (n + 1) → ℝ,
        R.readout () (n, loss) x = x 0 ^ 2 +
          ∑ i : Fin n, (x i.succ - edge loss i * x i.castSucc) ^ 2 /
            (1 - edge loss i ^ 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := (h 0 (fun _ => 0) (by intro i hi; omega)).2.2 (fun _ => 0)
  norm_num [rejected, actual, realize, Matrix.mulVec, dotProduct] at hz

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(0, fun _ => 0), (fun _ => 0), (fun _ => 1), ?_⟩
  have hK : (fun i j : Fin 1 => kernel (fun _ => 0) i j) =
      (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    simp [kernel, Fin.eq_zero i, Fin.eq_zero j]
  simp [actual, realize, hK, dotProduct]

def source_registration : Registration arena (type_of% @inverse_quadratic_form) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨inverse_quadratic_form, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@inverse_quadratic_form) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.ExponentialKernel.InverseQuadraticForm.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.ExponentialKernel.InverseQuadraticForm.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x =>
    x ⬝ᵥ ((fun i j : Fin (p.1 + 1) => kernel p.2 i j)⁻¹ *ᵥ x))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.ExponentialKernel.InverseQuadraticForm
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Entanglement.ExponentialKernel.InverseQuadraticForm
