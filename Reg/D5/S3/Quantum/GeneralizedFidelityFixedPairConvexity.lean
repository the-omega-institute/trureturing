import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.GeneralizedFidelityFixedPairConvexity
import Reg.Support.SingleDependentReadout

/-! # Fixed-pair convexity: dependent-family registration -/

open _root_.D5.S3.Quantum
open _root_.D5.S3.Quantum.GeneralizedFidelityFixedPairConvexity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Quantum.GeneralizedFidelityFixedPairConvexity

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

local notation "M2" => _root_.D5.S3.Quantum.FiniteDimensional.QubitMatrix

/-- Q and R remain source parameters; P ranges over actual matrices. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (M2 × M2) (fun _ => M2) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ q P => GeneralizedFidelity.bures q.2 P q.1)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ P => -((P 0 0).re ^ 2)) (fun e => nomatch e)

/-- The law retains the full public telescope and the same coefficient. -/
def arena : Arena where
  signature := signature
  Law obs := ∀ (Q R : M2) (_hQtr : Matrix.trace Q = 1) (_hR : R.PosDef),
    ConvexOn ℝ densitySet (obs.readout () (Q, R)) ↔ (coefficient R Q).PosSemidef

private def E0 : M2 := Matrix.diagonal ![1, 0]
private def E1 : M2 := Matrix.diagonal ![0, 1]

private theorem E0_psd : E0.PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num [E0]

private theorem E1_psd : E1.PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num [E1]

private theorem E0_trace : Matrix.trace E0 = 1 := by
  norm_num [E0, Matrix.trace, Fin.sum_univ_two]

private theorem E1_trace : Matrix.trace E1 = 1 := by
  norm_num [E1, Matrix.trace, Fin.sum_univ_two]

private theorem sqrt_E0 : CFC.sqrt E0 = E0 := by
  apply CFC.sqrt_unique _ E0_psd.nonneg
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [E0, Matrix.mul_apply, Fin.sum_univ_two]

private theorem sqrt_E1 : CFC.sqrt E1 = E1 := by
  apply CFC.sqrt_unique _ E1_psd.nonneg
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [E1, Matrix.mul_apply, Fin.sum_univ_two]

private theorem coefficient_one (Q : M2) : coefficient 1 Q = CFC.sqrt Q := by
  ext i j
  simp [coefficient, CFC.sqrt_one, Matrix.smul_apply, Matrix.add_apply,
    Algebra.smul_def]
  ring

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hC : (coefficient 1 E0).PosSemidef := by
    rw [coefficient_one]
    exact Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg E0)
  have hf := (h E0 1 E0_trace Matrix.PosDef.one).mpr hC
  have hm := hf.2 (show E0 ∈ densitySet from ⟨E0_psd, E0_trace⟩)
    (show E1 ∈ densitySet from ⟨E1_psd, E1_trace⟩)
    (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : 0 ≤ (1 / 2 : ℝ))
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  norm_num [rejected, realize, E0, E1, Matrix.smul_apply, Matrix.add_apply,
    Algebra.smul_def, Matrix.algebraMap_matrix_apply] at hm

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(E0, 1), E0, E1, ?_⟩
  simp only [actual, realize, GeneralizedFidelity.bures, GeneralizedFidelity.fidelity,
    CFC.sqrt_one, inv_one, one_mul, mul_one, sqrt_E0, sqrt_E1]
  norm_num [E0, E1, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]

def source_registration : Registration arena (type_of% @fixed_pair_convexity_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fixed_pair_convexity_iff, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

/-- The current compiled source material must confirm the occurrence path. -/
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@fixed_pair_convexity_iff) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.GeneralizedFidelityFixedPairConvexity.fixed_pair_convexity_iff.audit
  realizationName := `Reg.D5.S3.Quantum.GeneralizedFidelityFixedPairConvexity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ q P => GeneralizedFidelity.bures q.2 P q.1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.GeneralizedFidelityFixedPairConvexity
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.GeneralizedFidelityFixedPairConvexity
