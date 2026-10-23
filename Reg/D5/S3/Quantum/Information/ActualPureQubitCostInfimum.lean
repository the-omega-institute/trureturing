import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.ActualPureQubitCostInfimum
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Information.ActualPureQubitCostInfimum
open _root_.D5.S3.Quantum.Information.ActualPureQubitCostInfimum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MatrixEnergy

/-- Observe the Bloch vector of the Hermitian matrix in the energy identity. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Matrix (Fin 2) (Fin 2) ℂ) (fun _ => EuclideanSpace ℝ (Fin 3))

def actual : Realization signature :=
  realize signature (fun _ _ M => bloch M) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M : Matrix (Fin 2) (Fin 2) ℂ), M.IsHermitian →
    2 * (Matrix.trace (M * M)).re = (Matrix.trace M).re ^ 2 + ‖R.readout () () M‖ ^ 2

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hM : (!![(1 : ℂ), 0; 0, 0]).IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.conjTranspose_apply]
  have he := h _ hM
  norm_num [rejected, realize, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two] at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, !![(1 : ℂ), 0; 0, 0], ?_⟩
  change bloch 0 ≠ bloch !![(1 : ℂ), 0; 0, 0]
  intro he
  have hc := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) he
  norm_num [bloch, Matrix.cons_val_two] at hc

def source_registration : Registration arena (type_of% @matrix_energy) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨matrix_energy, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@matrix_energy) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.ActualPureQubitCostInfimum.MatrixEnergy.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Information.ActualPureQubitCostInfimum.MatrixEnergy.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ M => bloch M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.ActualPureQubitCostInfimum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end MatrixEnergy

end
end Reg.D5.S3.Quantum.Information.ActualPureQubitCostInfimum
