import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds
open _root_.D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
open _root_.D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace PureDeterminant

/-- Observe the squared determinant norm of the coefficient matrix. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => (Fin 2 × Fin 2) → ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ ψ => ‖(Matrix.of (Function.curry ψ)).det‖ ^ 2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ ψ : (Fin 2 × Fin 2) → ℂ,
    (partialTraceRight (rankOneDensity ψ)).det.re = R.readout () () ψ

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 0
  rw [Direct.pure_det] at he
  change ‖(0 : Matrix (Fin 2) (Fin 2) ℂ).det‖ ^ 2 = 1 at he
  norm_num at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, Function.uncurry (1 : Matrix (Fin 2) (Fin 2) ℂ), ?_⟩
  change ‖(Matrix.of (Function.curry (0 : (Fin 2 × Fin 2) → ℂ))).det‖ ^ 2 ≠
    ‖(Matrix.of (Function.curry (Function.uncurry
      (1 : Matrix (Fin 2) (Fin 2) ℂ)))).det‖ ^ 2
  norm_num [Function.curry, Function.uncurry, Matrix.det_fin_two, Matrix.one_apply]

def source_registration : Registration arena (type_of% @Direct.pure_det) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨Direct.pure_det, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@Direct.pure_det) (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.PureDeterminant.unit
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.PureDeterminant
    "source_registration"
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
    (fun _ _ ψ => ‖(Matrix.of (Function.curry ψ)).det‖ ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end PureDeterminant

namespace QubitDeterminant

/-- Observe the determinant coordinate in the upper bound for a qubit density matrix. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Matrix (Fin 2) (Fin 2) ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ τ => τ.det.re) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (τ : Matrix (Fin 2) (Fin 2) ℂ) (_hτ : τ.PosSemidef) (_ht : τ.trace = 1),
    0 ≤ τ.det.re ∧ R.readout () () τ ≤ 1 / 4

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let τ : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1, 0]
  have hp : τ.PosSemidef := Matrix.PosSemidef.diagonal (by
    intro i; fin_cases i <;> simp)
  have ht : τ.trace = 1 := by norm_num [τ, Matrix.trace_fin_two]
  have he := (h τ hp ht).2
  change (1 : ℝ) ≤ 1 / 4 at he
  norm_num at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (0 : Matrix (Fin 2) (Fin 2) ℂ).det.re ≠
    (1 : Matrix (Fin 2) (Fin 2) ℂ).det.re
  norm_num

def source_registration : Registration arena (type_of% @qubit_det_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨qubit_det_bounds, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@qubit_det_bounds) (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.QubitDeterminant.unit
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.QubitDeterminant
    "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ τ => τ.det.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end QubitDeterminant

end
end Reg.D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds
