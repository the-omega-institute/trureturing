import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.WeightedRayStochasticRigidity
import Reg.Support.SingleDependentReadout

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
open _root_.D5.S3.Quantum.Measurement.WeightedRayStochasticRigidity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Quantum.Measurement.WeightedRayStochasticRigidity

abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
abbrev Stoch := Matrix (Fin 5) (Fin 5) ℝ
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Mat) (fun _ => Fin 5 → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ ρ => probability ρ) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (U : unitaryGroup (Fin 2) ℂ) (T : Stoch),
    (T ∈ colStochastic ℝ (Fin 5) ∧
      ∀ ρ : Mat, ρ.PosSemidef → trace ρ = 1 →
        T.mulVec (R.readout () () ρ) = R.readout () () ((U : Mat) * ρ * star (U : Mat))) ↔
      (∃ γ : ℝ, (U : Mat) = Complex.exp ((γ : ℂ) * Complex.I) • 1) ∧
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1/3 ∧ T = kernel t

private def zGate : unitaryGroup (Fin 2) ℂ :=
  ⟨!![1,0;0,-1], by
    apply Matrix.mem_unitaryGroup_iff.mpr
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]⟩

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp : (1 : Stoch) ∈ colStochastic ℝ (Fin 5) := by simp
  have he := (h zGate 1).mp ⟨hp, by intros; simp [rejected, realize]⟩
  obtain ⟨γ, hγ⟩ := he.1
  have h0 := congrFun₂ hγ 0 0
  have h1 := congrFun₂ hγ 1 1
  norm_num [zGate] at h0 h1
  have hx : (1 : ℂ) = -1 := h0.trans h1.symm
  norm_num at hx

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), !![1,0;0,0], !![0,0;0,1], ?_⟩
  intro he
  have hc := congrFun he 2
  have hp : 0 < gain := by unfold gain; positivity
  norm_num [actual, realize, probability, effect,
    _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB,
    _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_formula,
    Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two] at hc
  linarith

def source_registration : Registration arena (type_of% @original_five_effect_classification) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨original_five_effect_classification, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_five_effect_classification) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Measurement.WeightedRayStochasticRigidity.original_five_effect_classification.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.WeightedRayStochasticRigidity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ ρ => probability ρ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.WeightedRayStochasticRigidity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["body", "body", "fn", "arg", "arg", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end Reg.D5.S3.Quantum.Measurement.WeightedRayStochasticRigidity
