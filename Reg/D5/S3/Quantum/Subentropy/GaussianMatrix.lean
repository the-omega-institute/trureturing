import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Subentropy.GaussianMatrix
import Reg.Support.SingleDependentReadout

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Matrix
open _root_.D5.S3.Quantum.Subentropy.Basic
open _root_.D5.S3.Quantum.Subentropy.GaussianMatrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.Quantum.Subentropy.GaussianQuadratic
open scoped BigOperators ComplexOrder MatrixOrder

namespace Reg.D5.S3.Quantum.Subentropy.GaussianMatrix
universe u
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => Real.negMulLog x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => Real.negMulLog x + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.PosSemidef) (htr : A.trace = 1) (i₀ : ι),
    Integrable (fun z => Real.negMulLog (gaussianQuadratic A z))
      (stdGaussian (EuclideanSpace ℂ ι)) ∧
    matrixSubentropy A =
      (∫ z, R.readout () () (gaussianQuadratic A z)
        ∂stdGaussian (EuclideanSpace ℂ ι)) -
      (∫ z : (ι × Fin 2) → ℝ,
        Real.negMulLog (((z (i₀,0))^2 + (z (i₀,1))^2)/2)
        ∂Measure.pi (fun _ : ι × Fin 2 => gaussianReal 0 1))
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let i₀ : ULift.{u} Unit := ⟨()⟩
  have hp : (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ).PosSemidef :=
    Matrix.PosSemidef.one
  have ht : (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ).trace = 1 := by simp
  have hb := (@h (ULift.{u} Unit) inferInstance inferInstance 1 hp ht i₀).2
  have ha := matrix_subentropy_gaussian_entropy 1 hp ht i₀
  simp only [rejected, realize] at hb
  rw [integral_add ha.1 (integrable_const (1 : ℝ))] at hb
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hb
  linarith [ha.2]
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, Real.exp 1, ?_⟩
  simp [actual, realize, Real.negMulLog, (Real.exp_pos 1).ne']
def source_registration : Registration arena.{u} (type_of% @matrix_subentropy_gaussian_entropy.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@matrix_subentropy_gaussian_entropy, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@matrix_subentropy_gaussian_entropy.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Subentropy.GaussianMatrix.matrix_subentropy_gaussian_entropy.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.GaussianMatrix.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.negMulLog x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.GaussianMatrix
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Subentropy.GaussianMatrix
