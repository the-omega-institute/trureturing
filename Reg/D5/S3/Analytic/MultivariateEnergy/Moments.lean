import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.MultivariateEnergy.Moments
import Reg.Support.DependentFamily

noncomputable section
namespace Reg.D5.S3.Analytic.MultivariateEnergy.Moments
open _root_.D5.S3.Analytic.MultivariateEnergy.Defs
open _root_.D5.S3.Analytic.MultivariateEnergy.Moments
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory

abbrev covarianceSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def covarianceActual : Realization covarianceSignature :=
  realize covarianceSignature (fun _ _ d => 1 / (d : ℝ)) (fun e => nomatch e)

def covarianceRejected : Realization covarianceSignature :=
  realize covarianceSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev covarianceArena : Arena where
  signature := covarianceSignature
  Law R := ∀ (d : ℕ) [NeZero d] (i j : Fin d),
    (∫ x : S d, x.val i * x.val j ∂sigma d) =
      if i = j then R.readout () () d else 0

private theorem covarianceRejected_false : ¬ covarianceArena.Law covarianceRejected := by
  intro h
  have he := @h 1 inferInstance 0 0
  rw [integral_coord_mul_coord] at he
  norm_num [covarianceRejected, realize] at he

private theorem covarianceDependence :
    ObservationalDependence covarianceSignature covarianceActual := by
  intro i
  exact ⟨(), 1, 2, by norm_num [covarianceActual, realize]⟩

def covarianceSource : Registration covarianceArena (type_of% @integral_coord_mul_coord) where
  actual := covarianceActual
  bridge := Iff.rfl
  variation := ⟨integral_coord_mul_coord, covarianceRejected, covarianceRejected_false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨covarianceRejected, ?_, rfl, covarianceRejected_false⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := covarianceDependence

def covarianceAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integral_coord_mul_coord) (Realization covarianceSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.MultivariateEnergy.Moments.covarianceAuditUnit
  realizationName := `Reg.D5.S3.Analytic.MultivariateEnergy.Moments.covarianceSource
  realizationSource := none
  generated := false
  arena := .source ⟨covarianceArena⟩
  objectArena := .source ⟨covarianceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source covarianceArena ⟨covarianceSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize covarianceSignature (fun _ _ d => 1 / (d : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.MultivariateEnergy.Moments
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.MultivariateEnergy.Moments
