import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.MultivariateEnergy.Energy
import Reg.Support.DependentFamily

noncomputable section
namespace Reg.D5.S3.Analytic.MultivariateEnergy.Energy
open _root_.D5.S3.Analytic.MultivariateEnergy.Defs
open _root_.D5.S3.Analytic.MultivariateEnergy.Moments
open _root_.D5.S3.Analytic.MultivariateEnergy.Energy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

private def axis (i : Fin 2) : S 2 :=
  ⟨EuclideanSpace.single i 1, by simp [Metric.mem_sphere, dist_zero_right, EuclideanSpace.single]⟩

private lemma L_axis (i j : Fin 2) : L (axis i) (axis j) =
    (if i = j then 1 else 0) - 1 / 2 := by
  rw [L_eq]
  simp [axis, EuclideanSpace.inner_single_left, EuclideanSpace.single, PiLp.single_apply]

abbrev coefficientSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def energyActual : Realization coefficientSignature :=
  realize coefficientSignature (fun _ _ b => b) (fun e => nomatch e)

def energyRejected : Realization coefficientSignature :=
  realize coefficientSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev energyArena : Arena where
  signature := coefficientSignature
  Law R := ∀ (d : ℕ) (β : ℝ) (μ : Measure (S d)) [IsProbabilityMeasure μ],
    energy (familyKernel d 0 β) μ = R.readout () () β * trace (Q μ * Q μ) -
      trace (Q μ * Q μ * Q μ)

private theorem energyRejected_false : ¬ energyArena.Law energyRejected := by
  intro h
  have hh := h 2 1 (Measure.dirac (axis 0))
  rw [energy_family_eq] at hh
  have hQ : Q (Measure.dirac (axis 0)) = A (axis 0) := integral_dirac A _
  simp only [energyRejected, realize, hQ, one_mul, zero_mul] at hh
  have hL : trace (A (axis 0) * A (axis 0)) = 1 / 2 := by
    change L (axis 0) (axis 0) = 1 / 2
    have hl := L_axis 0 0
    norm_num at hl
    exact hl
  linarith

private theorem energyDependence :
    ObservationalDependence coefficientSignature energyActual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [energyActual, realize]⟩

def energySource : Registration energyArena (type_of% @energy_family_eq) where
  actual := energyActual
  bridge := Iff.rfl
  variation := ⟨energy_family_eq, energyRejected, energyRejected_false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨energyRejected, ?_, rfl, energyRejected_false⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := energyDependence

def energyAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@energy_family_eq) (Realization coefficientSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.MultivariateEnergy.Energy.energyAuditUnit
  realizationName := `Reg.D5.S3.Analytic.MultivariateEnergy.Energy.energySource
  realizationSource := none
  generated := false
  arena := .source ⟨energyArena⟩
  objectArena := .source ⟨energyArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source energyArena ⟨energySource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coefficientSignature (fun _ _ b => b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.MultivariateEnergy.Energy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def averagedActual : Realization coefficientSignature :=
  realize coefficientSignature (fun _ _ b => b / 3) (fun e => nomatch e)

def averagedRejected : Realization coefficientSignature :=
  realize coefficientSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev averagedArena : Arena where
  signature := coefficientSignature
  Law R := ∀ (d : ℕ) [NeZero d] (β : ℝ) (x y : S d),
    avgKernel (familyKernel d 0 β) x y = R.readout () () β * L x y

private theorem averagedRejected_false : ¬ averagedArena.Law averagedRejected := by
  intro h
  have hh := h 2 3 (axis 0) (axis 0)
  rw [avgKernel_family_eq, L_axis] at hh
  norm_num [averagedRejected, realize] at hh

private theorem averagedDependence :
    ObservationalDependence coefficientSignature averagedActual := by
  intro i
  exact ⟨(), 0, 3, by norm_num [averagedActual, realize]⟩

def averagedSource : Registration averagedArena (type_of% @avgKernel_family_eq) where
  actual := averagedActual
  bridge := Iff.rfl
  variation := ⟨avgKernel_family_eq, averagedRejected, averagedRejected_false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨averagedRejected, ?_, rfl, averagedRejected_false⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := averagedDependence

def averagedAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@avgKernel_family_eq) (Realization coefficientSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.MultivariateEnergy.Energy.averagedAuditUnit
  realizationName := `Reg.D5.S3.Analytic.MultivariateEnergy.Energy.averagedSource
  realizationSource := none
  generated := false
  arena := .source ⟨averagedArena⟩
  objectArena := .source ⟨averagedArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source averagedArena ⟨averagedSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coefficientSignature (fun _ _ b => b / 3) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.MultivariateEnergy.Energy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def positiveActual : Realization coefficientSignature :=
  realize coefficientSignature (fun _ _ b => b) (fun e => nomatch e)

def positiveRejected : Realization coefficientSignature :=
  realize coefficientSignature (fun _ _ b => -b) (fun e => nomatch e)

abbrev positiveArena : Arena where
  signature := coefficientSignature
  Law R := ∀ (d : ℕ) [NeZero d] (β : ℝ), 0 ≤ β →
    IsCondPosDef (avgKernel (familyKernel d 0 (R.readout () () β)))

private theorem positiveRejected_false : ¬ positiveArena.Law positiveRejected := by
  intro h
  have hh := h 2 3 (by norm_num)
  have hc := hh (Measure.dirac (axis 0)) (Measure.dirac (axis 1))
    inferInstance inferInstance (by simp)
  simp only [positiveRejected, realize] at hc
  simp only [avgKernel_family_eq, integral_dirac, L_axis] at hc
  norm_num at hc

private theorem positiveDependence :
    ObservationalDependence coefficientSignature positiveActual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [positiveActual, realize]⟩

def positiveSource : Registration positiveArena (type_of% @isCondPosDef_family) where
  actual := positiveActual
  bridge := Iff.rfl
  variation := ⟨isCondPosDef_family, positiveRejected, positiveRejected_false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨positiveRejected, ?_, rfl, positiveRejected_false⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := positiveDependence

def positiveAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@isCondPosDef_family) (Realization coefficientSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.MultivariateEnergy.Energy.positiveAuditUnit
  realizationName := `Reg.D5.S3.Analytic.MultivariateEnergy.Energy.positiveSource
  realizationSource := none
  generated := false
  arena := .source ⟨positiveArena⟩
  objectArena := .source ⟨positiveArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source positiveArena ⟨positiveSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coefficientSignature (fun _ _ b => b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.MultivariateEnergy.Energy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.MultivariateEnergy.Energy
