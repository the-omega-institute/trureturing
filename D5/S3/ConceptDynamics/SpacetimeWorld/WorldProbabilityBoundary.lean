/- GID: D5/S3/ConceptDynamics/SpacetimeWorld/WorldProbabilityBoundary
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/SpacetimeWorld/WorldProbabilityBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ConceptDynamics/SpacetimeWorld/WorldProbabilityBoundary.CartesianForcesIndependence; result=D5/S3/ConceptDynamics/SpacetimeWorld/WorldProbabilityBoundary.cartesian_probability_refutation; claim=D5/S3/ConceptDynamics/SpacetimeWorld/WorldProbabilityBoundary.CartesianForcesIndependence
   digest: A probability measure on Cartesian worlds can have dependent coordinates. -/

import D5.S3.ConceptDynamics.SpacetimeWorld.JointMarginalBoundary
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.SpacetimeWorld.WorldProbabilityBoundary

open MeasureTheory ProbabilityTheory WorldDomains JointMarginalBoundary

/-- The underlying space includes all four Cartesian worlds, including both crossed worlds. -/
def fullWorldEquiv : (Value × Value) ≃ fullModel.World :=
  pairEquiv.trans (Equiv.Set.univ JointValuation).symm

instance valueMeasurableSpace : MeasurableSpace Value := ⊤
instance worldMeasurableSpace : MeasurableSpace fullModel.World := ⊤
instance valueMeasurableSingleton : MeasurableSingletonClass Value := ⟨fun _ => trivial⟩
instance worldMeasurableSingleton : MeasurableSingletonClass fullModel.World := ⟨fun _ => trivial⟩

def leftRV : fullModel.World → Value := coordinate fullModel ⟨false, Or.inl rfl⟩
def rightRV : fullModel.World → Value := coordinate fullModel ⟨true, Or.inr rfl⟩

theorem coordinates_measurable : Measurable leftRV ∧ Measurable rightRV :=
  ⟨measurable_from_top, measurable_from_top⟩

/-- Only the measure's support is diagonal; the world domain remains the full Cartesian product. -/
def diagonalMeasure : Measure fullModel.World :=
  (1 / 2 : ENNReal) • Measure.dirac (fullWorldEquiv (oneValue, oneValue)) +
    (1 / 2 : ENNReal) • Measure.dirac (fullWorldEquiv (twoValue, twoValue))

instance diagonalMeasure_probability : IsProbabilityMeasure diagonalMeasure where
  measure_univ := by simp [diagonalMeasure, ENNReal.inv_two_add_inv_two]

open Classical in
theorem diagonalMeasure_apply (A : Set fullModel.World) :
    diagonalMeasure A =
      (if fullWorldEquiv (oneValue, oneValue) ∈ A then 1 / 2 else 0) +
        (if fullWorldEquiv (twoValue, twoValue) ∈ A then 1 / 2 else 0) := by
  classical
  simp [diagonalMeasure, Set.indicator, mul_ite]

theorem diagonal_atom_masses :
    diagonalMeasure {fullWorldEquiv (oneValue, oneValue)} = 1 / 2 ∧
      diagonalMeasure {fullWorldEquiv (twoValue, twoValue)} = 1 / 2 := by
  have unequal : oneValue ≠ twoValue := crossed_worlds_excluded.1
  have different : fullWorldEquiv (oneValue, oneValue) ≠
      fullWorldEquiv (twoValue, twoValue) :=
    fun h => unequal (congrArg Prod.fst (fullWorldEquiv.injective h))
  constructor <;> rw [diagonalMeasure_apply]
  · simp [Ne.symm different]
  · simp [different]

/-- Both values have half mass under each actual coordinate random variable. -/
theorem marginal_masses (v : Value) :
    diagonalMeasure (leftRV ⁻¹' {v}) = 1 / 2 ∧
      diagonalMeasure (rightRV ⁻¹' {v}) = 1 / 2 := by
  classical
  have unequal : oneValue ≠ twoValue := crossed_worlds_excluded.1
  constructor <;> rw [diagonalMeasure_apply]
  all_goals
    change (if oneValue = v then (1 / 2 : ENNReal) else 0) +
      (if twoValue = v then 1 / 2 else 0) = 1 / 2
    rcases v.property with hv | hv
    · have hv' : v = oneValue := Subtype.ext hv
      rw [hv']
      simp [Ne.symm unequal]
    · have hv' : v = twoValue := Subtype.ext hv
      rw [hv']
      simp [unequal]

theorem rectangle_one_eq_atom :
    leftRV ⁻¹' {oneValue} ∩ rightRV ⁻¹' {oneValue} =
      {fullWorldEquiv (oneValue, oneValue)} := by
  ext w
  obtain ⟨⟨a, b⟩, rfl⟩ := fullWorldEquiv.surjective w
  change (a = oneValue ∧ b = oneValue) ↔
    fullWorldEquiv (a, b) = fullWorldEquiv (oneValue, oneValue)
  rw [fullWorldEquiv.injective.eq_iff, Prod.mk.injEq]

theorem rectangle_masses :
    diagonalMeasure (leftRV ⁻¹' {oneValue} ∩ rightRV ⁻¹' {oneValue}) = 1 / 2 ∧
      diagonalMeasure (leftRV ⁻¹' {oneValue}) *
        diagonalMeasure (rightRV ⁻¹' {oneValue}) = 1 / 4 := by
  constructor
  · rw [rectangle_one_eq_atom]
    exact diagonal_atom_masses.1
  · rw [(marginal_masses oneValue).1, (marginal_masses oneValue).2]
    convert (ENNReal.mul_inv (a := 2) (b := 2)
      (Or.inl (by norm_num)) (Or.inr (by norm_num))).symm using 1 <;> norm_num

theorem coordinates_not_independent : ¬ IndepFun leftRV rightRV diagonalMeasure := by
  intro h
  have rectangle := h.measure_inter_preimage_eq_mul {oneValue} {oneValue}
    (measurableSet_singleton _) (measurableSet_singleton _)
  rw [rectangle_masses.1, rectangle_masses.2] at rectangle
  norm_num at rectangle

/-- A universal stronger claim on a fixed full Cartesian domain with distinct coordinate names.
No measure factorization hypothesis is present. -/
def CartesianForcesIndependence : Prop :=
  ∀ μ : Measure fullModel.World, IsProbabilityMeasure μ → IndepFun leftRV rightRV μ

theorem cartesian_probability_refutation : ¬ CartesianForcesIndependence := by
  intro h
  exact coordinates_not_independent (h diagonalMeasure diagonalMeasure_probability)

end D5.S3.ConceptDynamics.SpacetimeWorld.WorldProbabilityBoundary
