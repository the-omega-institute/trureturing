/- GID: D5/S3/Weil/Budget/CirclePrimalEquivalence
   generality: G
   mirror-B: D5/B/S3/Weil/Budget/CirclePrimalEquivalence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The circle primal equals the maximal Haar floor and its residual formulation. -/

import D5.S3.Weil.Budget.FullCirclePrimalAttainment

/- Library-search and duplicate audit trail (2026-09-03):
   * Literal, notation-variant, digestion-receipt, digest, generalized-theorem, and
     in-flight-lane searches found no formalization of atom ba3d2170....
   * `FullCirclePrimalAttainment.full_circle_primal_attainment` proves the adjacent
     attainment theorem but does not state the residual primal equivalence.
   * Pinned Mathlib supplies `IsGreatest.csSup_eq`, `Measure.sub_add_cancel_of_le`,
     `integral_add_measure`, and `integral_smul_nnreal_measure`; no theorem packages
     the circle primal equivalence itself. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
open D5.S3.Weil.Budget.FullCirclePrimalAttainment

namespace D5.S3.Weil.Budget.CirclePrimalEquivalence

noncomputable local instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle
local instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

/-- A positive finite circle measure satisfying the budget and all prescribed moments. -/
def feasibleMeasure {iota : Type*}
    (moment : iota → C(Circle, ℝ))
    (target : iota → ℝ)
    (budget : ℝ≥0)
    (measure : FiniteMeasure Circle) : Prop :=
  measure.mass ≤ budget ∧
    ∀ i, ∫ z, moment i z ∂(measure : Measure Circle) = target i

/-- `alpha` is a normalized-Haar coefficient dominated by `measure`. -/
def dominatedHaarCoefficient (measure : FiniteMeasure Circle) (alpha : ℝ≥0) : Prop :=
  (((alpha • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) ≤
    (measure : Measure Circle))

/-- The largest normalized-Haar coefficient dominated by a finite circle measure. -/
noncomputable def haarFloor (measure : FiniteMeasure Circle) : ℝ≥0 :=
  sSup {alpha : ℝ≥0 | dominatedHaarCoefficient measure alpha}

/-- A Haar coefficient dominated by at least one feasible circle measure. -/
def floorFeasible {iota : Type*}
    (moment : iota → C(Circle, ℝ))
    (target : iota → ℝ)
    (budget : ℝ≥0)
    (alpha : ℝ≥0) : Prop :=
  ∃ measure : FiniteMeasure Circle,
    feasibleMeasure moment target budget measure ∧
      dominatedHaarCoefficient measure alpha

/-- The explicit residual form after writing `measure = alpha • m_T + sigma`. -/
def residualFeasible {iota : Type*}
    (a : ℝ)
    (center : iota → ℝ)
    (moment : iota → C(Circle, ℝ))
    (target : iota → ℝ)
    (budget : ℝ≥0)
    (alpha : ℝ≥0)
    (sigma : FiniteMeasure Circle) : Prop :=
  alpha + sigma.mass ≤ budget ∧
    ∀ i, 2 * a * (alpha : ℝ) * center i +
      ∫ z, moment i z ∂(sigma : Measure Circle) = target i

/-- The circle primal objective: maximize the scaled Haar floor over feasible measures. -/
noncomputable def circlePrimalValue {iota : Type*}
    (a : ℝ)
    (moment : iota → C(Circle, ℝ))
    (target : iota → ℝ)
    (budget : ℝ≥0) : ℝ :=
  sSup ((fun measure : FiniteMeasure Circle => 2 * a * (haarFloor measure : ℝ)) ''
    {measure | feasibleMeasure moment target budget measure})

private theorem floor_feasible_iff_residual
    {iota : Type*}
    (a : ℝ)
    (center : iota → ℝ)
    (moment : iota → C(Circle, ℝ))
    (target : iota → ℝ)
    (budget : ℝ≥0)
    (haarMoment : ∀ i,
      ∫ z, moment i z ∂(normalizedCircleHaar : Measure Circle) = 2 * a * center i)
    (alpha : ℝ≥0) :
    floorFeasible moment target budget alpha ↔
      ∃ sigma : FiniteMeasure Circle,
        residualFeasible a center moment target budget alpha sigma := by
  constructor
  · rintro ⟨measure, hmeasure, domination⟩
    let floorMeasure : FiniteMeasure Circle := alpha • normalizedCircleHaar
    let sigma : FiniteMeasure Circle :=
      ⟨(measure : Measure Circle) - (floorMeasure : Measure Circle), inferInstance⟩
    have decomposition : floorMeasure + sigma = measure := by
      apply FiniteMeasure.toMeasure_injective
      change (floorMeasure : Measure Circle) +
          ((measure : Measure Circle) - (floorMeasure : Measure Circle)) =
        (measure : Measure Circle)
      rw [add_comm, Measure.sub_add_cancel_of_le domination]
    have floorMass : floorMeasure.mass = alpha := by
      dsimp only [floorMeasure]
      rw [FiniteMeasure.mass, FiniteMeasure.smul_apply]
      change alpha * normalizedCircleHaar.mass = alpha
      rw [normalizedCircleHaar_mass, mul_one]
    have massDecomposition : floorMeasure.mass + sigma.mass = measure.mass := by
      simpa only [FiniteMeasure.mass, FiniteMeasure.coeFn_add, Pi.add_apply] using
        congrArg FiniteMeasure.mass decomposition
    refine ⟨sigma, ?_, ?_⟩
    · rw [← floorMass]
      exact massDecomposition.le.trans hmeasure.1
    · intro i
      have integrableMoment (nu : FiniteMeasure Circle) :
          Integrable (fun z => moment i z) (nu : Measure Circle) := by
        simpa using (moment i).continuous.continuousOn.integrableOn_compact
          (μ := (nu : Measure Circle)) isCompact_univ
      calc
        2 * a * (alpha : ℝ) * center i +
              ∫ z, moment i z ∂(sigma : Measure Circle) =
            (alpha : ℝ) *
                (∫ z, moment i z ∂(normalizedCircleHaar : Measure Circle)) +
              ∫ z, moment i z ∂(sigma : Measure Circle) := by
                rw [haarMoment i]
                ring
        _ = ∫ z, moment i z ∂(floorMeasure : Measure Circle) +
              ∫ z, moment i z ∂(sigma : Measure Circle) := by
                dsimp only [floorMeasure]
                rw [FiniteMeasure.toMeasure_smul, integral_smul_nnreal_measure]
                rfl
        _ = ∫ z, moment i z ∂((floorMeasure + sigma : FiniteMeasure Circle) :
              Measure Circle) := by
                rw [FiniteMeasure.toMeasure_add]
                exact (integral_add_measure (integrableMoment floorMeasure)
                  (integrableMoment sigma)).symm
        _ = target i := by
              rw [congrArg FiniteMeasure.toMeasure decomposition]
              exact hmeasure.2 i
  · rintro ⟨sigma, hbudget, hmoments⟩
    let measure : FiniteMeasure Circle := alpha • normalizedCircleHaar + sigma
    have floorMass : (alpha • normalizedCircleHaar).mass = alpha := by
      rw [FiniteMeasure.mass, FiniteMeasure.smul_apply]
      change alpha * normalizedCircleHaar.mass = alpha
      rw [normalizedCircleHaar_mass, mul_one]
    refine ⟨measure, ⟨?_, ?_⟩, ?_⟩
    · calc
        measure.mass = (alpha • normalizedCircleHaar).mass + sigma.mass := by
          simp only [measure, FiniteMeasure.mass, FiniteMeasure.coeFn_add, Pi.add_apply]
        _ = alpha + sigma.mass := by rw [floorMass]
        _ ≤ budget := hbudget
    · intro i
      have integrableMoment (nu : FiniteMeasure Circle) :
          Integrable (fun z => moment i z) (nu : Measure Circle) := by
        simpa using (moment i).continuous.continuousOn.integrableOn_compact
          (μ := (nu : Measure Circle)) isCompact_univ
      calc
        ∫ z, moment i z ∂(measure : Measure Circle) =
            ∫ z, moment i z
                ∂((alpha • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) +
              ∫ z, moment i z ∂(sigma : Measure Circle) := by
                dsimp only [measure]
                rw [FiniteMeasure.toMeasure_add]
                exact integral_add_measure
                  (integrableMoment (alpha • normalizedCircleHaar)) (integrableMoment sigma)
        _ = (alpha : ℝ) *
                (∫ z, moment i z ∂(normalizedCircleHaar : Measure Circle)) +
              ∫ z, moment i z ∂(sigma : Measure Circle) := by
                rw [FiniteMeasure.toMeasure_smul, integral_smul_nnreal_measure]
                rfl
        _ = 2 * a * (alpha : ℝ) * center i +
              ∫ z, moment i z ∂(sigma : Measure Circle) := by
                rw [haarMoment i]
                ring
        _ = target i := hmoments i
    · change
        (((alpha • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) ≤
          ((alpha • normalizedCircleHaar + sigma : FiniteMeasure Circle) : Measure Circle))
      simpa using Measure.le_add_right (le_refl
        (((alpha • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle)))

/-- For positive scale `a`, the circle primal is twice `a` times the attained maximal
Haar floor. The same maximizer is the largest coefficient in the explicit nonnegative
residual formulation, whose budget and moment equations are displayed pointwise. -/
theorem circle_primal_equivalence
    {iota : Type*}
    (a : ℝ)
    (center : iota → ℝ)
    (moment : iota → C(Circle, ℝ))
    (target : iota → ℝ)
    (budget : ℝ≥0)
    (ha : 0 < a)
    (haarMoment : ∀ i,
      ∫ z, moment i z ∂(normalizedCircleHaar : Measure Circle) = 2 * a * center i)
    (hfeasible : ∃ measure : FiniteMeasure Circle,
      feasibleMeasure moment target budget measure) :
    ∃ (measure : FiniteMeasure Circle) (alpha : ℝ≥0),
      feasibleMeasure moment target budget measure ∧
      dominatedHaarCoefficient measure alpha ∧
      haarFloor measure = alpha ∧
      IsGreatest
        (haarFloor '' {nu | feasibleMeasure moment target budget nu}) alpha ∧
      IsGreatest {beta | floorFeasible moment target budget beta} alpha ∧
      circlePrimalValue a moment target budget = 2 * a * (alpha : ℝ) ∧
      circlePrimalValue a moment target budget / (2 * a) = (alpha : ℝ) ∧
      ∀ beta : ℝ≥0,
        floorFeasible moment target budget beta ↔
          ∃ sigma : FiniteMeasure Circle,
            residualFeasible a center moment target budget beta sigma := by
  obtain ⟨measure, hbudget, hmoments, alpha, domination, maximal⟩ :=
    full_circle_primal_attainment moment target budget (by
      simpa only [feasibleMeasure] using hfeasible)
  have measureFeasible : feasibleMeasure moment target budget measure :=
    ⟨hbudget, hmoments⟩
  have coefficientGreatest :
      IsGreatest {beta : ℝ≥0 | dominatedHaarCoefficient measure beta} alpha := by
    refine ⟨domination, ?_⟩
    intro beta hbeta
    exact maximal measure hbudget hmoments beta hbeta
  have floorEquality : haarFloor measure = alpha := coefficientGreatest.csSup_eq
  have floorGreatest :
      IsGreatest
        (haarFloor '' {nu | feasibleMeasure moment target budget nu}) alpha := by
    refine ⟨⟨measure, measureFeasible, floorEquality⟩, ?_⟩
    rintro _ ⟨nu, hnu, rfl⟩
    apply csSup_le
    · refine ⟨0, ?_⟩
      change dominatedHaarCoefficient nu 0
      unfold dominatedHaarCoefficient
      simpa only [zero_smul, FiniteMeasure.toMeasure_zero] using
        Measure.zero_le (nu : Measure Circle)
    · intro beta hbeta
      exact maximal nu hnu.1 hnu.2 beta hbeta
  have explicitGreatest :
      IsGreatest {beta : ℝ≥0 | floorFeasible moment target budget beta} alpha := by
    refine ⟨⟨measure, measureFeasible, domination⟩, ?_⟩
    rintro beta ⟨nu, hnu, hbeta⟩
    exact maximal nu hnu.1 hnu.2 beta hbeta
  have primalGreatest :
      IsGreatest
        ((fun nu : FiniteMeasure Circle => 2 * a * (haarFloor nu : ℝ)) ''
          {nu | feasibleMeasure moment target budget nu})
        (2 * a * (alpha : ℝ)) := by
    refine ⟨⟨measure, measureFeasible, ?_⟩, ?_⟩
    · change 2 * a * (haarFloor measure : ℝ) = 2 * a * (alpha : ℝ)
      rw [floorEquality]
    rintro _ ⟨nu, hnu, rfl⟩
    apply mul_le_mul_of_nonneg_left
    · exact_mod_cast floorGreatest.2 ⟨nu, hnu, rfl⟩
    · positivity
  have primalEquality :
      circlePrimalValue a moment target budget = 2 * a * (alpha : ℝ) := by
    exact primalGreatest.csSup_eq
  refine ⟨measure, alpha, measureFeasible, domination, floorEquality, floorGreatest,
    explicitGreatest, primalEquality, ?_, ?_⟩
  · rw [primalEquality]
    exact mul_div_cancel_left₀ (alpha : ℝ) (mul_ne_zero (by norm_num) ha.ne')
  · intro beta
    exact floor_feasible_iff_residual a center moment target budget haarMoment beta

#print axioms circle_primal_equivalence

end D5.S3.Weil.Budget.CirclePrimalEquivalence
