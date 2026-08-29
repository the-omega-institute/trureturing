/- GID: D5/S3/Weil/Budget/FullCirclePrimalAttainment
   generality: G
   mirror-B: D5/B/S3/Weil/Budget/FullCirclePrimalAttainment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Feasible budgeted circle moment problems attain their maximal Haar floor. -/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Sub

/- Library-search audit trail (2026-08-29):
   * D5 and pinned-Mathlib searches found no exact circle primal-attainment theorem.
   * Body-shape searches for `haarAddCircle`, `homeomorphCircle'`, finite measures on
     `Circle`, normalized circle Haar, and Haar-floor predicates found no D5 primitive.
   * `AddCircle.haarAddCircle`, `AddCircle.homeomorphCircle'`, and
     `ProbabilityMeasure.toFiniteMeasure` construct the normalized Haar measure below.
   * `isCompact_setOf_finiteMeasure_le_of_compactSpace`, continuous finite-measure
     mass/integral evaluation, `Measure.sub_add_cancel_of_le`, and the compact extreme-value
     theorem supply the proof. -/

open scoped ENNReal NNReal
open MeasureTheory Set Topology

namespace D5.S3.Weil.Budget.FullCirclePrimalAttainment

noncomputable local instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle
local instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

/-- Normalized Haar measure on the complex unit circle, transported from the additive circle. -/
noncomputable def normalizedCircleHaar : FiniteMeasure Circle := by
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  exact FiniteMeasure.map
    (ProbabilityMeasure.toFiniteMeasure
      (⟨AddCircle.haarAddCircle, inferInstance⟩ :
        ProbabilityMeasure (AddCircle (2 * Real.pi))))
    AddCircle.homeomorphCircle'

/-- The normalized circle Haar measure has unit mass. -/
theorem normalizedCircleHaar_mass : normalizedCircleHaar.mass = 1 := by
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  rw [normalizedCircleHaar, FiniteMeasure.mass]
  rw [FiniteMeasure.map_apply _ AddCircle.homeomorphCircle'.continuous.measurable
    MeasurableSet.univ]
  exact ProbabilityMeasure.coeFn_univ
    (⟨AddCircle.haarAddCircle, inferInstance⟩ :
      ProbabilityMeasure (AddCircle (2 * Real.pi)))

/-- If a budgeted circle moment problem is feasible, one feasible measure realizes a Haar
coefficient at least as large as every Haar coefficient dominated by any feasible measure. -/
theorem full_circle_primal_attainment
    {ι : Type*}
    (moment : ι → C(Circle, ℝ))
    (target : ι → ℝ)
    (budget : ℝ≥0)
    (hfeasible : ∃ μ : FiniteMeasure Circle,
      μ.mass ≤ budget ∧
      ∀ i, ∫ z, moment i z ∂(μ : Measure Circle) = target i) :
    ∃ μ : FiniteMeasure Circle,
      μ.mass ≤ budget ∧
      (∀ i, ∫ z, moment i z ∂(μ : Measure Circle) = target i) ∧
      ∃ alpha : ℝ≥0,
        ((alpha • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) ≤
          (μ : Measure Circle) ∧
        ∀ (ν : FiniteMeasure Circle),
          ν.mass ≤ budget →
          (∀ i, ∫ z, moment i z ∂(ν : Measure Circle) = target i) →
          ∀ beta : ℝ≥0,
            ((beta • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) ≤
              (ν : Measure Circle) →
            beta ≤ alpha := by
  let reconstruction : ℝ≥0 × FiniteMeasure Circle → FiniteMeasure Circle :=
    fun p => p.1 • normalizedCircleHaar + p.2
  let compactBox : Set (ℝ≥0 × FiniteMeasure Circle) :=
    Icc 0 budget ×ˢ {sigma | sigma.mass ≤ budget}
  let constraints : Set (ℝ≥0 × FiniteMeasure Circle) :=
    {p | (reconstruction p).mass ≤ budget} ∩
      ⋂ i, {p | ∫ z, moment i z ∂((reconstruction p : FiniteMeasure Circle) : Measure Circle) =
        target i}
  let feasiblePairs := compactBox ∩ constraints
  have reconstruction_continuous : Continuous reconstruction := by
    dsimp [reconstruction]
    fun_prop
  have compact_box : IsCompact compactBox := by
    dsimp [compactBox]
    exact isCompact_Icc.prod (isCompact_setOf_finiteMeasure_le_of_compactSpace Circle budget)
  have constraints_closed : IsClosed constraints := by
    dsimp [constraints]
    apply IsClosed.inter
    · exact isClosed_Iic.preimage
        (FiniteMeasure.continuous_mass.comp reconstruction_continuous)
    · exact isClosed_iInter fun i =>
        isClosed_singleton.preimage
          ((FiniteMeasure.continuous_integral_continuousMap (moment i)).comp
            reconstruction_continuous)
  have feasible_pairs_compact : IsCompact feasiblePairs := by
    exact compact_box.inter_right constraints_closed
  have feasible_pairs_nonempty : feasiblePairs.Nonempty := by
    obtain ⟨μ, hμbudget, hμmoment⟩ := hfeasible
    refine ⟨(0, μ), ?_⟩
    refine ⟨?_, ?_⟩
    · exact ⟨⟨by simp, by exact zero_le⟩, hμbudget⟩
    · dsimp [constraints, reconstruction]
      refine ⟨by simpa using hμbudget, ?_⟩
      simp only [mem_iInter, mem_setOf_eq]
      simpa using hμmoment
  obtain ⟨p, hp, hpmax⟩ :=
    feasible_pairs_compact.exists_isMaxOn feasible_pairs_nonempty continuous_fst.continuousOn
  have hp_moments :
      ∀ i, ∫ z, moment i z ∂((reconstruction p : FiniteMeasure Circle) : Measure Circle) =
        target i := by
    simpa only [constraints, mem_iInter, mem_setOf_eq] using hp.2.2
  refine ⟨reconstruction p, hp.2.1, hp_moments, p.1, ?_, ?_⟩
  · change
      ((p.1 • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) ≤
        ((p.1 • normalizedCircleHaar + p.2 : FiniteMeasure Circle) : Measure Circle)
    simpa using Measure.le_add_right (le_refl
      (((p.1 • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle)))
  · intro ν hνbudget hνmoment beta hbeta
    let sigma : FiniteMeasure Circle :=
      ⟨(ν : Measure Circle) -
          ((beta • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle),
        inferInstance⟩
    have decomposition : beta • normalizedCircleHaar + sigma = ν := by
      apply FiniteMeasure.toMeasure_injective
      change
        ((beta • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) +
            ((ν : Measure Circle) -
              ((beta • normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle)) =
          (ν : Measure Circle)
      rw [add_comm, Measure.sub_add_cancel_of_le hbeta]
    have decomposition_measure :
        ((beta • normalizedCircleHaar + sigma : FiniteMeasure Circle) : Measure Circle) =
          (ν : Measure Circle) := congrArg FiniteMeasure.toMeasure decomposition
    have beta_mass_le : (beta • normalizedCircleHaar).mass ≤ ν.mass := by
      apply ENNReal.coe_le_coe.mp
      simpa only [FiniteMeasure.ennreal_mass] using hbeta Set.univ
    have beta_le_budget : beta ≤ budget := by
      calc
        beta = (beta • normalizedCircleHaar).mass := by
          rw [FiniteMeasure.mass, FiniteMeasure.smul_apply]
          change beta = beta * normalizedCircleHaar.mass
          rw [normalizedCircleHaar_mass, mul_one]
        _ ≤ ν.mass := beta_mass_le
        _ ≤ budget := hνbudget
    have sigma_mass_le : sigma.mass ≤ budget := by
      calc
        sigma.mass ≤ (beta • normalizedCircleHaar + sigma).mass := by
          simp only [FiniteMeasure.mass, FiniteMeasure.coeFn_add, Pi.add_apply]
          exact le_add_of_nonneg_left (by exact zero_le)
        _ = ν.mass := congrArg FiniteMeasure.mass decomposition
        _ ≤ budget := hνbudget
    apply hpmax (a := (beta, sigma))
    refine ⟨⟨⟨by exact zero_le, beta_le_budget⟩, sigma_mass_le⟩, ?_⟩
    dsimp [constraints, reconstruction]
    simp only [mem_inter_iff, mem_setOf_eq, mem_iInter]
    refine ⟨?_, ?_⟩
    · simpa only [decomposition] using hνbudget
    · have decomposition_measure' :
          (beta • ((normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle)) +
              (sigma : Measure Circle) =
            (ν : Measure Circle) := by
          simpa only [FiniteMeasure.toMeasure_add, FiniteMeasure.toMeasure_smul] using
            decomposition_measure
      rw [decomposition_measure']
      exact hνmoment

#print axioms normalizedCircleHaar_mass
#print axioms full_circle_primal_attainment

end D5.S3.Weil.Budget.FullCirclePrimalAttainment
