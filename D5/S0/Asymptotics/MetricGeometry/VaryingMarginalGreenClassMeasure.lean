/- GID: D5/S0/Asymptotics/MetricGeometry/VaryingMarginalGreenClassMeasure
   generality: G
   mirror-B: D5/B/S0/Asymptotics/MetricGeometry/VaryingMarginalGreenClassMeasure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: For arbitrary probability marginals mu_i on a measurable alphabet, a finite-support green class has product mass equal to the product of its pinned singleton masses, and this mass is positive exactly when every pinned singleton mass is positive. For a finite nontrivial discrete alphabet, coordinatewise comparison with the inverse alphabet size gives the corresponding comparison with critical Hausdorff measure through its frozen equality with uniform string measure. -/

import D5.S0.Asymptotics.MetricGeometry.GreenClassHausdorffDimension

open MeasureTheory Measure
open scoped ENNReal Topology

namespace D5.S0.Asymptotics.MetricGeometry.VaryingMarginalGreenClassMeasure

open D5.S0.Naming.GreenClassMeasure
open D5.S0.Asymptotics.MetricGeometry.GreenClassHausdorffDimension

noncomputable section

attribute [local instance] PiNat.metricSpace PiNat.boundedSpace Pi.borelSpace

/-- A green class under varying probability marginals has the product of its pinned masses. -/
theorem varying_greenClass_measure {O : Type*} [MeasurableSpace O]
    [MeasurableSingletonClass O] (μ : ℕ → Measure O)
    [∀ i, IsProbabilityMeasure (μ i)] (S : Finset ℕ) (t : ℕ → O) :
    (Measure.infinitePi μ) (greenClass S t) = ∏ i ∈ S, μ i {t i} := by
  rw [greenClass, Measure.infinitePi_pi μ (fun i _ => measurableSet_singleton (t i))]

/-- A varying-marginal green class has positive mass exactly when every pinned mass is positive. -/
theorem varying_greenClass_measure_pos_iff {O : Type*} [MeasurableSpace O]
    [MeasurableSingletonClass O] (μ : ℕ → Measure O)
    [∀ i, IsProbabilityMeasure (μ i)] (S : Finset ℕ) (t : ℕ → O) :
    0 < (Measure.infinitePi μ) (greenClass S t) ↔ ∀ i ∈ S, 0 < μ i {t i} := by
  rw [varying_greenClass_measure, CanonicallyOrderedAdd.prod_pos]

/-- Upper bounds by uniform singleton mass give mass at most critical Hausdorff measure. -/
theorem varying_greenClass_measure_le_hausdorffMeasure {O : Type*} [Fintype O]
    [Nonempty O] [Nontrivial O] [MeasurableSpace O] [MeasurableSingletonClass O]
    [TopologicalSpace O] [DiscreteTopology O] (μ : ℕ → Measure O)
    [∀ i, IsProbabilityMeasure (μ i)] (S : Finset ℕ) (t : ℕ → O)
    (h : ∀ i ∈ S, μ i {t i} ≤ (Fintype.card O : ℝ≥0∞)⁻¹) :
    (Measure.infinitePi μ) (greenClass S t) ≤ μH[namingDim O] (greenClass S t) := by
  rw [varying_greenClass_measure, hausdorffMeasure_eq_stringMeasure, greenClass_measure,
    ← Finset.prod_const]
  exact Finset.prod_le_prod (fun _ _ => bot_le) h

/-- Lower bounds by uniform singleton mass give mass at least critical Hausdorff measure. -/
theorem hausdorffMeasure_le_varying_greenClass_measure {O : Type*} [Fintype O]
    [Nonempty O] [Nontrivial O] [MeasurableSpace O] [MeasurableSingletonClass O]
    [TopologicalSpace O] [DiscreteTopology O] (μ : ℕ → Measure O)
    [∀ i, IsProbabilityMeasure (μ i)] (S : Finset ℕ) (t : ℕ → O)
    (h : ∀ i ∈ S, (Fintype.card O : ℝ≥0∞)⁻¹ ≤ μ i {t i}) :
    μH[namingDim O] (greenClass S t) ≤ (Measure.infinitePi μ) (greenClass S t) := by
  rw [varying_greenClass_measure, hausdorffMeasure_eq_stringMeasure, greenClass_measure,
    ← Finset.prod_const]
  exact Finset.prod_le_prod (fun _ _ => bot_le) h

example {O : Type*} [MeasurableSpace O] [MeasurableSingletonClass O]
    (μ : ℕ → Measure O) [∀ i, IsProbabilityMeasure (μ i)] (t : ℕ → O) :
    (Measure.infinitePi μ) (greenClass (Finset.range 1) t) = μ 0 {t 0} := by
  simp [varying_greenClass_measure]

end

end D5.S0.Asymptotics.MetricGeometry.VaryingMarginalGreenClassMeasure
