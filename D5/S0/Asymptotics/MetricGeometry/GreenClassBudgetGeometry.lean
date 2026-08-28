/- GID: D5/S0/Asymptotics/MetricGeometry/GreenClassBudgetGeometry
   generality: G
   mirror-B: D5/B/S0/Asymptotics/MetricGeometry/GreenClassBudgetGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Green-class measure depends only on test budget, while prefix-metric diameter depends sharply on the first untested coordinate and is minimized exactly by gapless prefix support. -/

import D5.S0.Asymptotics.MetricGeometry.GreenClassDiameter

/- Library-search audit trail (2026-08-26):
   * Exact current-tree searches for a public theorem combining uniform
     Green-class measure with first-hole diameter and prefix extremality missed.
   * `GreenClassMeasure.greenClass`, `stringMeasure`, and `greenClass_measure`
     are the canonical source-carrier primitives for the volume clause.
   * `GreenClassDiameter.green_class_diameter` and
     `prefix_support_minimizes_diameter` are exact D5 hits for the metric clauses
     and are imported and applied directly.
   * Pinned Mathlib searches for a theorem combining infinite-product cylinder
     measure with `PiNat` diameter missed; Mathlib supplies the component APIs
     already used by the imported frozen owners. No definition is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Asymptotics.MetricGeometry.GreenClassBudgetGeometry

open MeasureTheory
open scoped ENNReal

open D5.S0.Asymptotics.MetricGeometry.GreenClassDiameter
open D5.S0.Naming.FirstHoleBound
open D5.S0.Naming.GreenClassMeasure

attribute [local instance] PiNat.metricSpace PiNat.boundedSpace

noncomputable section

/-- For a finite nontrivial alphabet, the uniform-product volume of a Green
class depends only on the number of tested coordinates, whereas its exact
prefix-metric diameter is set by the first untested coordinate. Consequently,
gapless prefix support is exactly what minimizes drift at a fixed budget. -/
theorem green_class_budget_geometry
    {O : Type*} [Fintype O] [Nonempty O] [MeasurableSpace O]
    [MeasurableSingletonClass O] [TopologicalSpace O] [DiscreteTopology O]
    [Nontrivial O] (S : Finset ℕ) (t : ℕ → O) :
    stringMeasure O (greenClass S t) =
        ((Fintype.card O : ℝ≥0∞))⁻¹ ^ S.card ∧
      (∀ U : Finset ℕ, U.card = S.card →
        stringMeasure O (greenClass U t) = stringMeasure O (greenClass S t)) ∧
      Metric.diam (greenClass S t) = (1 / 2 : ℝ) ^ firstHole S ∧
      ((1 / 2 : ℝ) ^ S.card ≤ Metric.diam (greenClass S t) ∧
        (Metric.diam (greenClass S t) = (1 / 2 : ℝ) ^ S.card ↔
          S = Finset.range S.card)) := by
  refine ⟨greenClass_measure S t, ?_, green_class_diameter S t,
    prefix_support_minimizes_diameter S t⟩
  intro U sameBudget
  rw [greenClass_measure U t, greenClass_measure S t, sameBudget]

/-- `Bool` supplies a concrete source carrier satisfying every public instance
premise of `green_class_budget_geometry`. -/
example :
    letI : MeasurableSpace Bool := ⊤
    stringMeasure Bool (greenClass {0} (fun _ => false)) =
        ((Fintype.card Bool : ℝ≥0∞))⁻¹ ^ ({0} : Finset ℕ).card ∧
      Metric.diam (greenClass {0} (fun _ => false)) =
        (1 / 2 : ℝ) ^ firstHole ({0} : Finset ℕ) := by
  letI : MeasurableSpace Bool := ⊤
  exact ⟨(green_class_budget_geometry ({0} : Finset ℕ) (fun _ => false)).1,
    (green_class_budget_geometry ({0} : Finset ℕ) (fun _ => false)).2.2.1⟩

#print axioms green_class_budget_geometry

end

end D5.S0.Asymptotics.MetricGeometry.GreenClassBudgetGeometry
