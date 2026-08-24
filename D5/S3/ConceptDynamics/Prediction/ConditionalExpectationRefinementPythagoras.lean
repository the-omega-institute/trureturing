/- GID: D5/S3/ConceptDynamics/Prediction/ConditionalExpectationRefinementPythagoras
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Prediction/ConditionalExpectationRefinementPythagoras
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Refinement splits squared prediction risk into later risk and innovation energy. -/

import D5.S3.ConceptDynamics.Prediction.ConditionalExpectationOptimality

/- Library-search audit trail (2026-08-24):
   * The imported prediction-family module supplies the canonical Mathlib
     `condExpL2` carrier used for conditional expectations in real `L2`.
   * Pinned Mathlib searches for nested conditional-expectation Pythagoras and
     tower lemmas found no exact combined theorem.
   * Exact supporting hits in `Mathlib.Analysis.InnerProductSpace.Projection.Basic`
     are `Submodule.starProjection_inner_eq_zero` and
     `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero`; both are applied below.
   * Repository search found the generic adjacent decomposition
     `innovation_energy_recurrence`, but it exposes an abstract innovation
     subspace rather than the source's difference of conditional expectations. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Prediction.ConditionalExpectationRefinementPythagoras

open MeasureTheory
open scoped ENNReal InnerProductSpace MeasureTheory

/-- When one conditioning sigma-algebra refines another, the earlier squared
prediction risk is the later risk plus the squared `L2` distance between the
two conditional expectations. In particular, refinement cannot increase risk. -/
theorem conditional_expectation_refinement_pythagoras
    {X : Type*} [ambient : MeasurableSpace X] (mu : Measure X)
    (coarse refined : MeasurableSpace X)
    (hRefines : coarse <= refined)
    (hRefined : refined <= ambient)
    (target : Lp Real 2 mu) :
    let coarseEstimate : Lp Real 2 mu :=
      (↑(condExpL2 Real Real (m := coarse) (m0 := ambient) (μ := mu)
        (hRefines.trans hRefined) target) :
        Lp Real 2 mu)
    let refinedEstimate : Lp Real 2 mu :=
      (↑(condExpL2 Real Real (m := refined) (m0 := ambient) (μ := mu)
        hRefined target) : Lp Real 2 mu)
    (‖target - coarseEstimate‖ ^ 2 =
        ‖target - refinedEstimate‖ ^ 2 +
          ‖refinedEstimate - coarseEstimate‖ ^ 2) ∧
      ‖target - refinedEstimate‖ ^ 2 <=
        ‖target - coarseEstimate‖ ^ 2 := by
  letI : Fact (coarse <= ambient) := ⟨hRefines.trans hRefined⟩
  letI : Fact (refined <= ambient) := ⟨hRefined⟩
  let coarseSpace : Submodule Real (Lp Real 2 mu) :=
    @lpMeas X Real Real _ _ _ coarse ambient 2 mu
  let refinedSpace : Submodule Real (Lp Real 2 mu) :=
    @lpMeas X Real Real _ _ _ refined ambient 2 mu
  have hSpace : coarseSpace <= refinedSpace := by
    intro f hf
    change AEStronglyMeasurable[refined] (f : X -> Real) mu
    change AEStronglyMeasurable[coarse] (f : X -> Real) mu at hf
    exact hf.mono hRefines
  let coarseEstimate : Lp Real 2 mu :=
    (↑(condExpL2 Real Real (m := coarse) (m0 := ambient) (μ := mu)
      (hRefines.trans hRefined) target) :
      Lp Real 2 mu)
  let refinedEstimate : Lp Real 2 mu :=
    (↑(condExpL2 Real Real (m := refined) (m0 := ambient) (μ := mu)
      hRefined target) : Lp Real 2 mu)
  have hCoarseProjection :
      coarseEstimate = coarseSpace.starProjection target := rfl
  have hRefinedProjection :
      refinedEstimate = refinedSpace.starProjection target := rfl
  have hInnovationMem : refinedEstimate - coarseEstimate ∈ refinedSpace := by
    rw [hCoarseProjection, hRefinedProjection]
    exact refinedSpace.sub_mem
      (refinedSpace.starProjection_apply_mem target)
      (hSpace (coarseSpace.starProjection_apply_mem target))
  have hOrthogonal :
      inner Real (target - refinedEstimate)
        (refinedEstimate - coarseEstimate) = 0 := by
    rw [hRefinedProjection]
    exact refinedSpace.starProjection_inner_eq_zero target _ hInnovationMem
  have hSplit :
      target - coarseEstimate =
        (target - refinedEstimate) + (refinedEstimate - coarseEstimate) := by
    abel
  have hPythagoras :
      ‖target - coarseEstimate‖ ^ 2 =
        ‖target - refinedEstimate‖ ^ 2 +
          ‖refinedEstimate - coarseEstimate‖ ^ 2 := by
    rw [hSplit]
    simpa only [sq] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hOrthogonal
  exact ⟨hPythagoras, by
    nlinarith [sq_nonneg ‖refinedEstimate - coarseEstimate‖]⟩

#print axioms conditional_expectation_refinement_pythagoras

end D5.S3.ConceptDynamics.Prediction.ConditionalExpectationRefinementPythagoras
