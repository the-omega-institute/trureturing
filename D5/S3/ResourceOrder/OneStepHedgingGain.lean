/- GID: D5/S3/ResourceOrder/OneStepHedgingGain
   generality: G
   mirror-B: D5/B/S3/ResourceOrder/OneStepHedgingGain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A nonzero innovation gives the exact one-step squared hedging gain. -/

import Mathlib.Topology.MetricSpace.HausdorffDistance
import D5.S3.Observer.Tomography.InnovationEnergyRecurrence

/- Library-search audit trail (2026-08-16):
   * Repository searches for one-step hedging gains and distance-to-span identities found no
     equivalent D5 declaration. `InnovationEnergyRecurrence` supplies the nested-space energy
     decomposition and is imported above.
   * Two natural-language `smart_search.sh` queries exited 1 after their local declaration-name
     scan. Exact identifier queries found `Submodule.starProjection_singleton` and
     `Submodule.norm_sq_eq_add_norm_sq_starProjection` in pinned Mathlib.
   * Loogle JSON queries returned one exact hit each for `Submodule.starProjection_singleton` and
     `Submodule.starProjection_minimal`; both are composed below with `Metric.infDist_eq_iInf`. -/

noncomputable section

open D5.S3.Observer.Tomography.InnovationEnergyRecurrence

namespace D5.S3.ResourceOrder.OneStepHedgingGain

private theorem infDist_submodule_eq_norm_starProjection_orthogonal
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (U : Submodule ℝ V) (x : V) :
    Metric.infDist x (U : Set V) = ‖Uᗮ.starProjection x‖ := by
  rw [Metric.infDist_eq_iInf]
  simp_rw [dist_eq_norm]
  calc
    (⨅ y : U, ‖x - y‖) = ‖x - U.starProjection x‖ :=
      (U.starProjection_minimal x).symm
    _ = ‖Uᗮ.starProjection x‖ := by rw [U.starProjection_orthogonal_val]

/-- If the new directions in a nested pair of finite-dimensional real inner-product subspaces
are spanned by a nonzero residual, then the decrease in squared distance to the attainable
subspace is exactly the normalized squared coupling with that residual. -/
theorem one_step_hedging_gain
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (M Mnext : Submodule ℝ V) (x residual : V)
    (hNested : M ≤ Mnext)
    (hInnovation : innovationSubspace M Mnext = ℝ ∙ residual)
    (hResidual : residual ≠ 0) :
    Metric.infDist x (M : Set V) ^ 2 - Metric.infDist x (Mnext : Set V) ^ 2 =
      (abs (inner ℝ x residual)) ^ 2 / ‖residual‖ ^ 2 := by
  have hResidualNorm : ‖residual‖ ≠ 0 := norm_ne_zero_iff.mpr hResidual
  have hProjection :
      ‖(innovationSubspace M Mnext).starProjection x‖ ^ 2 =
        (abs (inner ℝ x residual)) ^ 2 / ‖residual‖ ^ 2 := by
    rw [hInnovation, Submodule.starProjection_singleton]
    rw [real_inner_comm residual x, norm_smul, norm_div, RCLike.norm_ofReal,
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖residual‖)]
    field_simp
  rw [infDist_submodule_eq_norm_starProjection_orthogonal,
    infDist_submodule_eq_norm_starProjection_orthogonal]
  have hRecurrence := innovation_energy_recurrence M Mnext x hNested
  rw [hProjection] at hRecurrence
  simpa only [residualEnergy, sub_eq_iff_eq_add, add_comm] using hRecurrence

#print axioms one_step_hedging_gain

end D5.S3.ResourceOrder.OneStepHedgingGain
