/- GID: D5/S3/Observer/Tomography/InnovationEnergyRecurrence
   generality: G
   mirror-B: D5/B/S3/Observer/Tomography/InnovationEnergyRecurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Nested observation spaces split residual energy into later residual and innovation. -/

import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/- Library-search audit trail (2026-08-15):
   * Loogle query `‖?x‖ ^ 2 = ‖?p‖ ^ 2 + ‖?r‖ ^ 2` returned the exact
     pinned-Mathlib hits `Submodule.norm_sq_eq_add_norm_sq_projection` and
     `Submodule.norm_sq_eq_add_norm_sq_starProjection`; the latter is imported
     and applied below.
   * Loogle query `orthogonalProjectionOnto norm` did not resolve as written
     and suggested the namespaced query `Submodule.orthogonalProjectionOnto norm`.
   * LeanSearch API attempts returned HTTP 404 and method-not-allowed responses.
     Repository and formalization searches found no innovation-energy recurrence.
-/

namespace D5.S3.Observer.Tomography.InnovationEnergyRecurrence

noncomputable section

/-- Squared norm of the component not captured by an observation subspace. -/
def residualEnergy {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (U : Submodule ℝ V) (x : V) : ℝ :=
  ‖Uᗮ.starProjection x‖ ^ 2

/-- The new directions gained when the observation space grows from `U` to `W`. -/
def innovationSubspace {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (U W : Submodule ℝ V) : Submodule ℝ V :=
  Uᗮ ⊓ W

/-- For nested observation subspaces, earlier residual energy is exactly the
later residual energy plus the energy in the newly observed directions. -/
theorem innovation_energy_recurrence
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (U W : Submodule ℝ V) (x : V) (hUW : U ≤ W) :
    residualEnergy U x =
      residualEnergy W x + ‖(innovationSubspace U W).starProjection x‖ ^ 2 := by
  let E : Submodule ℝ V := innovationSubspace U W
  have hEU : E ≤ Uᗮ := inf_le_left
  have hEW : E ≤ W := inf_le_right
  have hspan : U ⊔ E = W := by
    simpa [E, innovationSubspace] using
      (Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hUW)
  have hinnovation : E.starProjection (Uᗮ.starProjection x) = E.starProjection x := by
    have hcomp := Submodule.starProjection_comp_starProjection_of_le hEU
    simpa only [ContinuousLinearMap.comp_apply] using
      DFunLike.congr_fun hcomp x
  have hremainder : Eᗮ.starProjection (Uᗮ.starProjection x) = Wᗮ.starProjection x := by
    apply Submodule.eq_starProjection_of_mem_orthogonal
    · exact Submodule.orthogonal_le hEW
        (Submodule.starProjection_apply_mem Wᗮ x)
    · apply E.le_orthogonal_orthogonal
      constructor
      · exact Uᗮ.sub_mem
          (Submodule.starProjection_apply_mem Uᗮ x)
          (Submodule.orthogonal_le hUW
            (Submodule.starProjection_apply_mem Wᗮ x))
      · have hxU : x - Uᗮ.starProjection x ∈ U := by
          simp
        have hxW : x - Wᗮ.starProjection x ∈ W := by
          simp
        change Uᗮ.starProjection x - Wᗮ.starProjection x ∈ W
        rw [show Uᗮ.starProjection x - Wᗮ.starProjection x =
          (x - Wᗮ.starProjection x) - (x - Uᗮ.starProjection x) by abel]
        exact W.sub_mem hxW (hUW hxU)
  have hpythagorean :=
    Submodule.norm_sq_eq_add_norm_sq_starProjection (Uᗮ.starProjection x) E
  rw [hinnovation, hremainder] at hpythagorean
  change ‖Uᗮ.starProjection x‖ ^ 2 =
    ‖Wᗮ.starProjection x‖ ^ 2 + ‖E.starProjection x‖ ^ 2
  simpa only [add_comm] using hpythagorean

/-- The recurrence has a concrete nonzero instance on the real line. -/
example :
    residualEnergy (⊥ : Submodule ℝ ℝ) 1 =
      residualEnergy (⊤ : Submodule ℝ ℝ) 1 +
        ‖(innovationSubspace (⊥ : Submodule ℝ ℝ) ⊤).starProjection 1‖ ^ 2 := by
  apply innovation_energy_recurrence
  exact bot_le

end

end D5.S3.Observer.Tomography.InnovationEnergyRecurrence
