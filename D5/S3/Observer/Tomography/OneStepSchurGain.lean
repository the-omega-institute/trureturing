/- GID: D5/S3/Observer/Tomography/OneStepSchurGain
   generality: G
   mirror-B: D5/B/S3/Observer/Tomography/OneStepSchurGain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A generated observation direction gives its exact normalized distance gain. -/

import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/- Library-search audit trail (2026-08-25):
   * Exact repository hit `InnovationEnergyRecurrence.innovation_energy_recurrence`
     gives the real finite-ambient nested-space identity; exact repository hit
     `OneStepHedgingGain.one_step_hedging_gain` gives its abstract nonzero quotient.
     Neither constructs the next space from the new generator or states the zero case.
   * Pinned Mathlib exact hits `Submodule.starProjection_singleton`,
     `Submodule.starProjection_minimal`, `Submodule.starProjection_orthogonal_val`,
     and `Submodule.norm_sq_eq_add_norm_sq_starProjection` are applied below.
   * Repository and pinned-Mathlib searches found no theorem packaging the generated
     real-or-complex one-step update with both source cases. -/

noncomputable section

open RCLike

namespace D5.S3.Observer.Tomography.OneStepSchurGain

private theorem infDist_submodule_eq_norm_starProjection_orthogonal
    {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    (U : Submodule 𝕜 V) [U.HasOrthogonalProjection] (x : V) :
    Metric.infDist x (U : Set V) = ‖Uᗮ.starProjection x‖ := by
  rw [Metric.infDist_eq_iInf]
  simp_rw [dist_eq_norm]
  calc
    (⨅ y : U, ‖x - y‖) = ‖x - U.starProjection x‖ :=
      (U.starProjection_minimal x).symm
    _ = ‖Uᗮ.starProjection x‖ := by rw [U.starProjection_orthogonal_val]

private theorem nested_distance_drop
    {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    (U W : Submodule 𝕜 V) [U.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    [(Uᗮ ⊓ W).HasOrthogonalProjection] (x : V) (hUW : U ≤ W) :
    Metric.infDist x (U : Set V) ^ 2 - Metric.infDist x (W : Set V) ^ 2 =
      ‖(Uᗮ ⊓ W).starProjection x‖ ^ 2 := by
  let E : Submodule 𝕜 V := Uᗮ ⊓ W
  have hEU : E ≤ Uᗮ := inf_le_left
  have hEW : E ≤ W := inf_le_right
  have hinnovation : E.starProjection (Uᗮ.starProjection x) = E.starProjection x := by
    have hcomp := Submodule.starProjection_comp_starProjection_of_le hEU
    simpa only [ContinuousLinearMap.comp_apply] using DFunLike.congr_fun hcomp x
  have hremainder : Eᗮ.starProjection (Uᗮ.starProjection x) = Wᗮ.starProjection x := by
    apply Submodule.eq_starProjection_of_mem_orthogonal
    · exact Submodule.orthogonal_le hEW (Submodule.starProjection_apply_mem Wᗮ x)
    · apply E.le_orthogonal_orthogonal
      constructor
      · exact Uᗮ.sub_mem
          (Submodule.starProjection_apply_mem Uᗮ x)
          (Submodule.orthogonal_le hUW (Submodule.starProjection_apply_mem Wᗮ x))
      · have hxU : x - Uᗮ.starProjection x ∈ U := by simp
        have hxW : x - Wᗮ.starProjection x ∈ W := by simp
        change Uᗮ.starProjection x - Wᗮ.starProjection x ∈ W
        rw [show Uᗮ.starProjection x - Wᗮ.starProjection x =
          (x - Wᗮ.starProjection x) - (x - Uᗮ.starProjection x) by abel]
        exact W.sub_mem hxW (hUW hxU)
  have hpythagorean := Submodule.norm_sq_eq_add_norm_sq_starProjection
    (Uᗮ.starProjection x) E
  rw [hinnovation, hremainder] at hpythagorean
  rw [infDist_submodule_eq_norm_starProjection_orthogonal,
    infDist_submodule_eq_norm_starProjection_orthogonal]
  dsimp only [E] at hpythagorean
  linarith

/-- Adjoining a generator to a finite-dimensional observation subspace constructs
its orthogonal innovation. A nonzero innovation gives the normalized squared
distance drop, while a zero innovation leaves the distance unchanged. -/
theorem one_step_schur_gain
    {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    (S : Submodule 𝕜 V) [FiniteDimensional 𝕜 S] (target generator : V) :
    let residual := Sᗮ.starProjection generator
    let next := S ⊔ 𝕜 ∙ generator
    (residual ≠ 0 →
      Metric.infDist target (S : Set V) ^ 2 -
          Metric.infDist target (next : Set V) ^ 2 =
        ‖inner 𝕜 target residual‖ ^ 2 / ‖residual‖ ^ 2) ∧
    (residual = 0 →
      Metric.infDist target (next : Set V) = Metric.infDist target (S : Set V)) := by
  let residual := Sᗮ.starProjection generator
  let next := S ⊔ 𝕜 ∙ generator
  letI : FiniteDimensional 𝕜 (𝕜 ∙ generator) := by infer_instance
  letI : FiniteDimensional 𝕜 next := by
    dsimp only [next]
    infer_instance
  change
    (residual ≠ 0 →
      Metric.infDist target (S : Set V) ^ 2 -
          Metric.infDist target (next : Set V) ^ 2 =
        ‖inner 𝕜 target residual‖ ^ 2 / ‖residual‖ ^ 2) ∧
    (residual = 0 →
      Metric.infDist target (next : Set V) = Metric.infDist target (S : Set V))
  have hResidualMemOrthogonal : residual ∈ Sᗮ := by
    exact Submodule.starProjection_apply_mem Sᗮ generator
  have hResidualFormula : residual = generator - S.starProjection generator := by
    exact Submodule.starProjection_orthogonal_val generator
  have hResidualMemNext : residual ∈ next := by
    rw [hResidualFormula]
    exact next.sub_mem
      ((show 𝕜 ∙ generator ≤ next from le_sup_right)
        (Submodule.mem_span_singleton_self generator))
      ((show S ≤ next from le_sup_left) (Submodule.starProjection_apply_mem S generator))
  have hSpace : S ⊔ 𝕜 ∙ residual = next := by
    apply le_antisymm
    · exact sup_le le_sup_left
        ((Submodule.span_singleton_le_iff_mem residual next).2 hResidualMemNext)
    · apply sup_le
      · exact le_sup_left
      · rw [Submodule.span_singleton_le_iff_mem]
        rw [show generator = S.starProjection generator + residual by
          rw [hResidualFormula]; abel]
        exact (S ⊔ 𝕜 ∙ residual).add_mem
          ((show S ≤ S ⊔ 𝕜 ∙ residual from le_sup_left)
            (Submodule.starProjection_apply_mem S generator))
          ((show 𝕜 ∙ residual ≤ S ⊔ 𝕜 ∙ residual from le_sup_right)
            (Submodule.mem_span_singleton_self residual))
  have hInnovation : Sᗮ ⊓ next = 𝕜 ∙ residual := by
    apply le_antisymm
    · intro z hz
      have hzNext : z ∈ S ⊔ 𝕜 ∙ residual := by
        rw [hSpace]
        exact hz.2
      rcases Submodule.mem_sup.mp hzNext with ⟨s, hs, t, ht, hst⟩
      have htOrthogonal : t ∈ Sᗮ := by
        exact ((Submodule.span_singleton_le_iff_mem residual Sᗮ).2
          hResidualMemOrthogonal) ht
      have hsOrthogonal : s ∈ Sᗮ := by
        rw [show s = z - t by rw [← hst]; abel]
        exact Sᗮ.sub_mem hz.1 htOrthogonal
      have hsZero : s = 0 := by
        have hsBot : s ∈ (⊥ : Submodule 𝕜 V) :=
          (Submodule.orthogonal_disjoint S).le_bot ⟨hs, hsOrthogonal⟩
        simpa only [Submodule.mem_bot] using hsBot
      rw [hsZero, zero_add] at hst
      exact hst ▸ ht
    · rw [Submodule.span_singleton_le_iff_mem]
      exact ⟨hResidualMemOrthogonal, hResidualMemNext⟩
  constructor
  · intro hResidual
    have hDrop := nested_distance_drop S next target le_sup_left
    have hDrop' :
        Metric.infDist target (S : Set V) ^ 2 -
            Metric.infDist target (next : Set V) ^ 2 =
          ‖(𝕜 ∙ residual).starProjection target‖ ^ 2 := by
      simpa only [hInnovation] using hDrop
    rw [Submodule.starProjection_singleton] at hDrop'
    have hResidualNorm : ‖residual‖ ≠ 0 := norm_ne_zero_iff.mpr hResidual
    rw [norm_smul, norm_div, norm_inner_symm residual target,
      RCLike.norm_ofReal, abs_of_nonneg (sq_nonneg ‖residual‖)] at hDrop'
    field_simp at hDrop' ⊢
    nlinarith [norm_nonneg residual]
  · intro hResidual
    have hGeneratorMem : generator ∈ S := by
      have : generator - S.starProjection generator = 0 := by
        simpa only [← hResidualFormula] using hResidual
      exact Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp this).symm
    have hNext : next = S := by
      exact sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem generator S).2 hGeneratorMem)
    rw [hNext]

#print axioms one_step_schur_gain

end D5.S3.Observer.Tomography.OneStepSchurGain
