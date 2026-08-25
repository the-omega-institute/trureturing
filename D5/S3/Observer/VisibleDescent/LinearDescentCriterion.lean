/- GID: D5/S3/Observer/VisibleDescent/LinearDescentCriterion
   generality: G
   mirror-B: D5/B/S3/Observer/VisibleDescent/LinearDescentCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Orthogonal visible descent is equivalent to a zero hidden-to-visible block. -/

import D5.S3.Observer.HiddenFlow.VisibleHiddenProjectionCriteria
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic.TFAE

/- Library-search audit trail (2026-08-25):
   * The existing hidden-flow module supplies the canonical complementary-projection
     interpretation and the adjacent invariant/cross-block criteria; it has no theorem
     stating bounded descent, projection-fiber dependence, or the unique descent map.
   * Exact pinned-Mathlib hits `Submodule.orthogonalProjectionOnto`,
     `Submodule.starProjection`, `orthogonalProjectionOnto_eq_zero_iff`,
     `orthogonalProjectionOnto_mem_subspace_eq_self`, and
     `ContinuousLinearMap.comp_apply` are applied below.
   * Repository searches found one matrix-carrier unbundled compression named
     `visibleDynamics`, but no bounded map from the visible subtype to itself and no
     public or private three-way equivalence matching this statement.
   * Pinned Mathlib and repository searches for `PTQ`, projection-fiber dependence,
     and unique bounded linear factorization found no exact packaged theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.VisibleDescent.LinearDescentCriterion

/-- The source's canonical descent `PT|_V`: include a visible vector, apply the
ambient bounded dynamics, and project orthogonally back to the visible subspace. -/
noncomputable def orthogonalVisibleDescent
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    (T : E →L[𝕜] E) : V →L[𝕜] V :=
  (V.orthogonalProjectionOnto.comp T).comp V.subtypeL

private theorem cross_block_zero_of_descent
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    (T : E →L[𝕜] E) (descended : V →L[𝕜] V)
    (commutes :
      V.orthogonalProjectionOnto.comp T =
        descended.comp V.orthogonalProjectionOnto) :
    (V.orthogonalProjectionOnto.comp T).comp Vᗮ.starProjection = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  have hAt := congrArg
    (fun map : E →L[𝕜] V => map (Vᗮ.starProjection x)) commutes
  have hiddenMem : Vᗮ.starProjection x ∈ Vᗮ :=
    Vᗮ.starProjection_apply_mem x
  have projectionZero :
      V.orthogonalProjectionOnto (Vᗮ.starProjection x) = 0 :=
    V.orthogonalProjectionOnto_eq_zero_iff.mpr hiddenMem
  change V.orthogonalProjectionOnto (T (Vᗮ.starProjection x)) = 0
  calc
    V.orthogonalProjectionOnto (T (Vᗮ.starProjection x)) =
        descended (V.orthogonalProjectionOnto (Vᗮ.starProjection x)) := by
          simpa only [ContinuousLinearMap.comp_apply] using hAt
    _ = descended 0 := congrArg descended projectionZero
    _ = 0 := map_zero descended

private theorem dependence_of_cross_block_zero
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    (T : E →L[𝕜] E)
    (crossBlock :
      (V.orthogonalProjectionOnto.comp T).comp Vᗮ.starProjection = 0) :
    forall x y,
      V.orthogonalProjectionOnto x = V.orthogonalProjectionOnto y ->
        V.orthogonalProjectionOnto (T x) =
          V.orthogonalProjectionOnto (T y) := by
  intro x y hxy
  have projectionSub : V.orthogonalProjectionOnto (x - y) = 0 := by
    simpa using sub_eq_zero.mpr hxy
  have subHidden : x - y ∈ Vᗮ :=
    V.orthogonalProjectionOnto_eq_zero_iff.mp projectionSub
  have hiddenProjectionSub : Vᗮ.starProjection (x - y) = x - y :=
    Submodule.starProjection_eq_self_iff.mpr subHidden
  have hAt := congrArg
    (fun map : E →L[𝕜] V => map (x - y)) crossBlock
  have visibleSubZero : V.orthogonalProjectionOnto (T (x - y)) = 0 := by
    simpa [ContinuousLinearMap.comp_apply, hiddenProjectionSub] using hAt
  rw [map_sub, map_sub] at visibleSubZero
  exact sub_eq_zero.mp visibleSubZero

private theorem canonical_descent_commutes_of_dependence
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    (T : E →L[𝕜] E)
    (depends : forall x y,
      V.orthogonalProjectionOnto x = V.orthogonalProjectionOnto y ->
        V.orthogonalProjectionOnto (T x) =
          V.orthogonalProjectionOnto (T y)) :
    V.orthogonalProjectionOnto.comp T =
      (orthogonalVisibleDescent V T).comp V.orthogonalProjectionOnto := by
  apply ContinuousLinearMap.ext
  intro x
  have hDepends := depends x (V.orthogonalProjectionOnto x)
    (V.orthogonalProjectionOnto_mem_subspace_eq_self
      (V.orthogonalProjectionOnto x)).symm
  simpa [orthogonalVisibleDescent, ContinuousLinearMap.comp_apply] using hDepends

private theorem descent_eq_canonical
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    (T : E →L[𝕜] E) (descended : V →L[𝕜] V)
    (commutes :
      V.orthogonalProjectionOnto.comp T =
        descended.comp V.orthogonalProjectionOnto) :
    descended = orthogonalVisibleDescent V T := by
  apply ContinuousLinearMap.ext
  intro v
  have hAt := congrArg (fun map : E →L[𝕜] V => map v.1) commutes
  simpa [orthogonalVisibleDescent, ContinuousLinearMap.comp_apply] using hAt.symm

/-- For a bounded operator on a Hilbert space, existence of visible descent,
vanishing of the hidden-to-visible block, and dependence of `PTx` only on `Px`
are equivalent. When they hold, the unique descent is the constructed map
`PT|_V`. -/
theorem linear_descent_criterion
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    (T : E →L[𝕜] E) :
    List.TFAE [
      Exists fun descended : V →L[𝕜] V =>
        V.orthogonalProjectionOnto.comp T =
          descended.comp V.orthogonalProjectionOnto,
      (V.orthogonalProjectionOnto.comp T).comp Vᗮ.starProjection = 0,
      forall x y,
        V.orthogonalProjectionOnto x = V.orthogonalProjectionOnto y ->
          V.orthogonalProjectionOnto (T x) =
            V.orthogonalProjectionOnto (T y)] ∧
    ((V.orthogonalProjectionOnto.comp T).comp Vᗮ.starProjection = 0 ->
      (V.orthogonalProjectionOnto.comp T =
        (orthogonalVisibleDescent V T).comp V.orthogonalProjectionOnto) ∧
      forall descended : V →L[𝕜] V,
        V.orthogonalProjectionOnto.comp T =
            descended.comp V.orthogonalProjectionOnto ->
          descended = orthogonalVisibleDescent V T) := by
  have equivalence : List.TFAE [
      Exists fun descended : V →L[𝕜] V =>
        V.orthogonalProjectionOnto.comp T =
          descended.comp V.orthogonalProjectionOnto,
      (V.orthogonalProjectionOnto.comp T).comp Vᗮ.starProjection = 0,
      forall x y,
        V.orthogonalProjectionOnto x = V.orthogonalProjectionOnto y ->
          V.orthogonalProjectionOnto (T x) =
            V.orthogonalProjectionOnto (T y)] := by
    tfae_have 1 -> 2 := by
      rintro ⟨descended, commutes⟩
      exact cross_block_zero_of_descent V T descended commutes
    tfae_have 2 -> 3 := by
      exact dependence_of_cross_block_zero V T
    tfae_have 3 -> 1 := by
      intro depends
      exact ⟨orthogonalVisibleDescent V T,
        canonical_descent_commutes_of_dependence V T depends⟩
    tfae_finish
  refine ⟨equivalence, ?_⟩
  intro crossBlock
  have depends := dependence_of_cross_block_zero V T crossBlock
  refine ⟨canonical_descent_commutes_of_dependence V T depends, ?_⟩
  intro descended commutes
  exact descent_eq_canonical V T descended commutes

#print axioms linear_descent_criterion

end D5.S3.Observer.VisibleDescent.LinearDescentCriterion
