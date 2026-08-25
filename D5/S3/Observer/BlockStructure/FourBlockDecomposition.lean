/- GID: D5/S3/Observer/BlockStructure/FourBlockDecomposition
   generality: G
   mirror-B: D5/B/S3/Observer/BlockStructure/FourBlockDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Four typed orthogonal blocks decompose T, including zero and empty-index cases. -/

import D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/- Library-search audit trail (2026-08-25):
   * Repository and pinned-Mathlib searches for `four_block_decomposition` and the
     expanded four-term formula returned no exact theorem.
   * `ProjectionCommutatorIdentity.commutator_eq_cross_blocks` is the exact adjacent
     commutator result, so the corollary below imports and applies it without reproving it.
   * `OrthogonalProjectionComplement.orthogonal_complement_projection_identities`
     bundles the relevant six laws, but requires completeness and closedness. The exact
     upstream `Submodule.starProjection_add_starProjection_orthogonal` works under the
     weaker `HasOrthogonalProjection` instance and is applied directly below.
   * `Submodule.orthogonalProjectionOnto`, `starProjection`, and `subtypeL` supply the
     four typed continuous linear maps; no repository wrapper already packages them.
 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.BlockStructure.FourBlockDecomposition

open D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity

/-- Splitting the identity on both sides of `T` gives its four algebraic blocks.
Idempotence of `P` is not needed for this ring identity. -/
theorem four_block_decomposition {A : Type*} [Ring A] (P Q T : A)
    (hQ : Q = 1 - P) :
    T = P * T * P + P * T * Q + Q * T * P + Q * T * Q := by
  have hComplement : P + Q = 1 := by
    rw [hQ]
    simp
  calc
    T = 1 * T * 1 := by simp
    _ = (P + Q) * T * (P + Q) := by rw [hComplement]
    _ = (P * T + Q * T) * (P + Q) := by rw [add_mul]
    _ = P * T * P + P * T * Q + Q * T * P + Q * T * Q := by noncomm_ring
#print axioms four_block_decomposition

/-- Without `Q = 1 - P`, the four-term formula already fails over the integers. -/
theorem complement_relation_is_necessary :
    let P : ℤ := 0
    let Q : ℤ := 0
    let T : ℤ := 1
    Q ≠ 1 - P ∧
      T ≠ P * T * P + P * T * Q + Q * T * P + Q * T * Q := by
  norm_num
#print axioms complement_relation_is_necessary

/-- The visible internal block `PTP`, with both its domain and codomain restricted to `V`. -/
noncomputable def visibleInternalBlock
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    (T : E →L[𝕜] E) : V →L[𝕜] V :=
  (V.orthogonalProjectionOnto.comp T).comp
    (V.starProjection.comp V.subtypeL)

/-- The hidden-to-visible block `PTQ`, from `Vᗮ` to `V`. -/
noncomputable def hiddenVisibleInfluence
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    (T : E →L[𝕜] E) : Vᗮ →L[𝕜] V :=
  (V.orthogonalProjectionOnto.comp T).comp
    (Vᗮ.starProjection.comp Vᗮ.subtypeL)

/-- The visible-to-hidden leakage block `QTP`, from `V` to `Vᗮ`. -/
noncomputable def visibleResidualLeakage
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    (T : E →L[𝕜] E) : V →L[𝕜] Vᗮ :=
  (Vᗮ.orthogonalProjectionOnto.comp T).comp
    (V.starProjection.comp V.subtypeL)

/-- The residual internal block `QTQ`, with domain and codomain `Vᗮ`. -/
noncomputable def residualInternalBlock
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    (T : E →L[𝕜] E) : Vᗮ →L[𝕜] Vᗮ :=
  (Vᗮ.orthogonalProjectionOnto.comp T).comp
    (Vᗮ.starProjection.comp Vᗮ.subtypeL)

/-- The four typed maps evaluate to the corresponding ambient projection products. -/
theorem typed_block_formulas
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    (T : E →L[𝕜] E) (v : V) (r : Vᗮ) :
    (visibleInternalBlock V T v : E) =
        V.starProjection (T (V.starProjection v)) ∧
      (hiddenVisibleInfluence V T r : E) =
        V.starProjection (T (Vᗮ.starProjection r)) ∧
      (visibleResidualLeakage V T v : E) =
        Vᗮ.starProjection (T (V.starProjection v)) ∧
      (residualInternalBlock V T r : E) =
        Vᗮ.starProjection (T (Vᗮ.starProjection r)) := by
  simp [visibleInternalBlock, hiddenVisibleInfluence, visibleResidualLeakage,
    residualInternalBlock, ContinuousLinearMap.comp_apply]
#print axioms typed_block_formulas

/-- Orthogonal projections onto `V` and `Vᗮ` give the four-block decomposition of `T`. -/
theorem orthogonal_four_block_decomposition
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    (T : E →L[𝕜] E) :
    T = V.starProjection.comp (T.comp V.starProjection) +
        V.starProjection.comp (T.comp Vᗮ.starProjection) +
        Vᗮ.starProjection.comp (T.comp V.starProjection) +
        Vᗮ.starProjection.comp (T.comp Vᗮ.starProjection) := by
  have split (x : E) :
      x = V.starProjection x + Vᗮ.starProjection x := by
    exact (V.starProjection_add_starProjection_orthogonal x).symm
  apply ContinuousLinearMap.ext
  intro x
  simp only [add_apply, ContinuousLinearMap.comp_apply]
  calc
    T x = T (V.starProjection x + Vᗮ.starProjection x) :=
      congrArg (fun y => T y) (split x)
    _ = T (V.starProjection x) + T (Vᗮ.starProjection x) := by rw [map_add]
    _ = (V.starProjection (T (V.starProjection x)) +
          Vᗮ.starProjection (T (V.starProjection x))) +
        (V.starProjection (T (Vᗮ.starProjection x)) +
          Vᗮ.starProjection (T (Vᗮ.starProjection x))) := by
      exact congrArg₂ (· + ·)
        (split (T (V.starProjection x)))
        (split (T (Vᗮ.starProjection x)))
    _ = V.starProjection (T (V.starProjection x)) +
          V.starProjection (T (Vᗮ.starProjection x)) +
          Vᗮ.starProjection (T (V.starProjection x)) +
          Vᗮ.starProjection (T (Vᗮ.starProjection x)) := by abel
#print axioms orthogonal_four_block_decomposition

/-- The previously proved commutator identity is the off-diagonal corollary. -/
theorem commutator_off_diagonal_corollary
    {A : Type*} [Ring A] (P Q T : A) (hQ : Q = 1 - P) :
    commutator P T = P * T * Q - Q * T * P := by
  exact commutator_eq_cross_blocks P Q T hQ
#print axioms commutator_off_diagonal_corollary

example {A : Type*} [Ring A] (T : A) :
    T = (0 : A) * T * 0 + 0 * T * 1 + 1 * T * 0 + 1 * T * 1 := by
  exact four_block_decomposition 0 1 T (by simp)

example {A : Type*} [Ring A] (T : A) :
    T = (1 : A) * T * 1 + 1 * T * 0 + 0 * T * 1 + 0 * T * 0 := by
  exact four_block_decomposition 1 0 T (by simp)

example {A : Type*} [Ring A] (P Q : A) (hQ : Q = 1 - P) :
    (0 : A) = P * 0 * P + P * 0 * Q + Q * 0 * P + Q * 0 * Q := by
  exact four_block_decomposition P Q 0 hQ

example {A : Type*} [Ring A] (P Q : A) (hQ : Q = 1 - P) :
    (1 : A) = P * 1 * P + P * 1 * Q + Q * 1 * P + Q * 1 * Q := by
  exact four_block_decomposition P Q 1 hQ

/-- The empty matrix index gives a one-element operator ring, covering `n = 0`. -/
example :
    let P : Matrix (Fin 0) (Fin 0) ℤ := 0
    let Q : Matrix (Fin 0) (Fin 0) ℤ := 0
    let T : Matrix (Fin 0) (Fin 0) ℤ := 0
    T = P * T * P + P * T * Q + Q * T * P + Q * T * Q := by
  dsimp only
  apply four_block_decomposition
  ext i
  exact Fin.elim0 i

end D5.S3.Observer.BlockStructure.FourBlockDecomposition
