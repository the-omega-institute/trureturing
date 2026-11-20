/- GID: D5/S3/Quantum/Algebra/Unitary/PointwiseStabilizer
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/Unitary/PointwiseStabilizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Isometries fixing a subspace pointwise restrict isomorphically to its complement. -/

import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.LinearAlgebra.Determinant

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Algebra.Unitary.PointwiseStabilizer

open Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The linear isometries of `E` that fix every vector of the subspace `K`. -/
def pointwiseStabilizer (K : Submodule 𝕜 E) : Subgroup (E ≃ₗᵢ[𝕜] E) where
  carrier := {U | ∀ x ∈ K, U x = x}
  mul_mem' {U V} hU hV x hx := by
    change U (V x) = x
    rw [hV x hx, hU x hx]
  one_mem' _ _ := rfl
  inv_mem' {U} hU x hx := by
    change U.symm x = x
    rw [LinearIsometryEquiv.symm_apply_eq, hU x hx]

section Restriction

variable {K : Submodule 𝕜 E}

/-- An isometry fixing `K` pointwise maps `Kᗮ` onto `Kᗮ`. -/
private lemma map_orthogonal_eq (U : pointwiseStabilizer K) :
    Kᗮ.map ((U : E ≃ₗᵢ[𝕜] E).toLinearEquiv : E →ₗ[𝕜] E) = Kᗮ := by
  rw [map_orthogonal_equiv]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change (U : E ≃ₗᵢ[𝕜] E) y ∈ K
    rw [U.2 y hy]
    exact hy
  · intro hx
    exact ⟨x, hx, U.2 x hx⟩

/-- Restriction of an isometry fixing `K` pointwise to `Kᗮ`. -/
private def restrict (U : pointwiseStabilizer K) : Kᗮ ≃ₗᵢ[𝕜] Kᗮ :=
  { (U : E ≃ₗᵢ[𝕜] E).toLinearEquiv.ofSubmodules Kᗮ Kᗮ (map_orthogonal_eq U) with
    norm_map' := fun y => (U : E ≃ₗᵢ[𝕜] E).norm_map (y : E) }

/-- Restriction to `Kᗮ` as a group homomorphism. -/
private def restrictHom : pointwiseStabilizer K →* (Kᗮ ≃ₗᵢ[𝕜] Kᗮ) where
  toFun := restrict
  map_one' := by ext y; rfl
  map_mul' _ _ := by ext y; rfl

variable [K.HasOrthogonalProjection]

/-- Extension of an isometry of `Kᗮ` by the identity on `K`. -/
private def extend (W : Kᗮ ≃ₗᵢ[𝕜] Kᗮ) : E ≃ₗᵢ[𝕜] E :=
  (K.orthogonalDecomposition.trans
    (LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl 𝕜 K) W)).trans
      K.orthogonalDecomposition.symm

private lemma extend_apply (W : Kᗮ ≃ₗᵢ[𝕜] Kᗮ) (x : E) :
    extend W x = (K.orthogonalProjectionOnto x : E) + (W (Kᗮ.orthogonalProjectionOnto x) : E) := by
  simp [extend]

private lemma extend_apply_of_mem (W : Kᗮ ≃ₗᵢ[𝕜] Kᗮ) {x : E} (hx : x ∈ K) : extend W x = x := by
  rw [extend_apply, orthogonalProjectionOnto_mem_subspace_eq_self ⟨x, hx⟩,
    orthogonalProjectionOnto_apply_of_mem_orthogonal (K.le_orthogonal_orthogonal hx)]
  simp

private lemma extend_apply_of_mem_orthogonal (W : Kᗮ ≃ₗᵢ[𝕜] Kᗮ) {y : E} (hy : y ∈ Kᗮ) :
    extend W y = W ⟨y, hy⟩ := by
  rw [extend_apply, orthogonalProjectionOnto_apply_of_mem_orthogonal hy,
    orthogonalProjectionOnto_mem_subspace_eq_self ⟨y, hy⟩]
  simp

private lemma restrictHom_bijective :
    Function.Bijective (restrictHom : pointwiseStabilizer K →* (Kᗮ ≃ₗᵢ[𝕜] Kᗮ)) := by
  constructor
  · intro U V h
    apply Subtype.ext
    apply LinearIsometryEquiv.ext
    intro x
    obtain ⟨k, hk, y, hy, rfl⟩ := exists_add_mem_mem_orthogonal (K := K) x
    have hy' : (U : E ≃ₗᵢ[𝕜] E) y = (V : E ≃ₗᵢ[𝕜] E) y := by
      have := congrArg (fun W : Kᗮ ≃ₗᵢ[𝕜] Kᗮ => ((W ⟨y, hy⟩ : Kᗮ) : E)) h
      exact this
    rw [map_add, map_add, U.2 k hk, V.2 k hk, hy']
  · intro W
    refine ⟨⟨extend W, fun x hx => extend_apply_of_mem W hx⟩, ?_⟩
    ext y
    exact extend_apply_of_mem_orthogonal W y.2

end Restriction

/-- Restriction to `Kᗮ` is a group isomorphism from the pointwise stabilizer of `K` onto the
isometry group of `Kᗮ`; when `E` is finite-dimensional it preserves the determinant. -/
theorem exists_mulEquiv_orthogonal (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] :
    ∃ e : pointwiseStabilizer K ≃* (Kᗮ ≃ₗᵢ[𝕜] Kᗮ),
      (∀ (U : pointwiseStabilizer K) (y : Kᗮ), ((e U y : Kᗮ) : E) = (U : E ≃ₗᵢ[𝕜] E) y) ∧
      (FiniteDimensional 𝕜 E → ∀ U : pointwiseStabilizer K,
        LinearMap.det ((U : E ≃ₗᵢ[𝕜] E).toLinearEquiv : E →ₗ[𝕜] E) =
          LinearMap.det ((e U).toLinearEquiv : Kᗮ →ₗ[𝕜] Kᗮ)) := by
  refine ⟨MulEquiv.ofBijective restrictHom restrictHom_bijective, fun U y => rfl, ?_⟩
  intro hE U
  have hmem : ∀ x : E, (U : E ≃ₗᵢ[𝕜] E) x - x ∈ Kᗮ := by
    intro x
    obtain ⟨k, hk, y, hy, rfl⟩ := exists_add_mem_mem_orthogonal (K := K) x
    rw [map_add, U.2 k hk, add_sub_add_left_eq_sub]
    exact Kᗮ.sub_mem (by rw [← map_orthogonal_eq U]; exact ⟨y, hy, rfl⟩) hy
  have he : Kᗮ ≤ Kᗮ.comap ((U : E ≃ₗᵢ[𝕜] E).toLinearEquiv : E →ₗ[𝕜] E) := by
    intro y hy
    show _ ∈ Kᗮ
    rw [← map_orthogonal_eq U]
    exact ⟨y, hy, rfl⟩
  have h1 : LinearMap.restrict _ he =
      ((MulEquiv.ofBijective restrictHom restrictHom_bijective U).toLinearEquiv :
        Kᗮ →ₗ[𝕜] Kᗮ) :=
    LinearMap.ext fun _ => rfl
  have h2 : Kᗮ.mapQ Kᗮ _ he = LinearMap.id := by
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, mkQ_apply, mapQ_apply, LinearMap.id_coe,
      id_eq]
    exact (Submodule.Quotient.eq Kᗮ).mpr (hmem x)
  rw [LinearMap.det_eq_det_mul_det Kᗮ _ he, h1, h2, LinearMap.det_id, mul_one]

end D5.S3.Quantum.Algebra.Unitary.PointwiseStabilizer

