/- GID: D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/SubmersionZero
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/General/LinearAlgebra/SubmersionZero
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.General.LinearAlgebra.SubmersionZero. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/General/LinearAlgebra/SubmersionZero.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.LinearAlgebra.Base
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of linear algebra and matrices (textbook or folklore).

General lemmas of real and complex analysis (textbook or folklore).

This file: Separating forms separate U ⊗ V; ultrametric bound on Mx; vanishing via submersion. -/

/-- Over a principal ideal domain R, with V torsion-free: if linear forms f_i on U have common
kernel 0, so do the maps f_i ⊗ 1 : U ⊗ V → V. -/
lemma tensor_eq_zero_of_separating {U V} [AddCommGroup U] [AddCommGroup V] {R ι} [CommRing R]
  [IsDomain R] [IsPrincipalIdealRing R] [Module R U] [Module R V] [Module.IsTorsionFree R V]
  {f : ι → Module.Dual R U} (hf : ∀ {a}, (∀ i, f i a = 0) → a = 0) Z
  (h : ∀ i, TensorProduct.lift (.lsmul R V ∘ₗ f i) Z = 0) : Z = 0 := by
  obtain ⟨S, _, W, rfl⟩ := by simpa using
    TensorProduct.exists_finite_submodule_right_of_setFinite {Z}
  obtain ⟨b, rfl⟩ := W.eq_repr_basis_right (Module.finBasis ..)
  simp [b.ext (g := 0) (hf fun i ↦ (Module.finBasis ..).linearIndependent.eq_coords_of_eq (g := 0)
    (Subtype.ext (by simpa [b.sum_fintype] using h i)) ·)]

/-- Over an ultrametric normed field, if c ≥ 0 bounds the absolute values of all entries of a
matrix M, then ‖Mx‖ ≤ c‖x‖ in the sup norm for every vector x. -/
lemma norm_mulVec_le {K l m} [NormedField K] [IsUltrametricDist K] [Fintype l] [Fintype m]
    {M : Matrix l m K} {c} (h : ∀ i j, ‖M i j‖ ≤ c) x (o : 0 ≤ c := by simp) : ‖M.mulVec x‖ ≤
    c * ‖x‖ := by simp [*, pi_norm_le_iff_of_nonneg, mul_le_mul, mul_nonneg, norm_le_pi_norm,
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg, M.mulVec_apply_eq_sum]

/-- Let G be entire on a complex Banach space F, and f: E → F strictly differentiable at a with
surjective derivative. If G∘f vanishes near a, then G = 0. -/
lemma eq_zero_of_submersion {E F} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {G f} {f' : E →L[ℂ] F} {a}
    (hG : AnalyticOnNhd ℂ G .univ) (hf : HasStrictFDerivAt f f' a) (h : f'.range = ⊤)
    (h0 : ∀ᶠ x in nhds a, G (f x) = (0 : ℂ)) y : G y = 0 :=
  congr($(hG.eq_of_eventuallyEq analyticOnNhd_const ((hf.map_nhds_eq_of_surj h).ge h0)) y)
