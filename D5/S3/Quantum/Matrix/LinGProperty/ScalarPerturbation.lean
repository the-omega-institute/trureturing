/- GID: D5/S3/Quantum/Matrix/LinGProperty/ScalarPerturbation
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/LinGProperty/ScalarPerturbation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Quantum/Schatten/SingularValueOrder]
   utility: none
   digest: Scalar perturbation bounds for every sorted singular value. -/

import D5.S3.Quantum.Schatten.SingularValueOrder

/-! The indexed perturbation bound follows from two spectral subspaces. -/

noncomputable section
open Matrix
open scoped InnerProductSpace ComplexOrder
namespace D5.S3.Quantum.Matrix.LinGProperty

set_option backward.isDefEq.respectTransparency false

private theorem gram_inner_norm_sq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (x : EuclideanSpace ℂ (Fin n)) :
    RCLike.re ⟪(Aᴴ * A).toEuclideanLin x, x⟫_ℂ = ‖A.toEuclideanLin x‖ ^ 2 := by
  change RCLike.re ⟪Matrix.toLpLin 2 2 (Aᴴ * A) x, x⟫_ℂ = _
  rw [Matrix.toLpLin_mul_same, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_left,
    ← inner_self_eq_norm_sq (𝕜 := ℂ)]

/-- Adding a scalar identity changes each singular value by at most the scalar modulus. -/
theorem singularValuesSorted_add_scalar {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) (j : Fin (Fintype.card (Fin n))) :
    singularValuesSorted (A + z • 1) j ≤ singularValuesSorted A j + ‖z‖ := by
  let B := A + z • 1
  let H := (Aᴴ * A).toEuclideanLin
  let K := (Bᴴ * B).toEuclideanLin
  have hH : H.IsSymmetric :=
    isSymmetric_toEuclideanLin_iff.mpr (isHermitian_conjTranspose_mul_self A)
  have hK : K.IsSymmetric :=
    isSymmetric_toEuclideanLin_iff.mpr (isHermitian_conjTranspose_mul_self B)
  obtain ⟨V, hV, hlow⟩ :=
    D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.exists_submodule_forall_unit_eigenvalue_le_re_inner
      hK finrank_euclideanSpace j
  obtain ⟨x, hx, hnx, hupp⟩ :=
    D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.exists_unit_vector_re_inner_le_eigenvalue
      hH finrank_euclideanSpace j V hV
  have hlow' := hlow x hx hnx
  change (isHermitian_conjTranspose_mul_self B).eigenvalues₀ j ≤
    RCLike.re ⟪(Bᴴ * B).toEuclideanLin x, x⟫_ℂ at hlow'
  change RCLike.re ⟪(Aᴴ * A).toEuclideanLin x, x⟫_ℂ ≤
    (isHermitian_conjTranspose_mul_self A).eigenvalues₀ j at hupp
  rw [gram_inner_norm_sq] at hlow' hupp
  have hAx : ‖A.toEuclideanLin x‖ ≤ singularValuesSorted A j := by
    rw [Schatten.singularValuesSorted_eq_sqrt_eigenvalues_zero]
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, conjTranspose_conjTranspose] using
      Real.sqrt_le_sqrt hupp
  have hBx : singularValuesSorted B j ≤ ‖B.toEuclideanLin x‖ := by
    rw [Schatten.singularValuesSorted_eq_sqrt_eigenvalues_zero]
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, conjTranspose_conjTranspose] using
      Real.sqrt_le_sqrt hlow'
  have happly : B.toEuclideanLin x = A.toEuclideanLin x + z • x := by
    simp [B, map_add, map_smul]
  calc
    singularValuesSorted B j ≤ ‖B.toEuclideanLin x‖ := hBx
    _ ≤ ‖A.toEuclideanLin x‖ + ‖z • x‖ := by rw [happly]; exact norm_add_le _ _
    _ = ‖A.toEuclideanLin x‖ + ‖z‖ := by rw [norm_smul, hnx, mul_one]
    _ ≤ singularValuesSorted A j + ‖z‖ := add_le_add hAx le_rfl

/-- A real scalar identity shifts the decreasing Hermitian eigenvalue list. -/
theorem eigenvalues_zero_add_scalar {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (r : ℝ)
    (hB : (A + (r : ℂ) • 1).IsHermitian)
    (j : Fin (Fintype.card (Fin n))) :
    hB.eigenvalues₀ j = hA.eigenvalues₀ j + r := by
  let T := A.toEuclideanLin
  let S := (A + (r : ℂ) • 1).toEuclideanLin
  have hT : T.IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr hA
  have hS : S.IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr hB
  have hinner (x : EuclideanSpace ℂ (Fin n)) (hx : ‖x‖ = 1) :
      RCLike.re ⟪S x, x⟫_ℂ = RCLike.re ⟪T x, x⟫_ℂ + r := by
    have happly : S x = T x + (r : ℂ) • x := by
      change (A + (r : ℂ) • 1).toEuclideanLin x = _
      rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply]
      rfl
    rw [happly, inner_add_left, map_add, inner_smul_left]
    simp [inner_self_eq_norm_sq_to_K, hx]
  apply le_antisymm
  · obtain ⟨V, hV, hlow⟩ :=
      D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.exists_submodule_forall_unit_eigenvalue_le_re_inner
        hS finrank_euclideanSpace j
    obtain ⟨x, hx, hnx, hup⟩ :=
      D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.exists_unit_vector_re_inner_le_eigenvalue
        hT finrank_euclideanSpace j V hV
    have hl := hlow x hx hnx
    rw [hinner x hnx] at hl
    exact hl.trans (add_le_add hup le_rfl)
  · obtain ⟨V, hV, hlow⟩ :=
      D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.exists_submodule_forall_unit_eigenvalue_le_re_inner
        hT finrank_euclideanSpace j
    obtain ⟨x, hx, hnx, hup⟩ :=
      D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.exists_unit_vector_re_inner_le_eigenvalue
        hS finrank_euclideanSpace j V hV
    rw [hinner x hnx] at hup
    exact (add_le_add (hlow x hx hnx) le_rfl).trans hup

end D5.S3.Quantum.Matrix.LinGProperty
