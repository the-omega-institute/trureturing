/- GID: D5/S3/Quantum/Schatten/SingularValueOrder
   generality: G
   mirror-B: D5/B/S3/Quantum/Schatten/SingularValueOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Loewner monotonicity of sorted Gram singular values. -/

import D5.S3.Quantum.Schatten.CompoundMatrices
import D5.S3.SpectralTopology.HermitianEigenvaluePerturbation

/-! Sorted singular values respect comparison of positive Gram forms. -/

noncomputable section
open Matrix
open scoped InnerProductSpace ComplexOrder
namespace D5.S3.Quantum.Schatten

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem eigenvalues_zero_mono {n : ℕ} {H K : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.IsHermitian) (hK : K.IsHermitian) (hHK : (K - H).PosSemidef)
    (i : Fin (Fintype.card (Fin n))) : hH.eigenvalues₀ i ≤ hK.eigenvalues₀ i := by
  let T := H.toEuclideanLin
  let S := K.toEuclideanLin
  have hT : (T : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] _).IsSymmetric :=
    isSymmetric_toEuclideanLin_iff.mpr hH
  have hS : (S : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] _).IsSymmetric :=
    isSymmetric_toEuclideanLin_iff.mpr hK
  obtain ⟨V, hV, hlow⟩ :=
    D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.exists_submodule_forall_unit_eigenvalue_le_re_inner
      hT finrank_euclideanSpace i
  obtain ⟨x, hxV, hnx, hup⟩ :=
    D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.exists_unit_vector_re_inner_le_eigenvalue
      hS finrank_euclideanSpace i V hV
  have hq := hHK.re_dotProduct_nonneg (WithLp.ofLp x)
  have hinner : RCLike.re ⟪T x, x⟫_ℂ ≤ RCLike.re ⟪S x, x⟫_ℂ := by
    rw [inner_re_symm (T x) x, inner_re_symm (S x) x]
    change Complex.re (H.mulVec (WithLp.ofLp x) ⬝ᵥ star (WithLp.ofLp x)) ≤
      Complex.re (K.mulVec (WithLp.ofLp x) ⬝ᵥ star (WithLp.ofLp x))
    rw [dotProduct_comm, dotProduct_comm (K.mulVec _)]
    simp only [Matrix.sub_mulVec, dotProduct_sub, map_sub] at hq
    change 0 ≤ Complex.re (star (WithLp.ofLp x) ⬝ᵥ K.mulVec (WithLp.ofLp x)) -
      Complex.re (star (WithLp.ofLp x) ⬝ᵥ H.mulVec (WithLp.ofLp x)) at hq
    exact sub_nonneg.mp hq
  exact (hlow x hxV hnx).trans (hinner.trans hup)

theorem singularValuesSorted_eq_sqrt_eigenvalues_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin (Fintype.card (Fin n))) :
    singularValuesSorted A i =
      Real.sqrt ((isHermitian_mul_conjTranspose_self A.conjTranspose).eigenvalues₀ i) := by
  let hA := isHermitian_mul_conjTranspose_self A.conjTranspose
  have hs : (Finset.univ.val.map (singularValues A)).sort (· ≥ ·) =
      List.ofFn (fun j => Real.sqrt (hA.eigenvalues₀ j)) := by
    change (Multiset.map ((fun j => Real.sqrt (hA.eigenvalues₀ j)) ∘
      (Fintype.equivOfCardEq (Fintype.card_fin _)).symm) Finset.univ.val).sort (· ≥ ·) = _
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
    simp only [Fin.univ_val_map, Multiset.map_coe, List.map_ofFn, Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simp only [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    have ha : Antitone (fun j => Real.sqrt (hA.eigenvalues₀ j)) :=
      fun _ _ hij => Real.sqrt_le_sqrt (hA.eigenvalues₀_antitone hij)
    exact ha.sortedGE_ofFn
  unfold singularValuesSorted
  simpa only [hs, List.get_eq_getElem, List.getElem_ofFn]

/-- Increasing a Gram matrix in the Loewner order increases every sorted singular value. -/
theorem gram_singularValuesSorted_mono {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (h : (B.conjTranspose * B - A.conjTranspose * A).PosSemidef)
    (i : Fin (Fintype.card (Fin n))) : singularValuesSorted A i ≤ singularValuesSorted B i := by
  rw [singularValuesSorted_eq_sqrt_eigenvalues_zero,
    singularValuesSorted_eq_sqrt_eigenvalues_zero]
  apply Real.sqrt_le_sqrt
  exact eigenvalues_zero_mono _ _ (by simpa only [conjTranspose_conjTranspose] using h) i

/-- Left multiplication by a unitary matrix preserves the sorted singular values. -/
theorem singularValuesSorted_unitary_mul {n : ℕ} (U A : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (i : Fin (Fintype.card (Fin n))) :
    singularValuesSorted (U * A) i = singularValuesSorted A i := by
  have hu : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hg : (U * A)ᴴ * (U * A) = Aᴴ * A := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ,
      hu, Matrix.one_mul]
  apply le_antisymm
  · exact gram_singularValuesSorted_mono (U * A) A (by rw [hg, sub_self]; exact PosSemidef.zero) i
  · exact gram_singularValuesSorted_mono A (U * A) (by rw [hg, sub_self]; exact PosSemidef.zero) i

/-- Taking the adjoint preserves the sorted singular values. -/
theorem singularValuesSorted_conjTranspose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (i : Fin (Fintype.card (Fin n))) :
    singularValuesSorted Aᴴ i = singularValuesSorted A i := by
  have he : (isHermitian_mul_conjTranspose_self A).eigenvalues =
      (isHermitian_conjTranspose_mul_self A).eigenvalues :=
    ((isHermitian_mul_conjTranspose_self A).eigenvalues_eq_eigenvalues_iff
      (isHermitian_conjTranspose_mul_self A)).mpr (charpoly_mul_comm A Aᴴ)
  rw [singularValuesSorted_eq_sqrt_eigenvalues_zero,
    singularValuesSorted_eq_sqrt_eigenvalues_zero]
  have hj := congrFun he ((Fintype.equivOfCardEq (Fintype.card_fin _)) i)
  simpa only [IsHermitian.eigenvalues, Equiv.symm_apply_apply,
    conjTranspose_conjTranspose] using congrArg Real.sqrt hj

theorem eigenvalues_zero_smul {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (q : ℝ) (hq : 0 ≤ q)
    (hQ : ((q : ℂ) • H).IsHermitian) (i : Fin (Fintype.card (Fin n))) :
    hQ.eigenvalues₀ i = q * hH.eigenvalues₀ i := by
  let T := H.toEuclideanLin
  let S := ((q : ℂ) • H).toEuclideanLin
  have hT : T.IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr hH
  have hS : S.IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr hQ
  have hinner (x : EuclideanSpace ℂ (Fin n)) :
      RCLike.re ⟪S x, x⟫_ℂ = q * RCLike.re ⟪T x, x⟫_ℂ := by
    change RCLike.re ⟪((q : ℂ) • H).toEuclideanLin x, x⟫_ℂ = _
    rw [map_smul, LinearMap.smul_apply, inner_smul_left]
    simp [T]
  apply le_antisymm
  · obtain ⟨V, hV, hlow⟩ :=
      D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.exists_submodule_forall_unit_eigenvalue_le_re_inner
        hS finrank_euclideanSpace i
    obtain ⟨x, hx, hn, hup⟩ :=
      D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.exists_unit_vector_re_inner_le_eigenvalue
        hT finrank_euclideanSpace i V hV
    exact (hlow x hx hn).trans ((hinner x).le.trans (mul_le_mul_of_nonneg_left hup hq))
  · obtain ⟨V, hV, hlow⟩ :=
      D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.exists_submodule_forall_unit_eigenvalue_le_re_inner
        hT finrank_euclideanSpace i
    obtain ⟨x, hx, hn, hup⟩ :=
      D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.exists_unit_vector_re_inner_le_eigenvalue
        hS finrank_euclideanSpace i V hV
    exact (mul_le_mul_of_nonneg_left (hlow x hx hn) hq).trans ((hinner x).symm.le.trans hup)

/-- Nonnegative real scaling acts componentwise on sorted singular values. -/
theorem singularValuesSorted_smul_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (r : ℝ) (hr : 0 ≤ r) (i : Fin (Fintype.card (Fin n))) :
    singularValuesSorted ((r : ℂ) • A) i = r * singularValuesSorted A i := by
  rw [singularValuesSorted_eq_sqrt_eigenvalues_zero,
    singularValuesSorted_eq_sqrt_eigenvalues_zero]
  have hg : ((r : ℂ) • A)ᴴ * ((r : ℂ) • A) =
      ((r ^ 2 : ℝ) : ℂ) • (Aᴴ * A) := by
    simp only [conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
      smul_mul_assoc, mul_smul_comm, smul_smul, ← Complex.ofReal_mul, pow_two]
  have he := eigenvalues_zero_smul (Aᴴ * A) (isHermitian_conjTranspose_mul_self A)
    (r ^ 2) (sq_nonneg r) (by rw [← hg]; exact isHermitian_conjTranspose_mul_self _) i
  have he' : (isHermitian_mul_conjTranspose_self ((r : ℂ) • A)ᴴ).eigenvalues₀ i =
      r ^ 2 * (isHermitian_mul_conjTranspose_self Aᴴ).eigenvalues₀ i := by
    simpa only [conjTranspose_conjTranspose, ← hg] using he
  rw [he', Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr]

end D5.S3.Quantum.Schatten
