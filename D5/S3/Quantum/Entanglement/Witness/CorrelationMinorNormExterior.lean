/- GID: D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormExterior
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/CorrelationMinorNormExterior
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual real complex and ordering correspondences for correlation compounds. -/

import D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormSpectral
import D5.S3.Quantum.Schatten.SingularValueOrder
import D5.S3.SpectralTopology.RectangularDilation

/-! Correspondences for the existing real increasing compound and existing
complex Schatten suppliers. No new norm or state structure is defined. -/
set_option autoImplicit false
set_option linter.style.longLine false
noncomputable section
open Matrix Module
open scoped ComplexOrder BigOperators InnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation
open D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormSpectral
open D5.S3.Quantum.Schatten
namespace D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormExterior

private lemma ofReal_conjTranspose {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) : (A.map Complex.ofReal)ᴴ = Aᴴ.map Complex.ofReal := by
  ext i j
  simp

private lemma ofReal_mul {ι κ ν : Type*} [Fintype κ]
    (A : Matrix ι κ ℝ) (B : Matrix κ ν ℝ) :
    (A*B).map Complex.ofReal = A.map Complex.ofReal * B.map Complex.ofReal :=
  Matrix.map_mul (f := algebraMap ℝ ℂ) (L := A) (M := B)

private lemma ofReal_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℝ) : U.val.map Complex.ofReal ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change U.val.map Complex.ofReal * (U.val.map Complex.ofReal)ᴴ = 1
  rw [ofReal_conjTranspose, ← ofReal_mul]
  have hh : U.val * U.valᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp U.property
  rw [hh]
  ext i j
  by_cases h : i=j <;> simp [Matrix.one_apply,h]

private lemma hermitian_norm_ofReal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) : ‖A.map Complex.ofReal‖ = ‖A‖ := by
  let U := hA.eigenvectorUnitary
  have hd := hA.spectral_theorem
  change A = U.val * Matrix.diagonal hA.eigenvalues * U.valᴴ at hd
  have he : A.map Complex.ofReal = U.val.map Complex.ofReal *
      Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) * (U.val.map Complex.ofReal)ᴴ := by
    conv_lhs => rw [hd]
    rw [ofReal_mul, ofReal_mul, ← ofReal_conjTranspose]
    congr 1
    ext i j
    by_cases h : i=j <;> simp [Matrix.diagonal_apply, h]
  conv_lhs => rw [he]
  simp only [← Matrix.star_eq_conjTranspose]
  rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem (ofReal_unitary U)),
    CStarRing.norm_mem_unitary_mul _ (ofReal_unitary U), Matrix.l2_opNorm_diagonal]
  conv_rhs => rw [hd]
  simp only [← Matrix.star_eq_conjTranspose]
  rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem U.property),
    CStarRing.norm_mem_unitary_mul _ U.property, Matrix.l2_opNorm_diagonal]
  simp only [Pi.norm_def, Complex.nnnorm_real, Function.comp_def, RCLike.ofReal_real_eq_id,
    id_eq]

/-- Real complexification preserves the actual rectangular Euclidean operator norm. -/
theorem opNorm_ofReal {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ ℝ) :
    ‖A.map Complex.ofReal‖ = ‖A‖ := by
  have hG : ((A.map Complex.ofReal)ᴴ * A.map Complex.ofReal) =
      (Aᴴ*A).map Complex.ofReal := by rw [ofReal_conjTranspose, ← ofReal_mul]
  have hh := hermitian_norm_ofReal (Aᴴ*A) A.posSemidef_conjTranspose_mul_self.isHermitian
  rw [← hG, Matrix.l2_opNorm_conjTranspose_mul_self,
    Matrix.l2_opNorm_conjTranspose_mul_self] at hh
  nlinarith [norm_nonneg A, norm_nonneg (A.map Complex.ofReal)]

/-- The complex supplier's sorted spectrum is the native real descending spectrum,
with all zeros retained and the original Gram normalization. -/
theorem sorted_singularValues_ofReal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin (Fintype.card (Fin n))) :
    singularValuesSorted (A.map Complex.ofReal) i = A.toEuclideanLin.singularValues i := by
  rw [singularValuesSorted_eq_sqrt_eigenvalues_zero, native_singular_value]
  congr 1
  have he : ((A.map Complex.ofReal)ᴴ * A.map Complex.ofReal) =
      (Aᴴ*A).map Complex.ofReal := by rw [ofReal_conjTranspose, ← ofReal_mul]
  have transfer (M : Matrix (Fin n) (Fin n) ℂ) (hm : M = (Aᴴ*A).map Complex.ofReal)
      (hM : M.IsHermitian) : hM.eigenvalues₀ = A.posSemidef_conjTranspose_mul_self.isHermitian.eigenvalues₀ := by
    subst M
    exact D5.S3.SpectralTopology.RectangularDilation.eigenvalues_ofReal _ _ hM
  simpa only [Matrix.conjTranspose_conjTranspose] using
    congrFun (transfer _ he (A.map Complex.ofReal).posSemidef_conjTranspose_mul_self.isHermitian) i

/-- The existing square complex SVD identifies the actual operator norm with
the largest singular value, for every finite index type. -/
theorem complex_opNorm_sorted {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hn : 0 < Fintype.card ι) :
    ‖A‖ = singularValuesSorted A ⟨0,hn⟩ := by
  obtain ⟨U,V,h⟩ := D5.S3.Quantum.Foundation.FiniteTraceDistance.exists_svd_sqrt_eigenvalues A
  have he : A = U.val * diagonal (fun i => (singularValues A i : ℂ)) * V.valᴴ := by
    simpa only [singularValues, Matrix.conjTranspose_conjTranspose] using h
  conv_lhs => rw [he]
  simp only [← Matrix.star_eq_conjTranspose]
  rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem V.property),
    CStarRing.norm_mem_unitary_mul _ U.property, Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (singularValuesSorted_nonneg A _)).mpr
    intro i
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (singularValues_nonneg A i)]
    obtain ⟨j,hj⟩ := singularValues_mem_sorted A i
    rw [hj]
    exact singularValuesSorted_antitone A (Nat.zero_le _)
  · obtain ⟨i,hi⟩ := singularValuesSorted_mem_values A ⟨0,hn⟩
    have hh := norm_le_pi_norm (fun i => (singularValues A i : ℂ)) i
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (singularValues_nonneg A i), ← hi] at hh
    exact hh

private def orderPermutation {n h : ℕ} (S : {S : Finset (Fin n) // S.card = h}) :
    Equiv.Perm (Fin h) :=
  (@Finset.orderIsoOfFin (Fin n) (AllOrdered.fintypeLinearOrderClassical _) S.val h S.property).toEquiv.trans
    (S.val.orderIsoOfFin S.property).toEquiv.symm

private def orderSign {n h : ℕ} (S : {S : Finset (Fin n) // S.card = h}) : ℂ :=
  ((Equiv.Perm.sign (orderPermutation S) : ℤ) : ℂ)

private lemma old_order_embedding {n h : ℕ} (S : {S : Finset (Fin n) // S.card = h}) (i : Fin h) :
    @Finset.orderEmbOfFin (Fin n) (AllOrdered.fintypeLinearOrderClassical _) S.val h S.property i =
      S.val.orderEmbOfFin S.property (orderPermutation S i) := by
  change ((@Finset.orderIsoOfFin (Fin n) (AllOrdered.fintypeLinearOrderClassical _)
    S.val h S.property i : S.val) : Fin n) = _
  change _ = ((S.val.orderIsoOfFin S.property) ((S.val.orderIsoOfFin S.property).symm
    (@Finset.orderIsoOfFin (Fin n) (AllOrdered.fintypeLinearOrderClassical _) S.val h S.property i)) : Fin n)
  rw [OrderIso.apply_symm_apply]

/-- The canonical increasing and supplier order conventions differ only by
actual diagonal sign unitaries, including all multiplicities and zero minors. -/
theorem compound_order_correspondence {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (h : ℕ) :
    compoundMatrix (A.map Complex.ofReal) h = Matrix.diagonal orderSign *
      (compound h A).map Complex.ofReal * Matrix.diagonal orderSign := by
  classical
  ext S T
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply]
  have he : (A.map Complex.ofReal).submatrix
      (@Finset.orderEmbOfFin (Fin n) (AllOrdered.fintypeLinearOrderClassical _) S.val h S.property)
      (@Finset.orderEmbOfFin (Fin n) (AllOrdered.fintypeLinearOrderClassical _) T.val h T.property) =
      ((A.submatrix (S.val.orderEmbOfFin S.property) (T.val.orderEmbOfFin T.property)).map Complex.ofReal).submatrix
        (orderPermutation S) (orderPermutation T) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.map_apply, old_order_embedding]
  change _ = orderSign S * (↑((A.submatrix _ _).det)) * orderSign T
  rw [compoundMatrix,he]
  have hp (M : Matrix (Fin h) (Fin h) ℂ) :
      (M.submatrix (orderPermutation S) (orderPermutation T)).det =
        orderSign S * (orderSign T * M.det) := by
    have hid : M.submatrix (orderPermutation S) (orderPermutation T) =
        (M.submatrix id (orderPermutation T)).submatrix (orderPermutation S) id := rfl
    rw [hid, Matrix.det_permute, Matrix.det_permute']
    rfl
  rw [hp]
  have hm (M : Matrix (Fin h) (Fin h) ℝ) : (M.map Complex.ofReal).det = (M.det : ℂ) := by
    exact (RingHom.map_det (algebraMap ℝ ℂ) M).symm
  rw [hm]
  ring

private lemma orderSign_unitary {n h : ℕ} :
    (Matrix.diagonal orderSign : Matrix {S : Finset (Fin n) // S.card = h} _ ℂ) ∈
      Matrix.unitaryGroup _ ℂ := by
  classical
  rw [Matrix.mem_unitaryGroup_iff]
  change Matrix.diagonal orderSign * (Matrix.diagonal orderSign)ᴴ = 1
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext S T
  by_cases he : S=T
  · subst T
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    change ((Equiv.Perm.sign (orderPermutation S) : ℤ) : ℂ) *
      star (((Equiv.Perm.sign (orderPermutation S) : ℤ) : ℂ)) = 1
    simp only [star_intCast]
    exact_mod_cast Int.isUnit_mul_self (Units.isUnit (Equiv.Perm.sign (orderPermutation S)))
  · simp [Matrix.diagonal_apply_ne _ he, Matrix.one_apply_ne he]

/-- The actual increasing real compound operator norm is the product of the
largest h native descending singular values. -/
theorem cmnInf_eq_native_product {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : ℕ) (hh : h ≤ n) :
    cmnInf h A = ∏ i : Fin h, A.toEuclideanLin.singularValues i := by
  classical
  have hcard : 0 < Fintype.card {S : Finset (Fin n) // S.card = h} := by
    simp only [Fintype.card_subtype, Finset.card_univ]
    simpa using Nat.choose_pos hh
  have he := prod_singularValuesSorted_eq_compoundSV (A.map Complex.ofReal) h (by simpa using hh)
  rw [← complex_opNorm_sorted _ hcard, compound_order_correspondence,
    CStarRing.norm_mul_mem_unitary _ orderSign_unitary,
    CStarRing.norm_mem_unitary_mul _ orderSign_unitary, opNorm_ofReal] at he
  unfold cmnInf
  rw [← he]
  apply Finset.prod_congr rfl
  intro i _
  exact sorted_singularValues_ofReal A ⟨i.val,by simpa using lt_of_lt_of_le i.isLt hh⟩

end D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormExterior
