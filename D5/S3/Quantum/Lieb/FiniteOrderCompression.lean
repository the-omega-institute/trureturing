/- GID: D5/S3/Quantum/Lieb/FiniteOrderCompression
   generality: G
   mirror-B: D5/B/S3/Quantum/Lieb/FiniteOrderCompression
   mirror-E: none(waiver:registration-audit-pending)
   anchors: []
   utility: none
   digest: A positive block has its functional-calculus first corner bounded by the calculus of that corner under doubled-space monotonicity. -/
module

public import OmegaMath.Analysis.CornerCompression
public import D5.S3.Quantum.Matrix.Spectral.IsometricCalculus
public import D5.S3.Quantum.Lieb.MonotoneBlockConcavity
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! Functional calculus in a positive corner, with an explicit strict comparison proof. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Lieb.FiniteOrderCompression

open LownerHeinzTheorem JensenOperatorInequality
open D5.S3.Quantum.Lieb.MonotoneBlockConcavity
open scoped Topology

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private theorem omegaEq_of_eq {α : Sort*} {a b : α} (h : a = b) : Omega.Eq a b := by
  cases h
  exact Omega.Eq.refl _

private def corner (i : Fin 2) (X : L (HSum H)) : L H :=
  hsumProj H i ∘L X ∘L hsumIncl H i

private theorem corner_nonneg (i : Fin 2) {X : L (HSum H)} (hX : 0 ≤ X) :
    0 ≤ corner i X := by
  have hpos := ((ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mp hX).adjoint_conj
    (hsumIncl H i)
  simpa only [corner, hsumIncl_adjoint] using
    (ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mpr hpos

private theorem block_corners (X : L (HSum H)) (hX : IsSelfAdjoint X) :
    X = blockOp (corner 0 X) (hsumProj H 0 ∘L X ∘L hsumIncl H 1)
      (star (hsumProj H 0 ∘L X ∘L hsumIncl H 1)) (corner 1 X) := by
  have hs : star (hsumProj H 0 ∘L X ∘L hsumIncl H 1) =
      hsumProj H 1 ∘L X ∘L hsumIncl H 0 := by
    change (hsumProj H 0 ∘L X ∘L hsumIncl H 1).adjoint = _
    simp only [ContinuousLinearMap.adjoint_comp, hsumIncl_adjoint, hsumProj_adjoint]
    change _ = hsumProj H 1 ∘L X ∘L hsumIncl H 0
    rw [show X.adjoint = X from hX.star_eq]
    rfl
  rw [hs]
  apply blockOp_ext <;> intro z
  all_goals
    have hz := congrArg (fun w => X w) (hsumIncl_proj_sum z)
    simp only [map_add] at hz
    rw [← hz]
    simp [corner, blockOp, ContinuousLinearMap.comp_apply, map_add]

private theorem diagonal_calculus (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ici 0)) (A B : L H) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    corner 0 (cfcR f (blockDiagonal A B)) = cfcR f A := by
    change corner 0 (cfcR f (blockDiagonal A B)) = cfcR f A
    have hAf : spectrum ℝ A ⊆ Set.Ici 0 := fun x hx => spectrum_nonneg_of_nonneg hA hx
    have hBf : spectrum ℝ B ⊆ Set.Ici 0 := fun x hx => spectrum_nonneg_of_nonneg hB hx
    rw [cfcR_blockDiagonal f A B (IsSelfAdjoint.of_nonneg hA)
      (IsSelfAdjoint.of_nonneg hB) (hf.mono (Set.union_subset hAf hBf))]
    ext x
    simp [corner, blockDiagonal, ContinuousLinearMap.comp_apply]
private theorem sandwich (X : L (HSum H)) (hX : 0 ≤ X) (ε : ℝ) (hε : 0 < ε) :
    ∃ b : L H, 0 ≤ corner 0 X + ε • 1 ∧ 0 ≤ b ∧
      0 ≤ blockDiagonal (corner 0 X + ε • 1) b ∧
      X ≤ blockDiagonal (corner 0 X + ε • 1) b := by
    obtain ⟨bound, hbound, hle⟩ := block_scalar_sandwich
      (corner 0 X) (corner 1 X) (hsumProj H 0 ∘L X ∘L hsumIncl H 1)
      (IsSelfAdjoint.of_nonneg (corner_nonneg 1 hX)) hε
    rw [← block_corners X (IsSelfAdjoint.of_nonneg hX)] at hle
    refine ⟨bound • (1 : L H), ?_, ?_, ?_, hle⟩
    · exact add_nonneg (corner_nonneg 0 hX) (smul_nonneg hε.le zero_le_one)
    · exact smul_nonneg hbound.le zero_le_one
    · exact hX.trans hle
private theorem limit_closed (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Ici 0))
    (A : L H) (hA : 0 ≤ A) (z : L H)
    (hbounds : ∀ ε : ℝ, 0 < ε → z ≤ cfcR f (A + ε • 1)) : z ≤ cfcR f A := by
    have hshift (ε : ℝ) (hε : ε ∈ Set.Ici (0 : ℝ)) : 0 ≤ A + ε • (1 : L H) :=
      add_nonneg hA (smul_nonneg hε zero_le_one)
    let F : ℝ → ℝ := fun x => f (max x 0)
    have hF : Continuous F := hf.comp_continuous (continuous_id.max continuous_const)
      (fun x => le_max_right x 0)
    have hcF : ContinuousOn (fun ε : ℝ => cfcR F (A + ε • 1)) (Set.Ici 0) := by
      apply ContinuousOn.cfc_of_mem_nhdsSet F (s := Set.univ) (by simp)
        (by fun_prop) (fun ε hε => IsSelfAdjoint.of_nonneg (hshift ε hε))
        hF.continuousOn
    have hc : ContinuousOn (fun ε : ℝ => cfcR f (A + ε • 1)) (Set.Ici 0) := by
      refine hcF.congr ?_
      intro ε hε
      apply cfc_congr
      intro x hx
      exact (congrArg f (max_eq_left (spectrum_nonneg_of_nonneg (hshift ε hε) hx))).symm
    have htend := ((hc.continuousWithinAt (show (0 : ℝ) ∈ Set.Ici 0 by simp)).mono
      Set.Ioi_subset_Ici_self).tendsto
    change z ≤ cfcR f A
    simpa using ge_of_tendsto htend
      (Filter.mem_of_superset self_mem_nhdsWithin (fun ε hε => hbounds ε hε))

/-- The proof uses monotonicity only on the selected doubled Hilbert space.
The function can vanish at zero, and the block may be singular. -/
theorem monotone_double_space_corner (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ici 0))
    (hmono : LownerHeinzCore.OperatorMonotone (𝓐 := L (HSum H)) f)
    (X : L (HSum H)) (hX : 0 ≤ X) :
    hsumProj H 0 ∘L cfcR f X ∘L hsumIncl H 0 ≤
      cfcR f (hsumProj H 0 ∘L X ∘L hsumIncl H 0) := by
  exact Omega.CornerCompression.corner_calculus_le (· ≤ ·) (· ≤ ·) (0 ≤ ·) (0 ≤ ·)
    (fun ε : ℝ => 0 < ε) (fun f => ContinuousOn f (Set.Ici 0)) cfcR cfcR
    (corner 0) (fun A ε => A + ε • 1) blockDiagonal
    (fun h => corner_mono h) (corner_nonneg 0)
    (fun f hf A B hA hB => omegaEq_of_eq (diagonal_calculus f hf A B hA hB))
    (fun X hX ε hε => by
      obtain ⟨b, ha, hb, hd, hle⟩ := sandwich X hX ε hε
      exact Omega.Exists.intro b (Omega.And.intro ha
        (Omega.And.intro hb (Omega.And.intro hd hle)))) limit_closed
    f hf (fun X Y hX hY hXY => hmono hY hX hXY) X hX

#print axioms monotone_double_space_corner
#print axioms Omega.CornerCompression.corner_calculus_le

end D5.S3.Quantum.Lieb.FiniteOrderCompression

namespace D5.S3.Quantum.Lieb.FiniteOrderCompression
open LownerHeinzTheorem JensenOperatorInequality
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

private def matrixCoordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (b : OrthonormalBasis ι ℂ K) : L K ≃⋆ₐ[ℂ] Matrix ι ι ℂ :=
  b.repr.conjStarAlgEquiv.trans Matrix.toEuclideanCLM.symm

private theorem coordinates_cfc {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (b : OrthonormalBasis ι ℂ K) (f : ℝ → ℝ) (X : L K) (hX : IsSelfAdjoint X) :
    matrixCoordinates b (cfc f X) = cfc f (matrixCoordinates b X) := by
  let e := matrixCoordinates b
  have hXe : IsSelfAdjoint (e X) := hX.map e
  have h := StarAlgHomClass.map_cfc e.symm f (e X)
    ((e X).finite_real_spectrum.continuousOn f) (StarAlgEquiv.isometry e.symm).continuous
    hXe (by simpa only [StarAlgEquiv.symm_apply_apply] using hX)
  apply e.symm.injective
  change e.symm (e (cfc f X)) = e.symm (cfc f (e X))
  rw [StarAlgEquiv.symm_apply_apply]
  simpa only [StarAlgEquiv.symm_apply_apply] using h.symm

private def doubledBasis (n : ℕ) :
    OrthonormalBasis (Fin (2 * n)) ℂ (HSum (EuclideanSpace ℂ (Fin n))) :=
  (Pi.orthonormalBasis (fun _ : Fin 2 => EuclideanSpace.basisFun (Fin n) ℂ)).reindex
    ((Equiv.sigmaEquivProd (Fin 2) (Fin n)).trans finProdFinEquiv)

/-- The matrix obtained by compressing the actual operator represented by `X`
to the first copy of `ℂⁿ`, using the orthonormal doubled coordinate basis. -/
private def firstCorner (n : ℕ) (X : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).symm
    (hsumProj (EuclideanSpace ℂ (Fin n)) 0 ∘L
      (matrixCoordinates (doubledBasis n)).symm X ∘L
      hsumIncl (EuclideanSpace ℂ (Fin n)) 0)

private theorem coordinates_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (b : OrthonormalBasis ι ℂ K) (X : L K) (i j : ι) :
    matrixCoordinates b X i j = inner ℂ (b i) (X (b j)) := by
  simp [matrixCoordinates, Matrix.toEuclideanCLM,
    LinearMap.toMatrixOrthonormal_apply_apply, EuclideanSpace.basisFun,
    LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    ← OrthonormalBasis.repr_apply_apply]
  change inner ℂ (EuclideanSpace.single i 1)
    (b.repr (X (b.repr.symm (EuclideanSpace.single j 1)))) = _
  rw [b.repr_symm_single, EuclideanSpace.inner_single_left]
  simpa only [map_one, one_mul] using (b.repr_apply_apply (X (b j)) i)

private theorem firstCorner_eq (n : ℕ)
    (X : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) :
    firstCorner n X = X.submatrix (fun i => finProdFinEquiv (0, i))
      (fun i => finProdFinEquiv (0, i)) := by
  ext i j
  let Y := (matrixCoordinates (doubledBasis n)).symm X
  change matrixCoordinates (EuclideanSpace.basisFun (Fin n) ℂ)
    (hsumProj (EuclideanSpace ℂ (Fin n)) 0 ∘L Y ∘L
      hsumIncl (EuclideanSpace ℂ (Fin n)) 0) i j = _
  rw [coordinates_entry]
  have hX := coordinates_entry (doubledBasis n) Y
    (finProdFinEquiv (0, i)) (finProdFinEquiv (0, j))
  rw [StarAlgEquiv.apply_symm_apply] at hX
  change _ = X (finProdFinEquiv (0, i)) (finProdFinEquiv (0, j))
  rw [hX]
  simp [doubledBasis, OrthonormalBasis.reindex_apply, Pi.orthonormalBasis_apply,
    hsumIncl, hsumEquiv, hsumProj, ContinuousLinearMap.comp_apply,
    EuclideanSpace.basisFun_apply, PiLp.inner_apply]

/-- Finite matrix order of exactly `2n` suffices for the first-corner inequality.
This assertion includes the zero-dimensional and singular blocks. -/
theorem matrix_monotone_corner (n : ℕ) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ici 0))
    (hmono : ∀ (A B : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ),
      A.PosSemidef → B.PosSemidef → A ≤ B → cfc f A ≤ cfc f B)
    (X : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) (hX : X.PosSemidef) :
    (cfc f X).submatrix (fun i : Fin n => finProdFinEquiv (0, i))
        (fun i : Fin n => finProdFinEquiv (0, i)) ≤
      cfc f (X.submatrix (fun i : Fin n => finProdFinEquiv (0, i))
        (fun i : Fin n => finProdFinEquiv (0, i))) := by
  rw [← firstCorner_eq n (cfc f X), ← firstCorner_eq n X]
  classical
  by_cases hn : n = 0
  · subst n
    exact le_of_eq (Subsingleton.elim _ _)
  · haveI : NeZero n := ⟨hn⟩
    let H := EuclideanSpace ℂ (Fin n)
    let e := matrixCoordinates (doubledBasis n)
    have htransport : LownerHeinzCore.OperatorMonotone (𝓐 := L (HSum H)) f := by
      intro A B hA hB hBA
      have hAB : e B ≤ e A := by
        apply sub_nonneg.mp
        simpa only [map_sub] using map_nonneg e (sub_nonneg.mpr hBA)
      have h := hmono (e B) (e A) (Matrix.nonneg_iff_posSemidef.mp (map_nonneg e hB))
        (Matrix.nonneg_iff_posSemidef.mp (map_nonneg e hA)) hAB
      have hh : e (cfc f B) ≤ e (cfc f A) := by
        change matrixCoordinates (doubledBasis n) (cfc f B) ≤
          matrixCoordinates (doubledBasis n) (cfc f A)
        rw [coordinates_cfc (doubledBasis n) f B (IsSelfAdjoint.of_nonneg hB),
          coordinates_cfc (doubledBasis n) f A (IsSelfAdjoint.of_nonneg hA)]
        exact h
      have hout := map_nonneg e.symm (sub_nonneg.mpr hh)
      exact sub_nonneg.mp (by
        simpa only [map_sub, StarAlgEquiv.symm_apply_apply] using hout)
    have hXe : 0 ≤ e.symm X := map_nonneg e.symm hX.nonneg
    have hc := monotone_double_space_corner f hf htransport (e.symm X) hXe
    have hcorner : IsSelfAdjoint
        (hsumProj H 0 ∘L e.symm X ∘L hsumIncl H 0) :=
      IsSelfAdjoint.of_nonneg (corner_nonneg 0 hXe)
    have hfc : e.symm (cfc f X) = cfc f (e.symm X) :=
      StarAlgHomClass.map_cfc e.symm f X (X.finite_real_spectrum.continuousOn f)
        (StarAlgEquiv.isometry e.symm).continuous hX.isHermitian
        (IsSelfAdjoint.of_nonneg hXe)
    have hbase := coordinates_cfc (EuclideanSpace.basisFun (Fin n) ℂ) f
      (hsumProj H 0 ∘L e.symm X ∘L hsumIncl H 0) hcorner
    change (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).symm
      (cfc f (hsumProj H 0 ∘L e.symm X ∘L hsumIncl H 0)) =
      cfc f ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).symm
        (hsumProj H 0 ∘L e.symm X ∘L hsumIncl H 0)) at hbase
    have hout := map_nonneg (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).symm
      (sub_nonneg.mpr hc)
    change (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).symm
      (hsumProj H 0 ∘L e.symm (cfc f X) ∘L hsumIncl H 0) ≤
      cfc f ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).symm
        (hsumProj H 0 ∘L e.symm X ∘L hsumIncl H 0))
    rw [hfc, ← hbase]
    exact sub_nonneg.mp (by simpa only [map_sub] using hout)

#print axioms matrix_monotone_corner
end D5.S3.Quantum.Lieb.FiniteOrderCompression

namespace D5.S3.Quantum.Lieb.FiniteOrderCompression
open Matrix
open D5.S3.Quantum.Lieb.PositiveMapJensen
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.ContractionBlocks
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

private def sumIndex (n : ℕ) : (Fin n ⊕ Fin n) ≃ Fin (2 * n) :=
  finSumFinEquiv.trans (finCongr (by omega))

private def sumCoordinates (n : ℕ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ ≃⋆ₐ[ℂ]
      Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ :=
  { Matrix.reindexAlgEquiv ℂ ℂ (sumIndex n) with
    map_smul' := by intros; exact map_smul (Matrix.reindexAlgEquiv ℂ ℂ (sumIndex n)) _ _
    map_star' := by intro X; exact Matrix.conjTranspose_reindex _ _ X }

private theorem sumIndex_inl (n : ℕ) (i : Fin n) :
    sumIndex n (Sum.inl i) = finProdFinEquiv (0, i) := by
  apply Fin.ext
  simp [sumIndex, finSumFinEquiv_apply_left, finProdFinEquiv]

private theorem sumCoordinates_cfc (n : ℕ) (f : ℝ → ℝ)
    (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (hX : X.IsHermitian) :
    sumCoordinates n (cfc f X) = cfc f (sumCoordinates n X) := by
  exact StarAlgHomClass.map_cfc (sumCoordinates n) f X
    (X.finite_real_spectrum.continuousOn f)
    (StarAlgEquiv.isometry (sumCoordinates n)).continuous hX (hX.isSelfAdjoint.map _)

private theorem sum_corner (n : ℕ) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ici 0))
    (hmono : ∀ (A B : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ),
      A.PosSemidef → B.PosSemidef → A ≤ B → cfc f A ≤ cfc f B)
    (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (hX : X.PosSemidef) :
    (cfc f X).submatrix Sum.inl Sum.inl ≤ cfc f (X.submatrix Sum.inl Sum.inl) := by
  have hc := matrix_monotone_corner n f hf hmono (sumCoordinates n X)
    (Matrix.nonneg_iff_posSemidef.mp (map_nonneg (sumCoordinates n) hX.nonneg))
  rw [← sumCoordinates_cfc n f X hX.isHermitian] at hc
  have he (Y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) :
      (sumCoordinates n Y).submatrix (fun i : Fin n => finProdFinEquiv (0, i))
          (fun i : Fin n => finProdFinEquiv (0, i)) = Y.submatrix Sum.inl Sum.inl := by
    ext i j
    change Y ((sumIndex n).symm (finProdFinEquiv (0, i)))
      ((sumIndex n).symm (finProdFinEquiv (0, j))) = Y (Sum.inl i) (Sum.inl j)
    rw [← sumIndex_inl, ← sumIndex_inl, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  simpa only [he] using hc

/-- Finite order `2n` gives Jensen's inequality for every `n`-dimensional
contraction. No invertibility or positivity at zero is required. -/
theorem matrix_monotone_contraction (n : ℕ) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ici 0)) (hf0 : 0 ≤ f 0)
    (hmono : ∀ (A B : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ),
      A.PosSemidef → B.PosSemidef → A ≤ B → cfc f A ≤ cfc f B)
    (A C : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef)
    (hC : Cᴴ * C ≤ 1) :
    Cᴴ * cfc f A * C ≤ cfc f (Cᴴ * A * C) := by
  classical
  let J : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ := Matrix.fromRows 1 0
  let D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ := Matrix.fromBlocks A 0 0 0
  have hJJ : Jᴴ * J = 1 := by
    simp [J, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows]
  have hD : D.PosSemidef := by
    have he : J * A * Jᴴ = D := by
      simp [J, D, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
        Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols]
      ext (i | i) (j | j) <;> simp
    exact he ▸ hA.mul_mul_conjTranspose_same J
  obtain ⟨U, hU, hUC⟩ := exists_unitary_dilation C
    (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hC))
  let V := U * J
  let X := Uᴴ * D * U
  have hX : X.PosSemidef := hD.conjTranspose_mul_mul_same U
  have hDJ : D * J = J * A := by
    simp [D, J, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul]
  have hTf := cfc_intertwining D A hD.isHermitian hA.isHermitian J hDJ f
  have hUU : Uᴴ * U = 1 := Unitary.star_mul_self_of_mem hU
  have hUstar : U * Uᴴ = 1 := Unitary.mul_star_self_of_mem hU
  have hUX : D * U = U * X := by simp [X, ← Matrix.mul_assoc, hUstar]
  have hUf := cfc_intertwining D X hD.isHermitian hX.isHermitian U hUX f
  have hXf : cfc f X = Uᴴ * cfc f D * U := by
    have hh := congrArg (fun Y => Uᴴ * Y) hUf
    simpa only [← Matrix.mul_assoc, hUU,
      Matrix.one_mul] using hh.symm
  have hcorner := sum_corner n f hf hmono X hX
  have hV : V.submatrix Sum.inl id = C := by
    ext i j
    simpa [V, J, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.one_apply] using hUC i j
  have hcornerX : X.submatrix Sum.inl Sum.inl = Cᴴ * A * C := by
    change (Uᴴ * D * U).submatrix Sum.inl Sum.inl = _
    ext i j
    simp [Matrix.mul_apply, D, Matrix.fromBlocks, Matrix.conjTranspose_apply,
      Fintype.sum_sum_type, hUC]
  have hXcorner : (cfc f X).submatrix Sum.inl Sum.inl = Vᴴ * cfc f D * V := by
    rw [hXf]
    have he (Y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) :
        Y.submatrix Sum.inl Sum.inl = Jᴴ * Y * J := by
      ext i j
      simp [J, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
        Fintype.sum_sum_type, Matrix.one_apply]
    rw [he]
    simp [V, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hDf : cfc f D = Matrix.fromBlocks (cfc f A) 0 0 (f 0 • 1) := by
    let K : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ := Matrix.fromRows 0 1
    have hDK : D * K = K * (0 : Matrix (Fin n) (Fin n) ℂ) := by
      simp [D, K, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul]
    have hKf := cfc_intertwining D 0 hD.isHermitian (Matrix.isHermitian_zero) K hDK f
    rw [cfc_apply_zero, Algebra.algebraMap_eq_smul_one] at hKf
    ext i j
    cases i with
    | inl i => cases j with
      | inl j => simpa [J, Matrix.mul_apply, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
          Fintype.sum_sum_type, Matrix.one_apply] using congrArg (fun Y => Y (Sum.inl i) j) hTf
      | inr j => simpa [K, Matrix.mul_apply, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
          Fintype.sum_sum_type, Matrix.one_apply] using congrArg (fun Y => Y (Sum.inl i) j) hKf
    | inr i => cases j with
      | inl j => simpa [J, Matrix.mul_apply, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
          Fintype.sum_sum_type, Matrix.one_apply] using congrArg (fun Y => Y (Sum.inr i) j) hTf
      | inr j => simpa [K, Matrix.mul_apply, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
          Fintype.sum_sum_type, Matrix.one_apply] using congrArg (fun Y => Y (Sum.inr i) j) hKf
  have hdrop : Cᴴ * cfc f A * C ≤ Vᴴ * cfc f D * V := by
    rw [hDf]
    let R := V.submatrix Sum.inr id
    have he : Vᴴ * Matrix.fromBlocks (cfc f A) 0 0 (f 0 • 1) * V =
        Cᴴ * cfc f A * C + Rᴴ * (f 0 • 1) * R := by
      ext i j
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_sum_type,
        Matrix.fromBlocks, R, ← hV, Matrix.one_apply,
        Finset.mul_sum, Finset.sum_mul, mul_assoc]
      congr 1
      · exact Finset.sum_comm
      · apply Finset.sum_congr rfl
        intro k hk
        ring
    rw [he]
    exact le_add_of_nonneg_right
      (((Matrix.nonneg_iff_posSemidef.mp (smul_nonneg hf0 (show (0 : Matrix (Fin n) (Fin n) ℂ) ≤ 1 from zero_le_one))).conjTranspose_mul_mul_same R).nonneg)
  rw [hXcorner, hcornerX] at hcorner
  exact hdrop.trans hcorner

end D5.S3.Quantum.Lieb.FiniteOrderCompression

namespace D5.S3.Quantum.Lieb.FiniteOrderCompression
open Matrix D5.S3.Quantum.Lieb.PositiveMapJensen
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- The selected doubled finite order restricts to the original finite order. -/
theorem matrix_monotone_restrict (n : ℕ) (f : ℝ → ℝ)
    (hmono : ∀ (A B : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ),
      A.PosSemidef → B.PosSemidef → A ≤ B → cfc f A ≤ cfc f B)
    (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAB : A ≤ B) : cfc f A ≤ cfc f B := by
  classical
  let J : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ := Matrix.fromRows 1 0
  have hJJ : Jᴴ * J = 1 := by
    simp [J, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows]
  let e := sumCoordinates n
  have he (X Y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (hXY : X ≤ Y) :
      e X ≤ e Y := by
    apply sub_nonneg.mp
    simpa only [map_sub] using map_nonneg e (sub_nonneg.mpr hXY)
  have hm := hmono (e (J * A * Jᴴ)) (e (J * B * Jᴴ))
    (map_nonneg e (hA.mul_mul_conjTranspose_same J).nonneg).posSemidef
    (map_nonneg e (hB.mul_mul_conjTranspose_same J).nonneg).posSemidef
    (he _ _ (by simpa using congruence_mono hAB Jᴴ))
  have hcalc (Z : Matrix (Fin n) (Fin n) ℂ) (hZ : Z.PosSemidef) :
      e (cfc f (J * Z * Jᴴ)) = cfc f (e (J * Z * Jᴴ)) :=
    sumCoordinates_cfc n f _ (hZ.mul_mul_conjTranspose_same J).isHermitian
  rw [← hcalc A hA, ← hcalc B hB] at hm
  have hback := map_nonneg e.symm (sub_nonneg.mpr hm)
  have hs : cfc f (J * A * Jᴴ) ≤ cfc f (J * B * Jᴴ) :=
    sub_nonneg.mp (by simpa only [map_sub, StarAlgEquiv.symm_apply_apply] using hback)
  have hsmall := congruence_mono hs J
  have hcorner (Z : Matrix (Fin n) (Fin n) ℂ) (hZ : Z.PosSemidef) :
      Jᴴ * cfc f (J * Z * Jᴴ) * J = cfc f Z := by
    have h := cfc_intertwining (J * Z * Jᴴ) Z
      (hZ.mul_mul_conjTranspose_same J).isHermitian hZ.isHermitian J
      (by simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]) f
    have hh := congrArg (fun Y => Jᴴ * Y) h
    simpa only [← Matrix.mul_assoc, hJJ, Matrix.one_mul] using hh
  simpa only [hcorner A hA, hcorner B hB] using hsmall
end D5.S3.Quantum.Lieb.FiniteOrderCompression
