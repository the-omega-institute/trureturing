/- GID: D5/S3/Quantum/Lieb/FiniteOrderCompression
   generality: G
   mirror-B: D5/B/S3/Quantum/Lieb/FiniteOrderCompression
   mirror-E: none(waiver:registration-audit-pending)
   anchors: []
   utility: none
   digest: A positive block has its functional-calculus first corner bounded by the calculus of that corner under doubled-space monotonicity. -/
module

public import OmegaMath.Analysis.CornerCompression
public import D5.S3.Quantum.Lieb.MonotoneBlockConcavity
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Order

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

private def system : Omega.CornerCompression.System
    (L H) (L (HSum H)) ℝ (ℝ → ℝ) where
  le := (· ≤ ·)
  leDouble := (· ≤ ·)
  positive := (0 ≤ ·)
  positiveDouble := (0 ≤ ·)
  small := (0 < ·)
  continuous := fun f => ContinuousOn f (Set.Ici 0)
  apply := cfcR
  applyDouble := cfcR
  corner := corner 0
  shift := fun A ε => A + ε • 1
  diagonal := blockDiagonal

private theorem system_laws : (system (H := H)).Laws where
  corner_mono := by
    intro X Y hXY
    exact corner_mono hXY
  corner_positive := corner_nonneg 0
  diagonal_calculus := by
    intro f hf A B hA hB
    change corner 0 (cfcR f (blockDiagonal A B)) = cfcR f A
    have hAf : spectrum ℝ A ⊆ Set.Ici 0 := fun x hx => spectrum_nonneg_of_nonneg hA hx
    have hBf : spectrum ℝ B ⊆ Set.Ici 0 := fun x hx => spectrum_nonneg_of_nonneg hB hx
    rw [cfcR_blockDiagonal f A B (IsSelfAdjoint.of_nonneg hA)
      (IsSelfAdjoint.of_nonneg hB) (hf.mono (Set.union_subset hAf hBf))]
    ext x
    simp [corner, blockDiagonal, ContinuousLinearMap.comp_apply]
  sandwich := by
    intro X hX ε hε
    obtain ⟨bound, hbound, hle⟩ := block_scalar_sandwich
      (corner 0 X) (corner 1 X) (hsumProj H 0 ∘L X ∘L hsumIncl H 1)
      (IsSelfAdjoint.of_nonneg (corner_nonneg 1 hX)) hε
    rw [← block_corners X (IsSelfAdjoint.of_nonneg hX)] at hle
    refine ⟨bound • (1 : L H), ?_, ?_, ?_, hle⟩
    · exact add_nonneg (corner_nonneg 0 hX) (smul_nonneg hε.le zero_le_one)
    · exact smul_nonneg hbound.le zero_le_one
    · exact hX.trans hle
  limit_closed := by
    intro f hf A hA z hbounds
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
  exact Omega.CornerCompression.corner_calculus_le system system_laws f hf
    (fun X Y hX hY hXY => hmono hY hX hXY) X hX

#print axioms monotone_double_space_corner
#print axioms Omega.CornerCompression.corner_calculus_le

end D5.S3.Quantum.Lieb.FiniteOrderCompression

namespace D5.S3.Quantum.Lieb.FiniteOrderCompression
open LownerHeinzTheorem JensenOperatorInequality
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

def matrixCoordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
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

def doubledBasis (n : ℕ) :
    OrthonormalBasis (Fin (2 * n)) ℂ (HSum (EuclideanSpace ℂ (Fin n))) :=
  (Pi.orthonormalBasis (fun _ : Fin 2 => EuclideanSpace.basisFun (Fin n) ℂ)).reindex
    ((Equiv.sigmaEquivProd (Fin 2) (Fin n)).trans finProdFinEquiv)

/-- The matrix obtained by compressing the actual operator represented by `X`
to the first copy of `ℂⁿ`, using the orthonormal doubled coordinate basis. -/
def firstCorner (n : ℕ) (X : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).symm
    (hsumProj (EuclideanSpace ℂ (Fin n)) 0 ∘L
      (matrixCoordinates (doubledBasis n)).symm X ∘L
      hsumIncl (EuclideanSpace ℂ (Fin n)) 0)

/-- Finite matrix order of exactly `2n` suffices for the first-corner inequality.
This assertion includes the zero-dimensional and singular blocks. -/
theorem matrix_monotone_corner (n : ℕ) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ici 0))
    (hmono : ∀ (A B : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ),
      A.PosSemidef → B.PosSemidef → A ≤ B → cfc f A ≤ cfc f B)
    (X : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) (hX : X.PosSemidef) :
    firstCorner n (cfc f X) ≤ cfc f (firstCorner n X) := by
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
