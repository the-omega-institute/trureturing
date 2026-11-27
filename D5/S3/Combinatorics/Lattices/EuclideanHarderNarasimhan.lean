/- GID: D5/S3/Combinatorics/Lattices/EuclideanHarderNarasimhan
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Lattices/EuclideanHarderNarasimhan
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gram covolumes give exact index inequalities and unique Euclidean HN filtrations. -/

import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import D5.S3.Arith.AbsoluteValues.Heights.Hadamard
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.Closure
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import D5.S3.Combinatorics.Lattices.HarderNarasimhan
import D5.S3.Combinatorics.Lattices.EuclideanSaturation

/-! Gram covolumes, exact saturation indices and Euclidean HN filtrations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace D5.S3.Combinatorics.Lattices.EuclideanGram

open Matrix
open scoped MatrixOrder

/-- The square root of the Gram determinant, including the empty family. -/
private def gramVolume {E : Type*} [Inner ℝ E] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (v : ι → E) : ℝ :=
  Real.sqrt (gram ℝ v).det

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem fischer_fin_psd {p q : ℕ}
    (H : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ) (hH : H.PosSemidef) :
    H.det ≤ (H.submatrix Sum.inl Sum.inl).det *
      (H.submatrix Sum.inr Sum.inr).det := by
  classical
  letI : LinearOrder (Fin p ⊕ Fin q) :=
    LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  let R := CFC.sqrt H
  have hR : R * Rᵀ = H := by
    have hs : Rᵀ = R := by
      simpa only [conjTranspose_eq_transpose_of_trivial] using
        (CFC.sqrt_nonneg H).posSemidef.isHermitian.eq
    rw [hs]
    exact CFC.sqrt_mul_sqrt_self H hH.nonneg
  let A := R.submatrix Sum.inl id
  let B := R.submatrix Sum.inr id
  have hAB : fromRows A B = R := by
    ext i j
    cases i <;> rfl
  have hA : A * Aᵀ = H.submatrix Sum.inl Sum.inl := by
    rw [← hR, submatrix_mul _ _ Sum.inl id Sum.inl Function.bijective_id,
      transpose_submatrix]
  have hB : B * Bᵀ = H.submatrix Sum.inr Sum.inr := by
    rw [← hR, submatrix_mul _ _ Sum.inr id Sum.inr Function.bijective_id,
      transpose_submatrix]
  simpa only [hAB, hR, hA, hB] using det_mul_transpose_self_fromRows_le A B

private theorem fischer_psd {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (H : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hH : H.PosSemidef) :
    H.det ≤ (H.submatrix Sum.inl Sum.inl).det *
      (H.submatrix Sum.inr Sum.inr).det := by
  let e := Equiv.sumCongr (Fintype.equivFin ι).symm (Fintype.equivFin κ).symm
  have h := fischer_fin_psd (H.submatrix e e) (hH.submatrix e)
  rw [det_submatrix_equiv_self] at h
  have ha : (H.submatrix e e).submatrix Sum.inl Sum.inl =
      (H.submatrix Sum.inl Sum.inl).submatrix
        (Fintype.equivFin ι).symm (Fintype.equivFin ι).symm := rfl
  have hb : (H.submatrix e e).submatrix Sum.inr Sum.inr =
      (H.submatrix Sum.inr Sum.inr).submatrix
        (Fintype.equivFin κ).symm (Fintype.equivFin κ).symm := rfl
  rw [ha, hb, det_submatrix_equiv_self, det_submatrix_equiv_self] at h
  exact h

private theorem schur_submatrix {ι κ η : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (X : Matrix ι κ ℝ) (Q : Matrix κ κ ℝ) (e : η → κ) :
    (Q - Xᴴ * P⁻¹ * X).submatrix e e =
      Q.submatrix e e - (X.submatrix id e)ᴴ * P⁻¹ * X.submatrix id e := by
  change Q.submatrix e e - (Xᴴ * P⁻¹ * X).submatrix e e = _
  rw [submatrix_mul _ _ e id e Function.bijective_id,
    submatrix_mul _ _ e id id Function.bijective_id, submatrix_id_id,
    conjTranspose_submatrix]

private theorem shared_det_le {ι κ η : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype η] [DecidableEq η]
    (H : Matrix (ι ⊕ (κ ⊕ η)) (ι ⊕ (κ ⊕ η)) ℝ)
    (hH : H.PosSemidef) :
    (H.submatrix Sum.inl Sum.inl).det * H.det ≤
      (H.submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)).det *
        (H.submatrix (Sum.map id Sum.inr) (Sum.map id Sum.inr)).det := by
  let P := H.submatrix Sum.inl Sum.inl
  let X := H.submatrix Sum.inl Sum.inr
  let Q := H.submatrix Sum.inr Sum.inr
  have hP := hH.submatrix Sum.inl
  have hA := hH.submatrix (Sum.map id Sum.inl)
  have hB := hH.submatrix (Sum.map id Sum.inr)
  by_cases hz : P.det = 0
  · change P.det * H.det ≤ _
    rw [hz, zero_mul]
    exact mul_nonneg hA.det_nonneg hB.det_nonneg
  have hPpos : P.PosDef := hP.posDef_iff_det_ne_zero.mpr hz
  letI := hPpos.isUnit.invertible
  have h21 : H.submatrix Sum.inr Sum.inl = Xᴴ := by
    dsimp only [X]
    rw [conjTranspose_submatrix, hH.isHermitian.eq]
  have hb : fromBlocks P X Xᴴ Q = H := by
    rw [← h21]
    exact fromBlocks_toBlocks H
  let S := Q - Xᴴ * P⁻¹ * X
  have hS : S.PosSemidef := (hPpos.fromBlocks₁₁ X Q).mp (hb.symm ▸ hH)
  have hd : H.det = P.det * S.det := by
    rw [← hb, det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  have hdA :
      (H.submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)).det =
        P.det * (S.submatrix Sum.inl Sum.inl).det := by
    rw [schur_submatrix P X Q Sum.inl]
    have h : H.submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl) =
        fromBlocks P (X.submatrix id Sum.inl) (X.submatrix id Sum.inl)ᴴ
          (Q.submatrix Sum.inl Sum.inl) := by
      rw [← hb]
      ext i j
      cases i <;> cases j <;> rfl
    rw [h, det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  have hdB :
      (H.submatrix (Sum.map id Sum.inr) (Sum.map id Sum.inr)).det =
        P.det * (S.submatrix Sum.inr Sum.inr).det := by
    rw [schur_submatrix P X Q Sum.inr]
    have h : H.submatrix (Sum.map id Sum.inr) (Sum.map id Sum.inr) =
        fromBlocks P (X.submatrix id Sum.inr) (X.submatrix id Sum.inr)ᴴ
          (Q.submatrix Sum.inr Sum.inr) := by
      rw [← hb]
      ext i j
      cases i <;> cases j <;> rfl
    rw [h, det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  have hf := fischer_psd S hS
  change P.det * H.det ≤ _
  rw [hdA, hdB, hd]
  nlinarith [mul_le_mul_of_nonneg_left hf (sq_nonneg P.det)]

/-- The volume of a common family times the volume of its two extensions is bounded
by the product of the volumes of the individual extensions. No independence is required. -/
private theorem shared_gram_volume_le {ι κ η : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype η] [DecidableEq η] (c : ι → E) (a : κ → E) (b : η → E) :
    Real.sqrt (gram ℝ c).det * Real.sqrt (gram ℝ (Sum.elim c (Sum.elim a b))).det ≤
      Real.sqrt (gram ℝ (Sum.elim c a)).det * Real.sqrt (gram ℝ (Sum.elim c b)).det := by
  have h := shared_det_le (gram ℝ (Sum.elim c (Sum.elim a b)))
    (posSemidef_gram ℝ _)
  have hc : (gram ℝ (Sum.elim c (Sum.elim a b))).submatrix Sum.inl Sum.inl =
      gram ℝ c := rfl
  have ha : (gram ℝ (Sum.elim c (Sum.elim a b))).submatrix
      (Sum.map id Sum.inl) (Sum.map id Sum.inl) = gram ℝ (Sum.elim c a) := by
    ext i j
    cases i <;> cases j <;> rfl
  have hb : (gram ℝ (Sum.elim c (Sum.elim a b))).submatrix
      (Sum.map id Sum.inr) (Sum.map id Sum.inr) = gram ℝ (Sum.elim c b) := by
    ext i j
    cases i <;> cases j <;> rfl
  rw [hc, ha, hb] at h
  rw [← Real.sqrt_mul (posSemidef_gram ℝ c).det_nonneg,
    ← Real.sqrt_mul (posSemidef_gram ℝ (Sum.elim c a)).det_nonneg]
  exact Real.sqrt_le_sqrt h

end D5.S3.Combinatorics.Lattices.EuclideanGram

namespace D5.S3.Combinatorics.Lattices.EuclideanSublattices

open Module Submodule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An integral submodule of a lattice, regarded in the ambient real vector space. -/
def ambient (L : Submodule ℤ E) (M : Submodule ℤ L) : Submodule ℤ E :=
  M.map L.subtype

/-- The real span of an integral submodule of a lattice. -/
def realSpan (L : Submodule ℤ E) (M : Submodule ℤ L) : Submodule ℝ E :=
  Submodule.span ℝ (ambient L M : Set E)

/-- Saturation consists exactly of lattice points in the real span. -/
def saturation (L : Submodule ℤ E) (M : Submodule ℤ L) : Submodule ℤ L :=
  ((realSpan L M).restrictScalars ℤ).comap L.subtype

/-- Real span is left adjoint to taking lattice points in a real subspace. -/
private def spanAdjunction (L : Submodule ℤ E) : GaloisConnection (realSpan L)
    (fun W : Submodule ℝ E => (W.restrictScalars ℤ).comap L.subtype) := by
  intro M W
  rw [realSpan, Submodule.span_le]
  change M.map L.subtype ≤ W.restrictScalars ℤ ↔ _
  exact Submodule.map_le_iff_le_comap

omit [NormedSpace ℝ E] in
private theorem ambient_le (L : Submodule ℤ E) (M : Submodule ℤ L) :
    ambient L M ≤ L := by
  rintro _ ⟨x, hx, rfl⟩
  exact x.property

private theorem realSpan_mono (L : Submodule ℤ E) : Monotone (realSpan L) := by
  intro M N hMN
  exact Submodule.span_mono (Submodule.map_mono hMN)

private theorem realSpan_saturation (L : Submodule ℤ E) (M : Submodule ℤ L) :
    realSpan L (saturation L M) = realSpan L M :=
  (spanAdjunction L).l_u_l_eq_l M

/-- Taking lattice points in a real span is an idempotent closure operation. -/
def closure (L : Submodule ℤ E) : ClosureOperator (Submodule ℤ L) :=
  (spanAdjunction L).closureOperator

/-- The saturated integral sublattices of the fixed ambient lattice. -/
abbrev Sublattice (L : Submodule ℤ E) := (closure L).Closeds

instance (L : Submodule ℤ E) : CompleteLattice (Sublattice L) :=
  (closure L).gi.liftCompleteLattice

/-- The ambient integral carrier of a saturated sublattice. -/
def integral (L : Submodule ℤ E) (M : Sublattice L) : Submodule ℤ E :=
  ambient L M.val

/-- The integer rank of a saturated sublattice. -/
private def rank (L : Submodule ℤ E) (M : Sublattice L) : ℤ :=
  (Module.finrank ℤ M.val : ℤ)

variable [FiniteDimensional ℝ E]

private instance ambient_discrete (L : Submodule ℤ E) [DiscreteTopology L]
    (M : Submodule ℤ L) : DiscreteTopology (ambient L M) :=
  DiscreteTopology.of_subset (inferInstance : DiscreteTopology L) (ambient_le L M)

instance integral_discrete (L : Submodule ℤ E) [DiscreteTopology L]
    (A : Sublattice L) : DiscreteTopology (integral L A) := ambient_discrete L A.val

private def spanLattice (N : Submodule ℤ E) :
    Submodule ℤ (Submodule.span ℝ (N : Set E)) :=
  N.comap ((Submodule.span ℝ (N : Set E)).subtype.restrictScalars ℤ)

private def spanLatticeEquiv (N : Submodule ℤ E) : spanLattice N ≃ₗ[ℤ] N :=
  Submodule.comapSubtypeEquivOfLe (show N ≤
    (Submodule.span ℝ (N : Set E)).restrictScalars ℤ from
      fun _ hx => Submodule.subset_span hx)

private instance spanLattice_discrete (N : Submodule ℤ E) [DiscreteTopology N] :
    DiscreteTopology (spanLattice N) :=
  ZLattice.comap_discreteTopology ℝ N
    (LinearMap.continuous_of_finiteDimensional _) (Submodule.injective_subtype _)

private instance spanLattice_isZLattice (N : Submodule ℤ E) [DiscreteTopology N] :
    IsZLattice ℝ (spanLattice N) := by
  refine ⟨?_⟩
  change Submodule.span ℝ
    (((↑) : Submodule.span ℝ (N : Set E) → E) ⁻¹' (N : Set E)) = ⊤
  exact Submodule.span_span_coe_preimage

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem ambient_rank_eq (L : Submodule ℤ E) (M : Submodule ℤ L) :
    Module.finrank ℤ M = Module.finrank ℤ (ambient L M) :=
  (Submodule.equivMapOfInjective L.subtype (Submodule.injective_subtype L) M).finrank_eq

theorem integral_rank_eq (L : Submodule ℤ E) [DiscreteTopology L]
    (M : Submodule ℤ L) :
    Module.finrank ℤ M = Module.finrank ℝ (realSpan L M) := by
  rw [ambient_rank_eq L M, ← (spanLatticeEquiv (ambient L M)).finrank_eq]
  exact ZLattice.rank ℝ (spanLattice (ambient L M))

private theorem saturation_rank_eq (L : Submodule ℤ E) [DiscreteTopology L]
    (M : Submodule ℤ L) :
    Module.finrank ℤ (saturation L M) = Module.finrank ℤ M := by
  rw [integral_rank_eq L (saturation L M), realSpan_saturation,
    ← integral_rank_eq L M]

private theorem rank_strictMono (L : Submodule ℤ E) [DiscreteTopology L] :
    StrictMono (rank L) := by
  intro M N hMN
  have hle : realSpan L M.val ≤ realSpan L N.val := realSpan_mono L hMN.le
  have hne : realSpan L M.val ≠ realSpan L N.val := by
    intro heq
    have hs : saturation L M.val = saturation L N.val := by
      simp only [saturation, heq]
    have hM := M.property.closure_eq
    have hN := N.property.closure_eq
    change saturation L M.val = M.val at hM
    change saturation L N.val = N.val at hN
    have hval : M.val = N.val := hM.symm.trans (hs.trans hN)
    exact hMN.ne (Subtype.ext hval)
  have hr := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle hne)
  rw [← integral_rank_eq L M.val, ← integral_rank_eq L N.val] at hr
  change (Module.finrank ℤ M.val : ℤ) < (Module.finrank ℤ N.val : ℤ)
  exact_mod_cast hr

private theorem rank_modular (L : Submodule ℤ E) [DiscreteTopology L]
    (M N : Sublattice L) : rank L (M ⊔ N) + rank L (M ⊓ N) = rank L M + rank L N := by
  have hcard := Submodule.rank_sup_add_rank_inf_eq M.val N.val
  have hnat : Module.finrank ℤ (M.val ⊔ N.val : Submodule ℤ L) +
      Module.finrank ℤ (M.val ⊓ N.val : Submodule ℤ L) =
      Module.finrank ℤ M.val + Module.finrank ℤ N.val := by
    have finiteRank (P : Submodule ℤ L) : Module.rank ℤ P < Cardinal.aleph0 :=
      (Submodule.rank_le P).trans_lt (Module.rank_lt_aleph0 ℤ L)
    have h := congrArg Cardinal.toNat hcard
    rw [Cardinal.toNat_add (finiteRank (M.val ⊔ N.val))
      (finiteRank (M.val ⊓ N.val)),
      Cardinal.toNat_add (finiteRank M.val) (finiteRank N.val)] at h
    exact h
  change (Module.finrank ℤ (saturation L (M.val ⊔ N.val)) : ℤ) +
    Module.finrank ℤ (M.val ⊓ N.val : Submodule ℤ L) =
    Module.finrank ℤ M.val + Module.finrank ℤ N.val
  rw [saturation_rank_eq]
  exact_mod_cast hnat

/-- The rank function with its strict order law and modular identity. -/
private structure Ranked (Λ : Type*) [Lattice Λ] where
  rank : Λ → ℤ
  strictMono : StrictMono rank
  modular : ∀ x y, rank (x ⊔ y) + rank (x ⊓ y) = rank x + rank y

/-- Real-span saturation supplies the ranked lattice used by slope filtrations. -/
private def rankData (L : Submodule ℤ E) [DiscreteTopology L] : Ranked (Sublattice L) where
  rank := rank L
  strictMono := rank_strictMono L
  modular := rank_modular L

end D5.S3.Combinatorics.Lattices.EuclideanSublattices

namespace D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan

open Module Matrix
open EuclideanSublattices hiding realSpan rank

section Gram

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem gram_linear_combination {ι κ : Type*} [Fintype ι]
    (v : ι → E) (T : Matrix ι κ ℝ) :
    gram ℝ (fun j => ∑ i, T i j • v i) = T.transpose * gram ℝ v * T := by
  ext j k
  simp only [gram_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    conj_trivial, Matrix.mul_apply, Matrix.transpose_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro l hl
  ring

private theorem gram_basis_change {ι κ : Type*} [Fintype ι]
    (M : Submodule ℤ E) (b : Basis ι ℤ M) (c : κ → M) :
    gram ℝ (fun i => (c i : E)) =
      ((b.toMatrix c).map (Int.castRingHom ℝ)).transpose *
        gram ℝ (fun i => (b i : E)) * (b.toMatrix c).map (Int.castRingHom ℝ) := by
  have hv (j : κ) :
      (c j : E) = ∑ i, ((b.toMatrix c) i j : ℝ) • (b i : E) := by
    simp only [Basis.toMatrix_apply, Int.cast_smul_eq_zsmul]
    simpa only [map_sum, map_smul, Submodule.subtype_apply] using
      congrArg M.subtype (b.sum_repr (c j)).symm
  conv_lhs => arg 2; ext j; rw [hv j]
  exact gram_linear_combination _ _

private theorem gram_det_cast {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℤ) : (T.map (Int.castRingHom ℝ)).det = (T.det : ℝ) := by
  exact ((Int.castRingHom ℝ).map_det T).symm

private theorem gram_det_basis_eq_same {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Submodule ℤ E) (b c : Basis ι ℤ M) :
    (gram ℝ (fun i => (b i : E))).det = (gram ℝ (fun i => (c i : E))).det := by
  have hu : IsUnit (b.toMatrix c).det := b.isUnit_det c
  have hsq : (((b.toMatrix c).det : ℤ) : ℝ) ^ 2 = 1 := by
    rcases Int.isUnit_iff.mp hu with h | h <;> simp [h]
  rw [gram_basis_change M b c, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  simp only [gram_det_cast]
  symm
  calc
    _ = (((b.toMatrix c).det : ℤ) : ℝ) ^ 2 *
        (gram ℝ (fun i => (b i : E))).det := by ring
    _ = _ := by rw [hsq, one_mul]

private theorem gram_det_basis_eq {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (M : Submodule ℤ E)
    (b : Basis ι ℤ M) (c : Basis κ ℤ M) :
    (gram ℝ (fun i => (b i : E))).det = (gram ℝ (fun i => (c i : E))).det := by
  let e := b.indexEquiv c
  calc
    _ = (gram ℝ (fun i => ((b.reindex e) i : E))).det := by
      trans ((gram ℝ (fun i => (b i : E))).submatrix e.symm e.symm).det
      · exact (Matrix.det_submatrix_equiv_self e.symm _).symm
      · congr 1
        ext i j
        simp only [Matrix.submatrix_apply, gram_apply, Basis.reindex_apply]
    _ = _ := gram_det_basis_eq_same M (b.reindex e) c

/-- Covolume is the square root of the Gram determinant of an integral basis. -/
def covolume (M : Submodule ℤ E) [Module.Free ℤ M] [Module.Finite ℤ M] : ℝ := by
  classical
  exact EuclideanGram.gramVolume (fun i => (Module.Free.chooseBasis ℤ M i : E))

private theorem covolume_congr (M N : Submodule ℤ E)
    [Module.Free ℤ M] [Module.Finite ℤ M] [Module.Free ℤ N] [Module.Finite ℤ N]
    (h : M = N) : covolume M = covolume N := by
  subst N
  rfl

/-- Any finite integral basis computes the same covolume, including rank zero. -/
theorem covolume_eq_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Submodule ℤ E) (b : Basis ι ℤ M) :
    @covolume E _ _ M (Module.Free.of_basis b) (Module.Finite.of_basis b) =
      Real.sqrt (gram ℝ (fun i => (b i : E))).det := by
  classical
  letI := Module.Free.of_basis b
  letI := Module.Finite.of_basis b
  exact congrArg Real.sqrt (gram_det_basis_eq M (Module.Free.chooseBasis ℤ M) b)

private theorem covolume_inclusion_factor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N : Submodule ℤ E) [Module.Free ℤ M] [Module.Finite ℤ M]
    [Module.Free ℤ N] [Module.Finite ℤ N] (hMN : M ≤ N)
    (b : Basis ι ℤ M) (c : Basis ι ℤ N) :
    covolume M =
      |((c.toMatrix (fun i => (⟨b i, hMN (b i).property⟩ : N))).det : ℝ)| *
        covolume N := by
  let v : ι → N := fun i => ⟨b i, hMN (b i).property⟩
  have hd := congrArg Matrix.det (gram_basis_change N c v)
  simp only [Matrix.det_mul, Matrix.det_transpose, gram_det_cast] at hd
  rw [covolume_eq_gram M b, covolume_eq_gram N c]
  change Real.sqrt (gram ℝ (fun i => (v i : E))).det = _
  rw [hd]
  have heq : ((c.toMatrix v).det : ℝ) * (gram ℝ (fun i => (c i : E))).det *
      ((c.toMatrix v).det : ℝ) =
      ((c.toMatrix v).det : ℝ) ^ 2 * (gram ℝ (fun i => (c i : E))).det := by ring
  rw [heq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

end Gram

section Discrete

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def realSpan (M : Submodule ℤ E) : Submodule ℝ E :=
  Submodule.span ℝ (M : Set E)

set_option backward.isDefEq.respectTransparency false in
private theorem basis_real_linearIndependent {ι : Type*}
    (M : Submodule ℤ E) [DiscreteTopology M] (b : Basis ι ℤ M) :
    LinearIndependent ℝ (fun i => (b i : E)) := by
  let b₀ := b.map (spanLatticeEquiv M).symm
  have hb := (b₀.ofZLatticeBasis ℝ).linearIndependent.map'
    (realSpan M).subtype (Submodule.ker_subtype _)
  have hfun : ((realSpan M).subtype ∘ (b₀.ofZLatticeBasis ℝ)) =
      (fun i => (b i : E)) := by
    funext i
    dsimp only [Function.comp_apply]
    rw [Basis.ofZLatticeBasis_apply]
    rfl
  exact (congrArg (fun f : ι → E => LinearIndependent ℝ f) hfun).mp hb

theorem covolume_pos (M : Submodule ℤ E) [DiscreteTopology M] :
    0 < covolume M := by
  classical
  rw [covolume]
  exact Real.sqrt_pos.mpr
    (Matrix.posDef_gram_of_linearIndependent
      (basis_real_linearIndependent M (Module.Free.chooseBasis ℤ M))).det_pos

theorem integral_rank_eq (M : Submodule ℤ E) [DiscreteTopology M] :
    Module.finrank ℤ M = Module.finrank ℝ (realSpan M) := by
  rw [← (spanLatticeEquiv M).finrank_eq]
  exact ZLattice.rank ℝ (spanLattice M)

set_option backward.isDefEq.respectTransparency false in
/-- Equal-span discrete inclusions have positive index and exact covolume ratio;
there is no covolume loss precisely when the two integral submodules coincide. -/
theorem covolume_index (M N : Submodule ℤ E)
    [DiscreteTopology N] (hMN : M ≤ N)
    (hspan : Submodule.span ℝ (M : Set E) = Submodule.span ℝ (N : Set E)) :
    letI : DiscreteTopology M :=
      DiscreteTopology.of_subset (inferInstance : DiscreteTopology N) hMN
    0 < M.toAddSubgroup.relIndex N.toAddSubgroup ∧
    covolume M = (M.toAddSubgroup.relIndex N.toAddSubgroup : ℝ) * covolume N ∧
    (covolume M = covolume N ↔ M = N) := by
  classical
  letI : DiscreteTopology M :=
    DiscreteTopology.of_subset (inferInstance : DiscreteTopology N) hMN
  have hr : Module.finrank ℤ M = Module.finrank ℤ N := by
    rw [integral_rank_eq M, integral_rank_eq N]
    exact congrArg (fun W : Submodule ℝ E => Module.finrank ℝ W) hspan
  let b := (Module.finBasis ℤ M).reindex (finCongr hr)
  let c := Module.finBasis ℤ N
  let v : Fin (Module.finrank ℤ N) → N := fun i => ⟨b i, hMN (b i).property⟩
  let z : ℤ := (c.toMatrix v).det
  have hf : covolume M = |(z : ℝ)| * covolume N :=
    covolume_inclusion_factor M N hMN b c
  have hz : z ≠ 0 := by
    intro hz
    have hp := covolume_pos M
    rw [hf, hz] at hp
    simpa using hp
  have hn : M.toAddSubgroup.relIndex N.toAddSubgroup = z.natAbs := by
    have h := AddSubgroup.relIndex_eq_natAbs_det M.toAddSubgroup N.toAddSubgroup hMN b c
    rw [Basis.det_apply] at h
    exact h
  have hcast : (M.toAddSubgroup.relIndex N.toAddSubgroup : ℝ) = |(z : ℝ)| := by
    rw [hn, Nat.cast_natAbs, Int.cast_abs]
  refine ⟨hn ▸ Int.natAbs_pos.mpr hz, hcast ▸ hf, ?_⟩
  constructor
  · intro heq
    have hone : (M.toAddSubgroup.relIndex N.toAddSubgroup : ℝ) = 1 := by
      rw [← hcast, heq] at hf
      nlinarith [covolume_pos N]
    have hnOne : M.toAddSubgroup.relIndex N.toAddSubgroup = 1 := by exact_mod_cast hone
    exact le_antisymm hMN (AddSubgroup.relIndex_eq_one.mp hnOne)
  · rintro rfl
    rfl

private theorem covolume_mono (M N : Submodule ℤ E)
    [DiscreteTopology M] [DiscreteTopology N] (hMN : M ≤ N)
    (hspan : realSpan M = realSpan N) : covolume N ≤ covolume M := by
  have h := covolume_index M N hMN hspan
  rw [h.2.1]
  have hn : (1 : ℝ) ≤ M.toAddSubgroup.relIndex N.toAddSubgroup := by
    exact_mod_cast h.1
  exact le_mul_of_one_le_left (covolume_pos N).le hn

private theorem covolume_sum_le (L A B : Submodule ℤ E)
    [DiscreteTopology A] [DiscreteTopology B]
    [DiscreteTopology (A ⊓ B : Submodule ℤ E)]
    [DiscreteTopology (A ⊔ B : Submodule ℤ E)]
    (hAL : A ≤ L) (hBL : B ≤ L)
    (hA : ∀ x : E, x ∈ L → x ∈ realSpan A → x ∈ A)
    (hB : ∀ x : E, x ∈ L → x ∈ realSpan B → x ∈ B) :
    covolume (A ⊓ B) * covolume (A ⊔ B) ≤ covolume A * covolume B := by
  classical
  let c := Module.Free.chooseBasis ℤ (A ⊓ B : Submodule ℤ E)
  let d := EuclideanSaturation.adaptedBasesOfSaturated (K := ℝ) L A B hAL hBL hA hB c
  let cv := fun i => (c i : E)
  let av := fun i => (d.a (Sum.inr i) : E)
  let bv := fun i => (d.b (Sum.inr i) : E)
  have ha : (fun i => (d.a i : E)) = Sum.elim cv av := by
    funext i
    cases i with
    | inl i => exact d.a_left i
    | inr i => rfl
  have hb : (fun i => (d.b i : E)) = Sum.elim cv bv := by
    funext i
    cases i with
    | inl i => exact d.b_left i
    | inr i => rfl
  have ht : (fun i => (d.total i : E)) = Sum.elim cv (Sum.elim av bv) := by
    funext i
    cases i with
    | inl i => exact d.total_left i
    | inr i =>
      cases i with
      | inl i => exact d.total_a i
      | inr i => exact d.total_b i
  rw [covolume_eq_gram _ c, covolume_eq_gram _ d.total,
    covolume_eq_gram _ d.a, covolume_eq_gram _ d.b, ha, hb, ht]
  exact EuclideanGram.shared_gram_volume_le cv av bv

omit [FiniteDimensional ℝ E] in
theorem integral_le (L : Submodule ℤ E) (A : Sublattice L) : integral L A ≤ L := by
  rintro _ ⟨x, hx, rfl⟩
  exact x.property

omit [FiniteDimensional ℝ E] in
theorem integral_saturated (L : Submodule ℤ E) (A : Sublattice L)
    (x : E) (hxL : x ∈ L) (hx : x ∈ realSpan (integral L A)) : x ∈ integral L A := by
  have hy : (⟨x, hxL⟩ : L) ∈ saturation L A.val := hx
  have hA := A.property.closure_eq
  change saturation L A.val = A.val at hA
  rw [hA] at hy
  exact Submodule.mem_map.mpr ⟨⟨x, hxL⟩, hy, rfl⟩

omit [FiniteDimensional ℝ E] in
private theorem integral_inf (L : Submodule ℤ E) (A B : Sublattice L) :
    integral L (A ⊓ B) = integral L A ⊓ integral L B :=
  Submodule.map_inf L.subtype (Submodule.injective_subtype L)

/-- The ordinary sum of the two integral carriers, before saturation. -/
def integralSum (L : Submodule ℤ E) (A B : Sublattice L) : Submodule ℤ E :=
  ambient L (A.val ⊔ B.val)

instance integralSum_discrete (L : Submodule ℤ E) [DiscreteTopology L]
    (A B : Sublattice L) : DiscreteTopology (integralSum L A B) :=
  ambient_discrete L (A.val ⊔ B.val)

/-- The index of the ordinary integral sum in its saturated join. -/
def saturationIndex (L : Submodule ℤ E) (A B : Sublattice L) : ℕ :=
  (integral L A ⊔ integral L B).toAddSubgroup.relIndex
    (integral L (A ⊔ B)).toAddSubgroup

omit [FiniteDimensional ℝ E] in
private theorem saturated_sum_span (L : Submodule ℤ E) (A B : Sublattice L) :
    let S := integral L A ⊔ integral L B
    let J := integral L (A ⊔ B)
    S ≤ J ∧ realSpan S = realSpan J := by
  let U := integral L A
  let V := integral L B
  have hin : U ⊔ V ≤ integral L (A ⊔ B) := by
    change A.val.map L.subtype ⊔ B.val.map L.subtype ≤
      (saturation L (A.val ⊔ B.val)).map L.subtype
    rw [← Submodule.map_sup]
    exact Submodule.map_mono ((EuclideanSublattices.closure L).le_closure _)
  have hspan : realSpan (U ⊔ V) = realSpan (integral L (A ⊔ B)) := by
    change Submodule.span ℝ
      ((A.val.map L.subtype ⊔ B.val.map L.subtype : Submodule ℤ E) : Set E) =
      EuclideanSublattices.realSpan L (saturation L (A.val ⊔ B.val))
    rw [← Submodule.map_sup]
    exact ((spanAdjunction L).l_u_l_eq_l (A.val ⊔ B.val)).symm
  exact ⟨hin, hspan⟩

/-- The saturation index is positive, gives the exact covolume ratio, and
covolume equality characterizes an already saturated sum. -/
private theorem covolume_saturation (L : Submodule ℤ E) [DiscreteTopology L]
    (A B : Sublattice L) :
    0 < saturationIndex L A B ∧
    covolume (integralSum L A B) =
      (saturationIndex L A B : ℝ) * covolume (integral L (A ⊔ B)) ∧
    (covolume (integralSum L A B) = covolume (integral L (A ⊔ B)) ↔
      integralSum L A B = integral L (A ⊔ B)) := by
  have hs := saturated_sum_span L A B
  have hS : integralSum L A B = integral L A ⊔ integral L B :=
    Submodule.map_sup _ _ _
  have hin : integralSum L A B ≤ integral L (A ⊔ B) := hS ▸ hs.1
  have hspan : realSpan (integralSum L A B) = realSpan (integral L (A ⊔ B)) :=
    hS ▸ hs.2
  simpa only [saturationIndex, ← hS] using
    covolume_index (integralSum L A B) (integral L (A ⊔ B)) hin hspan

private theorem covolume_index_bound (L : Submodule ℤ E) [DiscreteTopology L]
    (A B : Sublattice L) :
    (saturationIndex L A B : ℝ) * covolume (integral L (A ⊓ B)) *
      covolume (integral L (A ⊔ B)) ≤
        covolume (integral L A) * covolume (integral L B) := by
  classical
  let U := integral L A
  let V := integral L B
  have hUL : U ≤ L := integral_le L A
  have hVL : V ≤ L := integral_le L B
  letI : DiscreteTopology (U ⊓ V : Submodule ℤ E) :=
    DiscreteTopology.of_subset (inferInstance : DiscreteTopology L)
      (inf_le_left.trans hUL)
  letI : DiscreteTopology (U ⊔ V : Submodule ℤ E) :=
    DiscreteTopology.of_subset (inferInstance : DiscreteTopology L) (sup_le hUL hVL)
  have hsum := covolume_sum_le L U V hUL hVL
    (integral_saturated L A) (integral_saturated L B)
  have hf := (covolume_saturation L A B).2.1
  have hS : integralSum L A B = U ⊔ V := Submodule.map_sup _ _ _
  rw [covolume_congr _ _ hS] at hf
  rw [hf] at hsum
  simpa only [saturationIndex, integral_inf, mul_left_comm, mul_assoc] using hsum

private theorem covolume_supermodular (L : Submodule ℤ E) [DiscreteTopology L]
    (A B : Sublattice L) :
    covolume (integral L (A ⊓ B)) * covolume (integral L (A ⊔ B)) ≤
      covolume (integral L A) * covolume (integral L B) := by
  have hs := saturated_sum_span L A B
  let S := integral L A ⊔ integral L B
  letI : DiscreteTopology S := DiscreteTopology.of_subset
    (inferInstance : DiscreteTopology (integral L (A ⊔ B))) hs.1
  have hm := covolume_mono S (integral L (A ⊔ B)) hs.1 hs.2
  have hf := (covolume_index S (integral L (A ⊔ B)) hs.1 hs.2).2.1
  have h := covolume_index_bound L A B
  change covolume S = (saturationIndex L A B : ℝ) * _ at hf
  rw [hf] at hm
  nlinarith [mul_le_mul_of_nonneg_left hm (covolume_pos (integral L (A ⊓ B))).le]

/-- The degree of a saturated sublattice is minus the logarithm of its Gram covolume. -/
def degree (L : Submodule ℤ E) [DiscreteTopology L] (A : Sublattice L) : ℝ :=
  -Real.log (covolume (integral L A))

private theorem degree_supermodular (L : Submodule ℤ E) [DiscreteTopology L]
    (A B : Sublattice L) : degree L A + degree L B ≤ degree L (A ⊔ B) + degree L (A ⊓ B) := by
  have hprod := covolume_supermodular L A B
  have hpos₁ := covolume_pos (integral L (A ⊓ B))
  have hpos₂ := covolume_pos (integral L (A ⊔ B))
  have hpos₃ := covolume_pos (integral L A)
  have hpos₄ := covolume_pos (integral L B)
  have hlog := Real.log_le_log (mul_pos hpos₁ hpos₂) hprod
  rw [Real.log_mul hpos₁.ne' hpos₂.ne', Real.log_mul hpos₃.ne' hpos₄.ne'] at hlog
  dsimp [degree]
  linarith

/-- The slope datum is constructed from the Gram determinant, without covolume axioms. -/
def slopeData (L : Submodule ℤ E) [DiscreteTopology L] :
    HarderNarasimhan.SlopeData (Sublattice L) where
  rank := (rankData L).rank
  rank_strictMono := (rankData L).strictMono
  rank_modular := (rankData L).modular
  degree := degree L
  degree_supermodular := degree_supermodular L

/-- Gram covolumes are submultiplicative on saturated joins; the resulting HN chain
is unique and its endpoint slopes are exactly the subobject and quotient extrema. -/
theorem euclidean_hn (L : Submodule ℤ E) [DiscreteTopology L] (A B : Sublattice L) :
    (saturationIndex L A B : ℝ) * covolume (integral L (A ⊓ B)) *
      covolume (integral L (A ⊔ B)) ≤
        covolume (integral L A) * covolume (integral L B) ∧
    ((∃! l, (slopeData L).Filtration A B l) ↔ A ≤ B) ∧
    ∀ e l, (slopeData L).Filtration A B (e :: l) →
      let D := slopeData L
      let q := HarderNarasimhan.lastLower A (e :: l)
      A ≤ q ∧ q < B ∧
        IsGreatest {s | ∃ x, A < x ∧ x ≤ B ∧ D.slope A x = s} (D.slope A e) ∧
        IsLeast {s | ∃ x, A ≤ x ∧ x < B ∧ D.slope x B = s} (D.slope q B) ∧
        D.muMax A B = D.slope A e ∧ D.muMin A B = D.slope q B ∧
        D.Destabilizer A B e ∧ D.slope q B ≤ D.slope A e ∧
        (D.Semistable A B ↔ l = []) ∧
        (D.muMin A B = D.muMax A B ↔ D.Semistable A B) ∧
        (l ≠ [] → D.slope q B < D.slope A e) := by
  refine ⟨covolume_index_bound L A B,
    HarderNarasimhan.exists_unique_filtration (slopeData L) A B, ?_⟩
  intro e l h
  exact HarderNarasimhan.filtration_extremes (slopeData L) A B e l h

end Discrete

end D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan
