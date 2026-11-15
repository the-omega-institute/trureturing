/- GID: D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Tensor ranks and the sufficient partial-transpose saturation criterion. -/

/-
proof_shape: tensorSum_range_of_jointSurjective: content; consumer=rank_tensorSum_of_jointSurjective.
proof_shape: tensorSum_eq_zero_iff: bind-only; consumer=Regularity.tensor_eq_zero_iff_of_independent_right.
proof_shape: the six rank and saturation conclusions inherit content through
  tensorSum_range_of_jointSurjective when same-delivery helpers are inlined.
proof_shape: coordinate and invariance helpers are consumed bind-only declarations.
escape_witness: tensorSum_range_of_jointSurjective constructs independent pure-tensor preimages.
admission_basis: escape-witness
Direct frozen dependency: MRDDensityColumnTensor.MRDDensityTensor.rectangle_finrank.
Protected baseline statement_id: sha256:3d6cf4bbf1b65e4ba690556cee57d6eb93a98c0e46cd85602a58a0fa2a6d1e95.
This module proves the sufficient direction; it does not assert the full classification.
-/

import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor
import Mathlib.LinearAlgebra.TensorProduct.Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Quantum.Entanglement.PartialTransposeSaturation

open Matrix
open scoped Kronecker

variable {m n p q : Type*}

/-- The two-term tensor sum, with the first factor first in each product index. -/
def tensorSum (A₁ A₂ : Matrix m n ℂ) (B₁ B₂ : Matrix p q ℂ) :
    Matrix (m × p) (n × q) ℂ := A₁ ⊗ₖ B₁ + A₂ ⊗ₖ B₂

/-- Partial transpose on the first factor, also for rectangular matrices. -/
def partialTranspose (A₁ A₂ : Matrix m n ℂ) (B₁ B₂ : Matrix p q ℂ) :
    Matrix (n × p) (m × q) ℂ := tensorSum A₁ᵀ A₂ᵀ B₁ B₂

/-- Rank of horizontal concatenation. -/
def hRank [Fintype n] (A₁ A₂ : Matrix m n ℂ) : ℕ :=
  (Matrix.fromCols A₁ A₂).rank

/-- Rank of vertical concatenation. -/
def vRank [Fintype n] (A₁ A₂ : Matrix m n ℂ) : ℕ :=
  (Matrix.fromRows A₁ A₂).rank

private theorem hRank_transpose [Fintype m] [Fintype n] (A₁ A₂ : Matrix m n ℂ) :
    hRank A₁ᵀ A₂ᵀ = vRank A₁ A₂ := by
  rw [hRank, vRank, ← Matrix.transpose_fromRows, Matrix.rank_transpose]

private theorem vRank_transpose [Fintype m] [Fintype n] (A₁ A₂ : Matrix m n ℂ) :
    vRank A₁ᵀ A₂ᵀ = hRank A₁ A₂ := by
  rw [vRank, hRank, ← Matrix.transpose_fromCols, Matrix.rank_transpose]

/-- Independence of either coefficient pair rules out a zero tensor sum unless
the other pair is zero. This includes empty and rectangular index types. -/
theorem tensorSum_eq_zero_iff (A₁ A₂ : Matrix m n ℂ) (B₁ B₂ : Matrix p q ℂ)
    (hA : LinearIndependent ℂ ![A₁, A₂]) :
    tensorSum A₁ A₂ B₁ B₂ = 0 ↔ B₁ = 0 ∧ B₂ = 0 := by
  constructor
  · intro h
    have hc (k : p) (l : q) : B₁ k l = 0 ∧ B₂ k l = 0 := by
      have he : B₁ k l • A₁ + B₂ k l • A₂ = 0 := by
        ext i j
        have hh := congrFun (congrFun h (i, k)) (j, l)
        simpa [tensorSum, Matrix.kroneckerMap_apply, mul_comm] using hh
      have hz := Fintype.linearIndependent_iff.mp hA ![B₁ k l, B₂ k l]
        (by simpa [Fin.sum_univ_two] using he)
      exact ⟨by simpa using hz 0, by simpa using hz 1⟩
    exact ⟨Matrix.ext fun k l => (hc k l).1, Matrix.ext fun k l => (hc k l).2⟩
  · rintro ⟨rfl, rfl⟩
    simp [tensorSum]

section Invariance

variable [Fintype m] [Fintype n] [Fintype p] [Fintype q]
  [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]

/-- Independent row and column changes act on the tensor sum by Kronecker
products of the same changes. -/
private theorem tensorSum_change (A₁ A₂ : Matrix m n ℂ) (B₁ B₂ : Matrix p q ℂ)
    (P : Matrix m m ℂ) (Q : Matrix n n ℂ)
    (R : Matrix p p ℂ) (S : Matrix q q ℂ) :
    tensorSum (P * A₁ * Q) (P * A₂ * Q) (R * B₁ * S) (R * B₂ * S) =
      (P ⊗ₖ R) * tensorSum A₁ A₂ B₁ B₂ * (Q ⊗ₖ S) := by
  simp only [tensorSum, Matrix.mul_kronecker_mul, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_assoc]

theorem rank_tensorSum_change (A₁ A₂ : Matrix m n ℂ) (B₁ B₂ : Matrix p q ℂ)
    (P : Matrix m m ℂ) (Q : Matrix n n ℂ)
    (R : Matrix p p ℂ) (S : Matrix q q ℂ)
    (hP : IsUnit P.det) (hQ : IsUnit Q.det)
    (hR : IsUnit R.det) (hS : IsUnit S.det) :
    (tensorSum (P * A₁ * Q) (P * A₂ * Q)
      (R * B₁ * S) (R * B₂ * S)).rank = (tensorSum A₁ A₂ B₁ B₂).rank := by
  rw [tensorSum_change, Matrix.rank_mul_eq_left_of_isUnit_det,
    Matrix.rank_mul_eq_right_of_isUnit_det]
  · rw [Matrix.det_kronecker]
    exact (hP.pow _).mul (hR.pow _)
  · rw [Matrix.det_kronecker]
    exact (hQ.pow _).mul (hS.pow _)

end Invariance

end D5.S3.Quantum.Entanglement.PartialTransposeSaturation

end

noncomputable section

namespace D5.S3.Quantum.Entanglement.PartialTransposeSaturation

open Matrix Module

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Horizontal concatenation has precisely the sum of the two column images. -/
private theorem hRank_eq_finrank_sup (A₁ A₂ : Matrix m n ℂ) :
    hRank A₁ A₂ = finrank ℂ ↥(LinearMap.range A₁.mulVecLin ⊔
      LinearMap.range A₂.mulVecLin) := by
  unfold hRank Matrix.rank
  apply congrArg (fun W : Submodule ℂ (m → ℂ) => finrank ℂ W)
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.fromCols_mulVec]
    exact Submodule.add_mem _
      ((show LinearMap.range A₁.mulVecLin ≤
        LinearMap.range A₁.mulVecLin ⊔ LinearMap.range A₂.mulVecLin from le_sup_left)
        ⟨x ∘ Sum.inl, rfl⟩)
      ((show LinearMap.range A₂.mulVecLin ≤
        LinearMap.range A₁.mulVecLin ⊔ LinearMap.range A₂.mulVecLin from le_sup_right)
        ⟨x ∘ Sum.inr, rfl⟩)
  · apply sup_le
    · rintro _ ⟨x, rfl⟩
      refine ⟨Sum.elim x 0, ?_⟩
      simp [Matrix.mulVecLin_apply, Matrix.fromCols_mulVec_sumElim]
    · rintro _ ⟨x, rfl⟩
      refine ⟨Sum.elim 0 x, ?_⟩
      simp [Matrix.mulVecLin_apply, Matrix.fromCols_mulVec_sumElim]

/-- Vertical concatenation records the joint image of the two coefficient maps. -/
private theorem vRank_eq_finrank_prod (A₁ A₂ : Matrix m n ℂ) :
    vRank A₁ A₂ = finrank ℂ (LinearMap.range (A₁.mulVecLin.prod A₂.mulVecLin)) := by
  let e := LinearEquiv.sumArrowLequivProdArrow m m ℂ ℂ
  have he : e.toLinearMap.comp (Matrix.fromRows A₁ A₂).mulVecLin =
      A₁.mulVecLin.prod A₂.mulVecLin := by
    ext x <;> rfl
  rw [← he, LinearMap.range_comp, e.finrank_map_eq]
  rfl

/-- Equality in the concatenation bound is equivalent to simultaneous,
independent prescription of both outputs in their common image sum. -/
theorem joint_control_iff (A₁ A₂ : Matrix m n ℂ) :
    vRank A₁ A₂ = 2 * hRank A₁ A₂ ↔
      ∀ y₁ ∈ LinearMap.range A₁.mulVecLin ⊔ LinearMap.range A₂.mulVecLin,
        ∀ y₂ ∈ LinearMap.range A₁.mulVecLin ⊔ LinearMap.range A₂.mulVecLin,
          ∃ x, A₁.mulVecLin x = y₁ ∧ A₂.mulVecLin x = y₂ := by
  let H := LinearMap.range A₁.mulVecLin ⊔ LinearMap.range A₂.mulVecLin
  have hle : LinearMap.range (A₁.mulVecLin.prod A₂.mulVecLin) ≤ H.prod H := by
    rintro _ ⟨x, rfl⟩
    exact ⟨(show LinearMap.range A₁.mulVecLin ≤ H from le_sup_left) ⟨x, rfl⟩,
      (show LinearMap.range A₂.mulVecLin ≤ H from le_sup_right) ⟨x, rfl⟩⟩
  have hd : finrank ℂ (H.prod H) = 2 * finrank ℂ H := by
    rw [(Submodule.prodEquiv H H).finrank_eq, Module.finrank_prod]
    omega
  rw [vRank_eq_finrank_prod, hRank_eq_finrank_sup]
  constructor
  · intro h y₁ hy₁ y₂ hy₂
    have he : LinearMap.range (A₁.mulVecLin.prod A₂.mulVecLin) = H.prod H :=
      Submodule.eq_of_le_of_finrank_eq hle (h.trans hd.symm)
    have hm : (y₁, y₂) ∈ LinearMap.range (A₁.mulVecLin.prod A₂.mulVecLin) :=
      he.symm ▸ (show (y₁, y₂) ∈ H.prod H from ⟨hy₁, hy₂⟩)
    obtain ⟨x, hx⟩ := hm
    exact ⟨x, congrArg Prod.fst hx, congrArg Prod.snd hx⟩
  · intro h
    have he : LinearMap.range (A₁.mulVecLin.prod A₂.mulVecLin) = H.prod H := by
      apply le_antisymm hle
      rintro ⟨y₁, y₂⟩ ⟨hy₁, hy₂⟩
      obtain ⟨x, hx₁, hx₂⟩ := h y₁ hy₁ y₂ hy₂
      exact ⟨x, Prod.ext hx₁ hx₂⟩
    rw [he, hd]

end D5.S3.Quantum.Entanglement.PartialTransposeSaturation

end

noncomputable section

namespace D5.S3.Quantum.Entanglement.PartialTransposeSaturation

open Matrix Module
open scoped Kronecker TensorProduct

section Abstract

variable {K U V U' V' : Type*} [Field K]
  [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  [AddCommGroup U'] [Module K U'] [AddCommGroup V'] [Module K V']

/-- Independent control of the second coefficient pair makes the tensor-sum
range the full tensor rectangle of the two combined ranges. -/
private theorem tensorSum_range_of_jointSurjective
    (f₁ f₂ : U →ₗ[K] V) (g₁ g₂ : U' →ₗ[K] V')
    (h : ∀ y₁ ∈ LinearMap.range g₁ ⊔ LinearMap.range g₂,
      ∀ y₂ ∈ LinearMap.range g₁ ⊔ LinearMap.range g₂,
      ∃ x, g₁ x = y₁ ∧ g₂ x = y₂) :
    LinearMap.range (TensorProduct.map f₁ g₁ + TensorProduct.map f₂ g₂) =
      Submodule.map₂ (TensorProduct.mk K V V')
        (LinearMap.range f₁ ⊔ LinearMap.range f₂)
        (LinearMap.range g₁ ⊔ LinearMap.range g₂) := by
  apply le_antisymm
  · refine (LinearMap.range_add_le _ _).trans ?_
    rw [TensorProduct.range_map, TensorProduct.range_map]
    exact sup_le (Submodule.map₂_le_map₂ le_sup_left le_sup_left)
      (Submodule.map₂_le_map₂ le_sup_right le_sup_right)
  · rw [Submodule.map₂_sup_left]
    apply sup_le
    · apply Submodule.map₂_le.mpr
      rintro _ ⟨x, rfl⟩ y hy
      obtain ⟨z, hz₁, hz₂⟩ := h y hy 0 (Submodule.zero_mem _)
      refine ⟨x ⊗ₜ[K] z, ?_⟩
      simp only [LinearMap.add_apply, TensorProduct.map_tmul, hz₁, hz₂,
        TensorProduct.tmul_zero, add_zero]
      rfl
    · apply Submodule.map₂_le.mpr
      rintro _ ⟨x, rfl⟩ y hy
      obtain ⟨z, hz₁, hz₂⟩ := h 0 (Submodule.zero_mem _) y hy
      refine ⟨x ⊗ₜ[K] z, ?_⟩
      simp only [LinearMap.add_apply, TensorProduct.map_tmul, hz₁, hz₂,
        TensorProduct.tmul_zero, zero_add]
      rfl

end Abstract

variable {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
  [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]

/-- A coefficient pair that independently controls its combined image gives an
exact product formula for the rank of every two-term tensor sum. -/
theorem rank_tensorSum_of_jointSurjective
    (A₁ A₂ : Matrix m n ℂ) (B₁ B₂ : Matrix p q ℂ)
    (hB : ∀ y₁ ∈ LinearMap.range B₁.mulVecLin ⊔ LinearMap.range B₂.mulVecLin,
      ∀ y₂ ∈ LinearMap.range B₁.mulVecLin ⊔ LinearMap.range B₂.mulVecLin,
      ∃ x, B₁.mulVecLin x = y₁ ∧ B₂.mulVecLin x = y₂) :
    (tensorSum A₁ A₂ B₁ B₂).rank =
      finrank ℂ ↥(LinearMap.range A₁.mulVecLin ⊔ LinearMap.range A₂.mulVecLin) *
      finrank ℂ ↥(LinearMap.range B₁.mulVecLin ⊔ LinearMap.range B₂.mulVecLin) := by
  rw [tensorSum, rank_eq_finrank_range_toLin _
    ((Pi.basisFun ℂ m).tensorProduct (Pi.basisFun ℂ p))
    ((Pi.basisFun ℂ n).tensorProduct (Pi.basisFun ℂ q)), map_add,
    Matrix.toLin_kronecker, Matrix.toLin_kronecker]
  change finrank ℂ ↥(LinearMap.range
    (TensorProduct.map A₁.mulVecLin B₁.mulVecLin +
      TensorProduct.map A₂.mulVecLin B₂.mulVecLin)) = _
  exact (congrArg
    (fun H : Submodule ℂ ((m → ℂ) ⊗[ℂ] (p → ℂ)) => finrank ℂ H)
    (tensorSum_range_of_jointSurjective _ _ _ _ hB)).trans
      (D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor.rectangle_finrank
        (LinearMap.range A₁.mulVecLin ⊔ LinearMap.range A₂.mulVecLin)
        (LinearMap.range B₁.mulVecLin ⊔ LinearMap.range B₂.mulVecLin))

/-- A vertically saturated second pair determines the untransposed rank even
without a saturation assumption on the first pair. -/
theorem rank_tensorSum_of_vertical_saturated
    (A₁ A₂ : Matrix m n ℂ) (B₁ B₂ : Matrix p q ℂ)
    (hB : vRank B₁ B₂ = 2 * hRank B₁ B₂) :
    (tensorSum A₁ A₂ B₁ B₂).rank = hRank A₁ A₂ * hRank B₁ B₂ := by
  simpa only [hRank_eq_finrank_sup] using
    rank_tensorSum_of_jointSurjective A₁ A₂ B₁ B₂
      ((joint_control_iff B₁ B₂).mp hB)

/-- The same one-sided hypothesis gives the exact partially transposed rank. -/
theorem rank_partialTranspose_of_vertical_saturated
    (A₁ A₂ : Matrix m n ℂ) (B₁ B₂ : Matrix p q ℂ)
    (hB : vRank B₁ B₂ = 2 * hRank B₁ B₂) :
    (partialTranspose A₁ A₂ B₁ B₂).rank = vRank A₁ A₂ * hRank B₁ B₂ := by
  simpa only [partialTranspose, hRank_transpose] using
    rank_tensorSum_of_vertical_saturated A₁ᵀ A₂ᵀ B₁ B₂ hB

/-- Both vertical concatenation equalities imply partial-transpose saturation. -/
theorem saturation_of_vertical
    (A₁ A₂ : Matrix m n ℂ) (B₁ B₂ : Matrix p q ℂ)
    (hA : vRank A₁ A₂ = 2 * hRank A₁ A₂)
    (hB : vRank B₁ B₂ = 2 * hRank B₁ B₂) :
    (partialTranspose A₁ A₂ B₁ B₂).rank =
      2 * (tensorSum A₁ A₂ B₁ B₂).rank := by
  rw [rank_partialTranspose_of_vertical_saturated A₁ A₂ B₁ B₂ hB,
    rank_tensorSum_of_vertical_saturated A₁ A₂ B₁ B₂ hB, hA, Nat.mul_assoc]

/-- Both horizontal concatenation equalities imply the other saturation family. -/
theorem saturation_of_horizontal
    (A₁ A₂ : Matrix m n ℂ) (B₁ B₂ : Matrix p q ℂ)
    (hA : hRank A₁ A₂ = 2 * vRank A₁ A₂)
    (hB : hRank B₁ B₂ = 2 * vRank B₁ B₂) :
    (partialTranspose A₁ A₂ B₁ B₂).rank =
      2 * (tensorSum A₁ A₂ B₁ B₂).rank := by
  have ht := saturation_of_vertical A₁ᵀ A₂ᵀ B₁ᵀ B₂ᵀ
    (by simpa only [hRank_transpose, vRank_transpose] using hA)
    (by simpa only [hRank_transpose, vRank_transpose] using hB)
  have hX : tensorSum A₁ᵀ A₂ᵀ B₁ᵀ B₂ᵀ =
      (tensorSum A₁ A₂ B₁ B₂)ᵀ := by
    simp only [tensorSum, Matrix.kroneckerMap_transpose, Matrix.transpose_add]
  have hPT : partialTranspose A₁ᵀ A₂ᵀ B₁ᵀ B₂ᵀ =
      (partialTranspose A₁ A₂ B₁ B₂)ᵀ := by
    simp only [partialTranspose, tensorSum, Matrix.transpose_transpose,
      Matrix.transpose_add, ← Matrix.kroneckerMap_transpose]
  simpa only [hX, hPT, Matrix.rank_transpose] using ht

/-- The proposed concatenation test is sufficient in every finite rectangular
dimension; linear independence is not needed for this direction. -/
theorem sufficient
    (A₁ A₂ : Matrix m n ℂ) (B₁ B₂ : Matrix p q ℂ)
    (h : (vRank A₁ A₂ = 2 * hRank A₁ A₂ ∧
        vRank B₁ B₂ = 2 * hRank B₁ B₂) ∨
      (hRank A₁ A₂ = 2 * vRank A₁ A₂ ∧
        hRank B₁ B₂ = 2 * vRank B₁ B₂)) :
    (partialTranspose A₁ A₂ B₁ B₂).rank =
      2 * (tensorSum A₁ A₂ B₁ B₂).rank := by
  rcases h with ⟨hA, hB⟩ | ⟨hA, hB⟩
  · exact saturation_of_vertical A₁ A₂ B₁ B₂ hA hB
  · exact saturation_of_horizontal A₁ A₂ B₁ B₂ hA hB

section CoordinateRank

variable {U V U' V' : Type*} [AddCommGroup U] [Module ℂ U]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup U'] [Module ℂ U']
  [AddCommGroup V'] [Module ℂ V']
  {a b c d : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
  [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq d]

/-- Coordinate rank of a tensor sum, with no choice-of-basis assumption hidden
in the use of the matrix rank formulas. -/
theorem finrank_tensorSum_toMatrix (bu : Basis a ℂ U) (bv : Basis b ℂ V)
    (bu' : Basis c ℂ U') (bv' : Basis d ℂ V')
    (f₁ f₂ : U →ₗ[ℂ] V) (g₁ g₂ : U' →ₗ[ℂ] V') :
    finrank ℂ (LinearMap.range (TensorProduct.map f₁ g₁ + TensorProduct.map f₂ g₂)) =
      (tensorSum (LinearMap.toMatrix bu bv f₁) (LinearMap.toMatrix bu bv f₂)
        (LinearMap.toMatrix bu' bv' g₁) (LinearMap.toMatrix bu' bv' g₂)).rank := by
  have he : LinearMap.toMatrix (bu.tensorProduct bu') (bv.tensorProduct bv')
      (TensorProduct.map f₁ g₁ + TensorProduct.map f₂ g₂) =
      tensorSum (LinearMap.toMatrix bu bv f₁) (LinearMap.toMatrix bu bv f₂)
        (LinearMap.toMatrix bu' bv' g₁) (LinearMap.toMatrix bu' bv' g₂) := by
    simp only [map_add, TensorProduct.toMatrix_map, tensorSum]
  rw [← he, Matrix.rank_eq_finrank_range_toLin _ (bv.tensorProduct bv')
    (bu.tensorProduct bu'), Matrix.toLin_toMatrix]

end CoordinateRank

end D5.S3.Quantum.Entanglement.PartialTransposeSaturation

end
