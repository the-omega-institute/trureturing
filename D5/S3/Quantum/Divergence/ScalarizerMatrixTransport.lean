/- GID: D5/S3/Quantum/Divergence/ScalarizerMatrixTransport
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/ScalarizerMatrixTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rectangular Euclidean matrix transports for the common positive-state scalarizer. -/

import D5.S3.HilbertOperators.DouglasLemma
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic

/-! Matrix transports used by UniversalPositiveScalarizer. The rectangular
factor is extracted from the existing Douglas theorem on a Hilbert direct sum.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder
open Matrix

namespace D5.S3.Quantum.Divergence.ScalarizerMatrixTransport

def matrixCLM {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (M : Matrix m n ℂ) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ m :=
  (Matrix.toEuclideanLin M).toContinuousLinearMap

private def padLeft {m p q : Type*} (D : Matrix m p ℂ) : Matrix m (Sum p q) ℂ :=
  fun i j => match j with | Sum.inl p' => D i p' | Sum.inr _ => 0

private def padRight {m p q : Type*} (C : Matrix m q ℂ) : Matrix m (Sum p q) ℂ :=
  fun i j => match j with | Sum.inl _ => 0 | Sum.inr q' => C i q'

private lemma padLeft_mulVec {m p q : Type*} [Fintype m] [DecidableEq m]
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    (D : Matrix m p ℂ) (z : EuclideanSpace ℂ m) (i : p) :
    ((padLeft (q := q) D).conjTranspose *ᵥ z.ofLp) (Sum.inl (β := q) i) =
      (D.conjTranspose *ᵥ z.ofLp) i := by
  simp [padLeft, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct]

private lemma padRight_mulVec {m p q : Type*} [Fintype m] [DecidableEq m]
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    (C : Matrix m q ℂ) (z : EuclideanSpace ℂ m) (j : q) :
    ((padRight (p := p) C).conjTranspose *ᵥ z.ofLp) (Sum.inr (α := p) j) =
      (C.conjTranspose *ᵥ z.ofLp) j := by
  simp [padRight, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct]

private lemma padLeft_norm {m p q : Type*} [Fintype m] [DecidableEq m]
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    (D : Matrix m p ℂ) (z : EuclideanSpace ℂ m) :
    ‖(Matrix.toEuclideanLin (padLeft (q := q) D).conjTranspose) z‖ ^ 2 =
      ‖(Matrix.toEuclideanLin D.conjTranspose) z‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  rw [Fintype.sum_sum_type]
  have hz : ∀ j : q, ((padLeft (q := q) D).conjTranspose *ᵥ z.ofLp)
      (Sum.inr (α := p) j) = 0 := by
    intro j
    simp [padLeft, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct]
  simp [padLeft_mulVec, hz]

private lemma padRight_norm {m p q : Type*} [Fintype m] [DecidableEq m]
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    (C : Matrix m q ℂ) (z : EuclideanSpace ℂ m) :
    ‖(Matrix.toEuclideanLin (padRight (p := p) C).conjTranspose) z‖ ^ 2 =
      ‖(Matrix.toEuclideanLin C.conjTranspose) z‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  rw [Fintype.sum_sum_type]
  have hz : ∀ i : p, ((padRight (p := p) C).conjTranspose *ᵥ z.ofLp)
      (Sum.inl (β := q) i) = 0 := by
    intro i
    simp [padRight, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct]
  simp [padRight_mulVec, hz]

lemma gram_majorization {m p q : Type*} [Fintype m] [DecidableEq m]
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    (C : Matrix m q ℂ) (D : Matrix m p ℂ) (k : ℝ) (hk : 0 ≤ k)
    (hgram : ((k : ℂ) • (C * Cᴴ) - D * Dᴴ).PosSemidef) :
    ∀ z : EuclideanSpace ℂ m,
      ‖(Matrix.toEuclideanLin Dᴴ) z‖ ≤ Real.sqrt k * ‖(Matrix.toEuclideanLin Cᴴ) z‖ := by
  intro z
  have hp := hgram.dotProduct_mulVec_nonneg z.ofLp
  have hC : star z.ofLp ⬝ᵥ ((C * Cᴴ) *ᵥ z.ofLp) =
      star (Cᴴ *ᵥ z.ofLp) ⬝ᵥ (Cᴴ *ᵥ z.ofLp) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.mulVec_conjTranspose C z.ofLp, star_star]
  have hD : star z.ofLp ⬝ᵥ ((D * Dᴴ) *ᵥ z.ofLp) =
      star (Dᴴ *ᵥ z.ofLp) ⬝ᵥ (Dᴴ *ᵥ z.ofLp) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.mulVec_conjTranspose D z.ofLp, star_star]
  have hp' := (Complex.nonneg_iff.mp hp).1
  have hsq : ‖(Matrix.toEuclideanLin Dᴴ) z‖ ^ 2 ≤
      k * ‖(Matrix.toEuclideanLin Cᴴ) z‖ ^ 2 := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub,
      dotProduct_smul] at hp'
    have hp'' : 0 ≤ k *
        (star z.ofLp ⬝ᵥ ((C * Cᴴ) *ᵥ z.ofLp)).re -
        (star z.ofLp ⬝ᵥ ((D * Dᴴ) *ᵥ z.ofLp)).re := by
      simpa using hp'
    rw [hC, hD] at hp''
    have hnormC : ‖(Matrix.toEuclideanLin Cᴴ) z‖ ^ 2 =
        (star (Cᴴ *ᵥ z.ofLp) ⬝ᵥ (Cᴴ *ᵥ z.ofLp)).re := by
      simp [EuclideanSpace.norm_sq_eq, Matrix.toLpLin_apply, dotProduct,
        Complex.sq_norm, Complex.normSq_apply, Complex.normSq_eq_conj_mul_self]
    have hnormD : ‖(Matrix.toEuclideanLin Dᴴ) z‖ ^ 2 =
        (star (Dᴴ *ᵥ z.ofLp) ⬝ᵥ (Dᴴ *ᵥ z.ofLp)).re := by
      simp [EuclideanSpace.norm_sq_eq, Matrix.toLpLin_apply, dotProduct,
        Complex.sq_norm, Complex.normSq_apply, Complex.normSq_eq_conj_mul_self]
    rw [hnormD, hnormC]
    linarith
  have hsqrt : 0 ≤ Real.sqrt k := Real.sqrt_nonneg _
  have hsqrt2 : (Real.sqrt k) ^ 2 = k := Real.sq_sqrt hk
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hsqrt (norm_nonneg _))).mp
  calc
    ‖(Matrix.toEuclideanLin Dᴴ) z‖ ^ 2 ≤
        k * ‖(Matrix.toEuclideanLin Cᴴ) z‖ ^ 2 := hsq
    _ = (Real.sqrt k * ‖(Matrix.toEuclideanLin Cᴴ) z‖) ^ 2 := by
      rw [mul_pow, hsqrt2]

lemma matrixCLM_adjoint {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (M : Matrix m n ℂ) :
    (matrixCLM M).adjoint = matrixCLM Mᴴ := by
  unfold matrixCLM
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.adjoint_toContinuousLinearMap]

private lemma norm_padLeft_eq {m p q : Type*} [Fintype m] [DecidableEq m]
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    (D : Matrix m p ℂ) (z : EuclideanSpace ℂ m) :
    ‖(Matrix.toEuclideanLin (padLeft (q := q) D).conjTranspose) z‖ =
      ‖(Matrix.toEuclideanLin D.conjTranspose) z‖ := by
  have h := padLeft_norm (q := q) D z
  nlinarith [norm_nonneg ((Matrix.toEuclideanLin (padLeft (q := q) D).conjTranspose) z),
    norm_nonneg ((Matrix.toEuclideanLin D.conjTranspose) z)]

private lemma norm_padRight_eq {m p q : Type*} [Fintype m] [DecidableEq m]
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    (C : Matrix m q ℂ) (z : EuclideanSpace ℂ m) :
    ‖(Matrix.toEuclideanLin (padRight (p := p) C).conjTranspose) z‖ =
      ‖(Matrix.toEuclideanLin C.conjTranspose) z‖ := by
  have h := padRight_norm (p := p) C z
  nlinarith [norm_nonneg ((Matrix.toEuclideanLin (padRight (p := p) C).conjTranspose) z),
    norm_nonneg ((Matrix.toEuclideanLin C.conjTranspose) z)]

private lemma padded_douglas {m p q : Type*} [Fintype m] [DecidableEq m]
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    (C : Matrix m q ℂ) (D : Matrix m p ℂ) (k : ℝ) (hk : 0 ≤ k)
    (hgram : ((k : ℂ) • (C * Cᴴ) - D * Dᴴ).PosSemidef) :
    ∃ L : EuclideanSpace ℂ (Sum p q) →L[ℂ] EuclideanSpace ℂ (Sum p q),
      matrixCLM (padLeft (q := q) D) =
        (matrixCLM (padRight (p := p) C)).comp L ∧ ‖L‖ ≤ Real.sqrt k := by
  apply D5.S3.HilbertOperators.DouglasLemma.exists_factorization_of_majorization
    (matrixCLM (padLeft (q := q) D)) (matrixCLM (padRight (p := p) C))
    (Real.sqrt_nonneg k)
  intro z
  rw [matrixCLM_adjoint, matrixCLM_adjoint]
  change ‖Matrix.toEuclideanLin (padLeft (q := q) D)ᴴ z‖ ≤
    Real.sqrt k * ‖Matrix.toEuclideanLin (padRight (p := p) C)ᴴ z‖
  rw [norm_padLeft_eq, norm_padRight_eq]
  exact gram_majorization C D k hk hgram z

lemma rectangular_douglas {m p q : Type*} [Fintype m] [DecidableEq m]
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    (C : Matrix m q ℂ) (D : Matrix m p ℂ) (k : ℝ) (hk : 0 ≤ k)
    (hgram : ((k : ℂ) • (C * Cᴴ) - D * Dᴴ).PosSemidef) :
    ∃ T : Matrix q p ℂ, C * T = D ∧
      ∀ z : EuclideanSpace ℂ p, ‖matrixCLM T z‖ ≤ Real.sqrt k * ‖z‖ := by
  obtain ⟨L, hL, hLn⟩ := padded_douglas C D k hk hgram
  let M : Matrix (Sum p q) (Sum p q) ℂ := Matrix.toEuclideanLin.symm L.toLinearMap
  have hM : Matrix.toEuclideanLin M = L.toLinearMap :=
    Matrix.toEuclideanLin.apply_symm_apply _
  have hLM : padLeft (q := q) D = padRight (p := p) C * M := by
    apply Matrix.toEuclideanLin.injective
    rw [Matrix.toLpLin_mul_same, hM]
    exact congrArg ContinuousLinearMap.toLinearMap hL
  let T : Matrix q p ℂ := fun j i => M (Sum.inr j) (Sum.inl i)
  refine ⟨T, ?_, ?_⟩
  · ext i j
    have hij := congrArg (fun A => A i (Sum.inl j)) hLM
    change (∑ x, C i x * T x j) = D i j
    simpa [padLeft, padRight, Matrix.mul_apply, Fintype.sum_sum_type, T] using hij.symm
  · intro z
    let z' : EuclideanSpace ℂ (Sum p q) := WithLp.toLp 2 (Sum.elim z.ofLp (fun _ => 0))
    have hz : ‖z'‖ = ‖z‖ := by
      have hs : ‖z'‖ ^ 2 = ‖z‖ ^ 2 := by
        simp [EuclideanSpace.norm_sq_eq, z', Fintype.sum_sum_type]
      nlinarith [norm_nonneg z', norm_nonneg z]
    have heq : ∀ j : q, (matrixCLM T z) j = (L z') (Sum.inr j) := by
      intro j
      have hm := congrArg (fun f => (f z') (Sum.inr j)) hM
      change (∑ i, T j i * z.ofLp i) = (L z') (Sum.inr j)
      simpa [matrixCLM, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
        T, z', Fintype.sum_sum_type] using hm
    have hpart : ‖matrixCLM T z‖ ≤ ‖L z'‖ := by
      apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]
      simp_rw [heq]
      exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact hpart.trans ((L.le_opNorm z').trans (by gcongr; rw [hz]))

lemma matrixCLM_mul {m n p : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]
    (A : Matrix m n ℂ) (B : Matrix n p ℂ) :
    matrixCLM (A * B) = (matrixCLM A).comp (matrixCLM B) := by
  apply ContinuousLinearMap.ext
  intro z
  exact congrArg (fun f => f z) (Matrix.toLpLin_mul_same 2 A B)

lemma norm_bound_gram {p q : Type*} [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q] (T : Matrix q p ℂ) (k : ℝ) (hk : 0 ≤ k)
    (hT : ∀ z : EuclideanSpace ℂ p, ‖matrixCLM T z‖ ≤ Real.sqrt k * ‖z‖) :
    ((k : ℂ) • (1 : Matrix p p ℂ) - Tᴴ * T).PosSemidef := by
  apply Matrix.isPositive_toEuclideanLin_iff.mp
  refine ⟨Matrix.isSymmetric_toEuclideanLin_iff.mpr ?_, ?_⟩
  · change ((k : ℂ) • (1 : Matrix p p ℂ) - Tᴴ * T)ᴴ = _
    simp
  · intro z
    have hn := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hT z)
    rw [mul_pow, Real.sq_sqrt hk] at hn
    have heq :
        Matrix.toEuclideanLin ((k : ℂ) • (1 : Matrix p p ℂ) - Tᴴ * T) z =
        (k : ℂ) • z - (Matrix.toEuclideanLin T).adjoint (Matrix.toEuclideanLin T z) := by
      rw [map_sub, map_smul, Matrix.toLpLin_mul_same,
        Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      simp [Matrix.toEuclideanLin]
    rw [heq, inner_sub_left, inner_smul_left, LinearMap.adjoint_inner_left]
    simpa [inner_self_eq_norm_sq_to_K, Complex.conj_ofReal,
      Complex.mul_re, ← Complex.ofReal_pow, matrixCLM] using sub_nonneg.mpr hn

end D5.S3.Quantum.Divergence.ScalarizerMatrixTransport
