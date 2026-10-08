/- GID: D5/S3/Quantum/Matrix/CommutatorGap
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/CommutatorGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A common maximizing block frame bounds scalar translations by the commutator gap. -/

/-
admission_basis: escape-witness
proof_shape: scalar_translation_from_block_bound: bind-only; consumer: translation_from_block; escape_witness: none
proof_shape: mulVec_rectNorm_bound: bind-only; consumer: headRow_bound, opSq_le_frobSq, translated_component_bounds; escape_witness: none
proof_shape: rectNorm_sq: bind-only; consumer: frobSq_block, pure_first_variance; escape_witness: none
proof_shape: rectNorm_sq_square: bind-only; consumer: maximizing_block_frame, opSq_le_frobSq, translation_from_block; escape_witness: none
proof_shape: norm_sq_head_tail: bind-only; consumer: blockNorm_domination; escape_witness: none
proof_shape: frobSq_block: bind-only; consumer: maximizing_block_frame, translation_from_block; escape_witness: none
proof_shape: headRow_bound: bind-only; consumer: translated_component_bounds; escape_witness: none
proof_shape: translated_head: bind-only; consumer: translated_component_bounds; escape_witness: none
proof_shape: translated_tail: bind-only; consumer: translated_component_bounds; escape_witness: none
proof_shape: translated_component_bounds: bind-only; consumer: blockNorm_domination; escape_witness: none
proof_shape: blockNorm_domination: bind-only; consumer: block_frobenius_bound; escape_witness: none
proof_shape: block_frobenius_bound: bind-only; consumer: translation_from_block; escape_witness: none
proof_shape: translation_from_block: bind-only; consumer: translation_gap; escape_witness: none
proof_shape: frobSq_unitary_right: bind-only; consumer: maximizing_block_frame, translation_gap, unitary_pencil_bound; escape_witness: none
proof_shape: frobSq_unitary_left: bind-only; consumer: maximizing_block_frame, translation_gap; escape_witness: none
proof_shape: opSq_le_frobSq: bind-only; consumer: projection_K_quadratic, projection_adjoint_bound; escape_witness: none
proof_shape: commutator_norm_bound_of_pure: bind-only; consumer: maximizing_block_frame; escape_witness: none
proof_shape: pure_first_variance: bind-only; consumer: maximizing_block_frame; escape_witness: none
proof_shape: exists_unitary_first_column: bind-only; consumer: maximizing_block_frame; escape_witness: none
proof_shape: pure_variance_norms: bind-only; consumer: pure_first_variance, pure_variance_conjugation; escape_witness: none
proof_shape: unitary_inner: bind-only; consumer: pure_variance_conjugation; escape_witness: none
proof_shape: unitary_vector_norm: bind-only; consumer: pure_variance_conjugation; escape_witness: none
proof_shape: conjugation_intertwine: bind-only; consumer: pure_variance_conjugation; escape_witness: none
proof_shape: opSq_conjugation: bind-only; consumer: translation_gap; escape_witness: none
proof_shape: translated_conjugation: bind-only; consumer: translation_gap; escape_witness: none
proof_shape: pure_variance_conjugation: bind-only; consumer: maximizing_block_frame; escape_witness: none
proof_shape: maximizing_block_frame: content; escape_witness: sphere_image_eq_ball_image, pure_of_density_linear_max, blochPure_surjective
proof_shape: gap_nonnegative: content; escape_witness: sphere_image_eq_ball_image, pure_of_density_linear_max, blochPure_surjective
proof_shape: translation_gap: content; escape_witness: sphere_image_eq_ball_image, pure_of_density_linear_max, blochPure_surjective
escape_witness: maximizing_block_frame / translation_gap
Direct frozen dependencies:
  owner GID: D5/S3/Weil/ZetaLinear/PosIndex; declaration: RHLinalg.frobSq
    declaration statement_id: sha256:a1114d4731d26d6c5ef81acb0a254cdc6e0ed6e629ccb2dcf75d7faa00f4ccce
  owner GID: D5/S3/Observer/HiddenFlow/ProjectionCommutatorIdentity; declaration: D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator
    declaration statement_id: sha256:4b14c2bab713c5f81d97b9a10d285ee0878e4a933dc5a6b66387f846355b44aa
  owner GID: D5/S3/Quantum/GNSMatrix; declaration: D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace
    declaration statement_id: sha256:470140292aee89705512206af514f5a42fdc3948e5c9195d302613a47b859917
  owner GID: D5/S3/Quantum/Algebra/GramUnitaryExtension; declaration: D5.S3.Quantum.Algebra.GramUnitaryExtension.exists_unitary_mul_eq_of_conjTranspose_mul_eq
    declaration statement_id: sha256:accd04d85421c0847456ddb52626f272e79ea98e568dcf9dfeddc5035a1f2013
  Other lane imports are same-delivery prerequisites, not baseline-frozen dependencies.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S3.Quantum.Matrix.CartesianVariance
import D5.S3.Quantum.GNSMatrix
import D5.S3.Quantum.Algebra.GramUnitaryExtension

noncomputable section
open Matrix Set Unitary
open scoped ComplexInnerProductSpace ComplexOrder
namespace D5.S3.Quantum.Matrix.CommutatorGap
open D5.S3.Quantum.Matrix.NumericalRange
open D5.S3.Quantum.Matrix.CartesianVariance
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum
open D5.S3.Quantum.Fibers.PhysicalFiber

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

private theorem scalar_translation_from_block_bound (a d p q r x t : ℝ)
    (ht : 0 ≤ t)
    (ha : a = p ^ 2 + q ^ 2 + r ^ 2 + x ^ 2)
    (hd : 2 * (p ^ 2 + q ^ 2) ≤ d) :
    (p + t) ^ 2 + r ^ 2 + x ^ 2 + (q + t) ^ 2 ≤
      a + 2 * t ^ 2 + 2 * t * Real.sqrt d := by
  have hd0 : 0 ≤ d := by nlinarith [sq_nonneg p, sq_nonneg q]
  have hroot := Real.sq_sqrt hd0
  have hroot0 := Real.sqrt_nonneg d
  have hs : p + q ≤ Real.sqrt d := by nlinarith [sq_nonneg (p - q)]
  have := mul_le_mul_of_nonneg_left hs ht
  nlinarith

def commOperator {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ)) : (EuclideanSpace ℂ (Fin n × Fin n)) →L[ℂ] (EuclideanSpace ℂ (Fin n × Fin n)) :=
  ((vectorize n).toLinearMap.comp (((LinearMap.mulLeft ℂ A - LinearMap.mulRight ℂ A)).comp (vectorize n).symm.toLinearMap)).toContinuousLinearMap

def gap {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ)) : ℝ := 2 * RHLinalg.frobSq A - ‖commOperator A‖ ^ 2

def opSq {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ)) : ℝ := ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖ ^ 2

open scoped Matrix.Norms.Frobenius in
private theorem mulVec_rectNorm_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (v : EuclideanSpace ℂ (Fin n)) :
    ‖WithLp.toLp 2 (A *ᵥ v.ofLp)‖ ≤ (@norm (Matrix _ _ ℂ) Matrix.frobeniusSeminormedAddCommGroup.toNorm) A * ‖v‖ := by
  have h := Matrix.frobenius_norm_mul A (Matrix.replicateCol Unit v.ofLp)
  have he : A * Matrix.replicateCol Unit v.ofLp = Matrix.replicateCol Unit (A *ᵥ v.ofLp) := by
    ext i j; rfl
  rw [he,Matrix.frobenius_norm_replicateCol,Matrix.frobenius_norm_replicateCol] at h
  exact h

private theorem rectNorm_sq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    ((@norm (Matrix _ _ ℂ) Matrix.frobeniusSeminormedAddCommGroup.toNorm) A)^2 = ∑ i, ∑ j, ‖A i j‖^2  := by
  open scoped Matrix.Norms.Frobenius in
    simp only [Matrix.frobenius_norm_def, Real.rpow_two, ← Real.sqrt_eq_rpow]
    exact Real.sq_sqrt (by positivity)

private theorem rectNorm_sq_square {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ)) : ((@norm (Matrix _ _ ℂ) Matrix.frobeniusSeminormedAddCommGroup.toNorm) A)^2 = RHLinalg.frobSq A := by
  have h := congrArg Complex.re (D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace A)
  simpa only [Complex.ofReal_re, RHLinalg.frobSq, RCLike.re_eq_complex_re] using h

private theorem norm_sq_head_tail {n : ℕ} (v : EuclideanSpace ℂ (Fin (n+1))) :
    ‖v‖^2 = ‖v 0‖^2 + ‖(fun (v : EuclideanSpace ℂ (Fin (n+1))) => WithLp.toLp 2 (Fin.tail v.ofLp)) v‖^2 := by
  simp [EuclideanSpace.norm_sq_eq,Fin.sum_univ_succ,Fin.tail]

private theorem frobSq_block {n : ℕ} (A : (Matrix (Fin (n+1)) (Fin (n+1)) ℂ)) :
    RHLinalg.frobSq A = ‖A 0 0‖^2 + ((@norm (Matrix _ _ ℂ) Matrix.frobeniusSeminormedAddCommGroup.toNorm) (A.submatrix Fin.succ Fin.succ))^2 +
      ((@norm (Matrix _ _ ℂ) Matrix.frobeniusSeminormedAddCommGroup.toNorm) ((fun (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) => A.submatrix (fun _ : Fin 1 => (0 : Fin (n+1))) Fin.succ) A))^2 + ‖(fun (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) => WithLp.toLp 2 (A.col 0 ∘ Fin.succ)) A‖^2 := by
  simp only [frobSq_eq_sum,Complex.normSq_eq_norm_sq,Fin.sum_univ_succ,
    rectNorm_sq,EuclideanSpace.norm_sq_eq,Matrix.submatrix_apply,
    Matrix.col,Matrix.transpose_apply,Function.comp_apply]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j : Fin n => ‖A i.succ j.succ‖^2)]
  ring

private theorem headRow_bound {n : ℕ} (A : (Matrix (Fin (n+1)) (Fin (n+1)) ℂ)) (v : EuclideanSpace ℂ (Fin n)) :
    ‖∑ j, A 0 j.succ * v j‖ ≤ (@norm (Matrix _ _ ℂ) Matrix.frobeniusSeminormedAddCommGroup.toNorm) ((fun (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) => A.submatrix (fun _ : Fin 1 => (0 : Fin (n+1))) Fin.succ) A) * ‖v‖ := by
  have h := mulVec_rectNorm_bound ((fun (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) => A.submatrix (fun _ : Fin 1 => (0 : Fin (n+1))) Fin.succ) A) v
  simpa [EuclideanSpace.norm_eq,Matrix.mulVec,dotProduct] using h

private theorem translated_head {n : ℕ} (A : (Matrix (Fin (n+1)) (Fin (n+1)) ℂ)) (c : ℂ)
    (v : EuclideanSpace ℂ (Fin (n+1))) :
    (Matrix.toEuclideanLin (A-c•1) v) 0 =
      (A 0 0-c)*v 0 + ∑ j, A 0 j.succ * ((fun (v : EuclideanSpace ℂ (Fin (n+1))) => WithLp.toLp 2 (Fin.tail v.ofLp)) v) j := by
  simp [Matrix.toEuclideanLin_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.tail]
  ring

private theorem translated_tail {n : ℕ} (A : (Matrix (Fin (n+1)) (Fin (n+1)) ℂ)) (c : ℂ)
    (v : EuclideanSpace ℂ (Fin (n+1))) :
    (fun (v : EuclideanSpace ℂ (Fin (n+1))) => WithLp.toLp 2 (Fin.tail v.ofLp)) (Matrix.toEuclideanLin (A-c•1) v) =
      v 0 • (fun (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) => WithLp.toLp 2 (A.col 0 ∘ Fin.succ)) A + Matrix.toEuclideanLin (A.submatrix Fin.succ Fin.succ) ((fun (v : EuclideanSpace ℂ (Fin (n+1))) => WithLp.toLp 2 (Fin.tail v.ofLp)) v) - c • (fun (v : EuclideanSpace ℂ (Fin (n+1))) => WithLp.toLp 2 (Fin.tail v.ofLp)) v := by
  ext i
  simp [Fin.tail,Matrix.col,Function.comp_apply,
    Matrix.toEuclideanLin_apply,Matrix.mulVec,dotProduct,
    Fin.sum_univ_succ,Finset.sum_sub_distrib,mul_comm]

private theorem translated_component_bounds {n : ℕ} (A : (Matrix (Fin (n+1)) (Fin (n+1)) ℂ)) (c : ℂ)
    (v : EuclideanSpace ℂ (Fin (n+1))) :
    ‖(Matrix.toEuclideanLin (A-c•1) v) 0‖ ≤
        (‖A 0 0‖+‖c‖)*‖v 0‖+(@norm (Matrix _ _ ℂ) Matrix.frobeniusSeminormedAddCommGroup.toNorm) ((fun (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) => A.submatrix (fun _ : Fin 1 => (0 : Fin (n+1))) Fin.succ) A)*‖(fun (v : EuclideanSpace ℂ (Fin (n+1))) => WithLp.toLp 2 (Fin.tail v.ofLp)) v‖ ∧
    ‖(fun (v : EuclideanSpace ℂ (Fin (n+1))) => WithLp.toLp 2 (Fin.tail v.ofLp)) (Matrix.toEuclideanLin (A-c•1) v)‖ ≤
        ‖(fun (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) => WithLp.toLp 2 (A.col 0 ∘ Fin.succ)) A‖*‖v 0‖+((@norm (Matrix _ _ ℂ) Matrix.frobeniusSeminormedAddCommGroup.toNorm) (A.submatrix Fin.succ Fin.succ)+‖c‖)*‖(fun (v : EuclideanSpace ℂ (Fin (n+1))) => WithLp.toLp 2 (Fin.tail v.ofLp)) v‖ := by
  constructor
  · rw [translated_head]
    calc
      _ ≤ ‖(A 0 0-c)*v 0‖ + ‖∑ j, A 0 j.succ * ((fun (v : EuclideanSpace ℂ (Fin (n+1))) => WithLp.toLp 2 (Fin.tail v.ofLp)) v) j‖ := norm_add_le _ _
      _ ≤ (‖A 0 0‖+‖c‖)*‖v 0‖+(@norm (Matrix _ _ ℂ) Matrix.frobeniusSeminormedAddCommGroup.toNorm) ((fun (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) => A.submatrix (fun _ : Fin 1 => (0 : Fin (n+1))) Fin.succ) A)*‖(fun (v : EuclideanSpace ℂ (Fin (n+1))) => WithLp.toLp 2 (Fin.tail v.ofLp)) v‖ := by
        rw [norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _))
          (headRow_bound A ((fun (v : EuclideanSpace ℂ (Fin (n+1))) => WithLp.toLp 2 (Fin.tail v.ofLp)) v))
  · rw [translated_tail]
    calc
      _ ≤ ‖v 0 • (fun (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) => WithLp.toLp 2 (A.col 0 ∘ Fin.succ)) A‖ + ‖Matrix.toEuclideanLin (A.submatrix Fin.succ Fin.succ) ((fun (v : EuclideanSpace ℂ (Fin (n+1))) => WithLp.toLp 2 (Fin.tail v.ofLp)) v)‖ + ‖c • (fun (v : EuclideanSpace ℂ (Fin (n+1))) => WithLp.toLp 2 (Fin.tail v.ofLp)) v‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
      _ ≤ ‖(fun (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) => WithLp.toLp 2 (A.col 0 ∘ Fin.succ)) A‖*‖v 0‖+((@norm (Matrix _ _ ℂ) Matrix.frobeniusSeminormedAddCommGroup.toNorm) (A.submatrix Fin.succ Fin.succ)+‖c‖)*‖(fun (v : EuclideanSpace ℂ (Fin (n+1))) => WithLp.toLp 2 (Fin.tail v.ofLp)) v‖ := by
        simp only [norm_smul]
        have h := mulVec_rectNorm_bound (A.submatrix Fin.succ Fin.succ) ((fun (v : EuclideanSpace ℂ (Fin (n+1))) => WithLp.toLp 2 (Fin.tail v.ofLp)) v)
        change ‖Matrix.toEuclideanLin (A.submatrix Fin.succ Fin.succ) ((fun (v : EuclideanSpace ℂ (Fin (n+1))) => WithLp.toLp 2 (Fin.tail v.ofLp)) v)‖ ≤ _ at h
        nlinarith

def comparisonMatrix {n : ℕ} (A : (Matrix (Fin (n+1)) (Fin (n+1)) ℂ)) (c : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![‖A 0 0‖+‖c‖,(@norm (Matrix _ _ ℂ) Matrix.frobeniusSeminormedAddCommGroup.toNorm) ((fun (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) => A.submatrix (fun _ : Fin 1 => (0 : Fin (n+1))) Fin.succ) A);‖(fun (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) => WithLp.toLp 2 (A.col 0 ∘ Fin.succ)) A‖,(@norm (Matrix _ _ ℂ) Matrix.frobeniusSeminormedAddCommGroup.toNorm) (A.submatrix Fin.succ Fin.succ)+‖c‖]

open scoped Matrix.Norms.Frobenius in
theorem blockNorm_domination {n : ℕ} (A : (Matrix (Fin (n+1)) (Fin (n+1)) ℂ)) (c : ℂ) :
    ‖(Matrix.toEuclideanLin (A-c•1)).toContinuousLinearMap‖ ≤
      ‖(Matrix.toEuclideanLin (comparisonMatrix A c)).toContinuousLinearMap‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  let u : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![‖v 0‖,‖(fun (v : EuclideanSpace ℂ (Fin (n+1))) => WithLp.toLp 2 (Fin.tail v.ofLp)) v‖]
  have hu : ‖u‖ = ‖v‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq_head_tail v]
    simp [u,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  have hb := translated_component_bounds A c v
  have hp : 0 ≤ (‖A 0 0‖+‖c‖)*‖v 0‖+(@norm (Matrix _ _ ℂ) Matrix.frobeniusSeminormedAddCommGroup.toNorm) ((fun (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) => A.submatrix (fun _ : Fin 1 => (0 : Fin (n+1))) Fin.succ) A)*‖(fun (v : EuclideanSpace ℂ (Fin (n+1))) => WithLp.toLp 2 (Fin.tail v.ofLp)) v‖ := by
    positivity
  have hq : 0 ≤ ‖(fun (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) => WithLp.toLp 2 (A.col 0 ∘ Fin.succ)) A‖*‖v 0‖+((@norm (Matrix _ _ ℂ) Matrix.frobeniusSeminormedAddCommGroup.toNorm) (A.submatrix Fin.succ Fin.succ)+‖c‖)*‖(fun (v : EuclideanSpace ℂ (Fin (n+1))) => WithLp.toLp 2 (Fin.tail v.ofLp)) v‖ := by
    positivity
  have hsq : ‖Matrix.toEuclideanLin (A-c•1) v‖^2 ≤
      ‖Matrix.toEuclideanLin (comparisonMatrix A c) u‖^2 := by
    rw [norm_sq_head_tail]
    have h1 := (sq_le_sq₀ (norm_nonneg _) hp).mpr hb.1
    have h2 := (sq_le_sq₀ (norm_nonneg _) hq).mpr hb.2
    simpa [EuclideanSpace.norm_sq_eq,Fin.sum_univ_two,comparisonMatrix,u,
      Matrix.toEuclideanLin_apply,Matrix.mulVec,dotProduct,mul_comm] using add_le_add h1 h2
  calc
    _ ≤ ‖Matrix.toEuclideanLin (comparisonMatrix A c) u‖ :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
    _ ≤ ‖(Matrix.toEuclideanLin (comparisonMatrix A c)).toContinuousLinearMap‖ * ‖u‖ :=
      by simpa using (Matrix.toEuclideanLin (comparisonMatrix A c)).toContinuousLinearMap.le_opNorm u
    _ = _ := by rw [hu]

open scoped Matrix.Norms.Frobenius in
private theorem block_frobenius_bound {n : ℕ} (A : (Matrix (Fin (n+1)) (Fin (n+1)) ℂ)) (c : ℂ) :
    opSq (A-c•1) ≤ (‖A 0 0‖+‖c‖)^2 + ((@norm (Matrix _ _ ℂ) Matrix.frobeniusSeminormedAddCommGroup.toNorm) ((fun (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) => A.submatrix (fun _ : Fin 1 => (0 : Fin (n+1))) Fin.succ) A))^2 +
      ‖(fun (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) => WithLp.toLp 2 (A.col 0 ∘ Fin.succ)) A‖^2 + ((@norm (Matrix _ _ ℂ) Matrix.frobeniusSeminormedAddCommGroup.toNorm) (A.submatrix Fin.succ Fin.succ)+‖c‖)^2  := by
  have hd := blockNorm_domination A c
  have hf : ‖(Matrix.toEuclideanLin (comparisonMatrix A c)).toContinuousLinearMap‖ ≤
      ‖WithLp.toLp 2 (fun ij : Fin 2 × Fin 2 => comparisonMatrix A c ij.1 ij.2)‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro v
    change ‖WithLp.toLp 2 (comparisonMatrix A c *ᵥ v.ofLp)‖ ≤
      ‖WithLp.toLp 2 (fun ij : Fin 2 × Fin 2 => comparisonMatrix A c ij.1 ij.2)‖ * ‖v‖
    have h := Matrix.frobenius_norm_mul (comparisonMatrix A c) (Matrix.replicateCol Unit v.ofLp)
    have he : comparisonMatrix A c * Matrix.replicateCol Unit v.ofLp =
        Matrix.replicateCol Unit (comparisonMatrix A c *ᵥ v.ofLp) := by ext i j; rfl
    rw [he, Matrix.frobenius_norm_replicateCol, Matrix.frobenius_norm_replicateCol] at h
    simpa only [Matrix.frobenius_norm_def, EuclideanSpace.norm_eq,
      Fintype.sum_prod_type, Real.sqrt_eq_rpow, Real.rpow_two ] using h
  have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hd.trans hf)
  simpa [opSq, EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type,
    Fin.sum_univ_two, comparisonMatrix, Real.norm_eq_abs, sq_abs, add_assoc] using hs


private theorem translation_from_block : (∀ n (A : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) (d : ℝ),
    2 * (Complex.normSq (A 0 0) + RHLinalg.frobSq (A.submatrix Fin.succ Fin.succ)) ≤ d →
    ∀ c : ℂ, opSq (A - c • (1 : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))) ≤
      RHLinalg.frobSq A + 2 * Complex.normSq c + 2 * ‖c‖ * Real.sqrt d) := by
  intro n A d hd c
  have h := scalar_translation_from_block_bound (RHLinalg.frobSq A) d
    ‖A 0 0‖ ((@norm (Matrix _ _ ℂ) Matrix.frobeniusSeminormedAddCommGroup.toNorm) (A.submatrix Fin.succ Fin.succ)) ((@norm (Matrix _ _ ℂ) Matrix.frobeniusSeminormedAddCommGroup.toNorm) ((fun (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) => A.submatrix (fun _ : Fin 1 => (0 : Fin (n+1))) Fin.succ) A))
    ‖(fun (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) => WithLp.toLp 2 (A.col 0 ∘ Fin.succ)) A‖ ‖c‖ (norm_nonneg _) (frobSq_block A) (by
      simpa only [rectNorm_sq_square,←Complex.normSq_eq_norm_sq] using hd)
  simpa only [←Complex.normSq_eq_norm_sq] using (block_frobenius_bound A c).trans h

theorem frobSq_unitary_right {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ)) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    RHLinalg.frobSq (A*(U : (Matrix (Fin n) (Fin n) ℂ))) = RHLinalg.frobSq A := by
  have h := congrArg Complex.re (Matrix.trace_units_conj' (Unitary.toUnits U) (Aᴴ * A))
  change (Matrix.trace ((U : Matrix (Fin n) (Fin n) ℂ)ᴴ * (Aᴴ * A) * (U : Matrix (Fin n) (Fin n) ℂ))).re = (Matrix.trace (Aᴴ * A)).re at h
  simpa only [RHLinalg.frobSq, RCLike.re_eq_complex_re, Matrix.conjTranspose_mul, Matrix.mul_assoc] using h

private theorem frobSq_unitary_left {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ)) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    RHLinalg.frobSq ((U : (Matrix (Fin n) (Fin n) ℂ))*A) = RHLinalg.frobSq A := by
  unfold RHLinalg.frobSq
  have hu : (U : (Matrix (Fin n) (Fin n) ℂ))ᴴ*(U : (Matrix (Fin n) (Fin n) ℂ)) = 1 := Unitary.star_mul_self_of_mem U.property
  rw [Matrix.conjTranspose_mul]
  have he : Aᴴ*(U : (Matrix (Fin n) (Fin n) ℂ))ᴴ*((U : (Matrix (Fin n) (Fin n) ℂ))*A) = Aᴴ*((U : (Matrix (Fin n) (Fin n) ℂ))ᴴ*(U : (Matrix (Fin n) (Fin n) ℂ)))*A := by simp only [Matrix.mul_assoc]
  rw [he,hu,Matrix.mul_one]

open scoped Matrix.Norms.Frobenius in
theorem opSq_le_frobSq {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ)) : opSq A ≤ RHLinalg.frobSq A := by
  have h : ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖ ≤ (@norm (Matrix _ _ ℂ) Matrix.frobeniusSeminormedAddCommGroup.toNorm) A := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro v
    exact mulVec_rectNorm_bound A v
  rw [opSq,←rectNorm_sq_square]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h

private theorem commutator_norm_bound_of_pure {n : ℕ} (hn : 0 < n) (A : (Matrix (Fin n) (Fin n) ℂ))
    (v : EuclideanSpace ℂ (Fin n))
    (hm : ∀ B : (Matrix (Fin n) (Fin n) ℂ), RHLinalg.frobSq (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B) ≤ 4*RHLinalg.frobSq B*variance A ((Matrix.vecMulVec (WithLp.ofLp v) (star (WithLp.ofLp v))))) :
    ‖commOperator A‖^2 ≤ 4*variance A ((Matrix.vecMulVec (WithLp.ofLp v) (star (WithLp.ofLp v)))) := by
  let i : Fin n := ⟨0,hn⟩
  have hone : RHLinalg.frobSq (Matrix.single i i 1 : (Matrix (Fin n) (Fin n) ℂ)) = 1 := by
    classical
    have he : vectorize n (Matrix.single i i 1 : (Matrix (Fin n) (Fin n) ℂ)) = EuclideanSpace.single (i,i) 1 := by
      ext k
      change (Matrix.single i i 1 : (Matrix (Fin n) (Fin n) ℂ)) k.1 k.2 = (Pi.single (i,i) (1 : ℂ) : Fin n × Fin n → ℂ) k
      by_cases h1 : k.1=i <;> by_cases h2 : k.2=i <;>
        simp [Matrix.single_apply,Pi.single_apply,Prod.ext_iff,eq_comm,h1,h2]
    rw [←vectorize_norm_sq,he]
    simp
  have h0 := hm (Matrix.single i i 1)
  rw [hone] at h0
  have hc : 0 ≤ 4*variance A ((Matrix.vecMulVec (WithLp.ofLp v) (star (WithLp.ofLp v)))) := by
    linarith [frobSq_nonneg (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A (Matrix.single i i 1))]
  have hh : ‖commOperator A‖ ≤ Real.sqrt (4*variance A ((Matrix.vecMulVec (WithLp.ofLp v) (star (WithLp.ofLp v))))) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro w
    let B := (vectorize n).symm w
    have hw : vectorize n B = w := (vectorize n).apply_symm_apply w
    have h := hm B
    rw [←vectorize_norm_sq,←vectorize_norm_sq,hw] at h
    have he : commOperator A w = vectorize n (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B) := by
      rw [←hw]
      rfl
    rw [←he] at h
    have hs : (Real.sqrt (4*variance A ((Matrix.vecMulVec (WithLp.ofLp v) (star (WithLp.ofLp v)))))*‖w‖)^2 =
        4*‖w‖^2*variance A ((Matrix.vecMulVec (WithLp.ofLp v) (star (WithLp.ofLp v)))) := by
      rw [mul_pow,Real.sq_sqrt hc]
      ring
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp (hs ▸ h)
  calc
    _ ≤ (Real.sqrt (4*variance A ((Matrix.vecMulVec (WithLp.ofLp v) (star (WithLp.ofLp v))))))^2 :=
      (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hh
    _ = _ := Real.sq_sqrt hc

private theorem exists_unitary_first_column {n : ℕ}
    (v : EuclideanSpace ℂ (Fin (n+1))) (hv : ‖v‖ = 1) :
    ∃ U : Matrix.unitaryGroup (Fin (n+1)) ℂ, ∀ i, (U : (Matrix (Fin (n+1)) (Fin (n+1)) ℂ)) i 0 = v i := by
  classical
  let e : EuclideanSpace ℂ (Fin (n+1)) := EuclideanSpace.single 0 1
  let B := Matrix.replicateCol (Fin 1) v.ofLp
  let A := Matrix.replicateCol (Fin 1) e.ofLp
  have hGram : Bᴴ * B = Aᴴ * A := by
    ext i j
    change dotProduct (star v.ofLp) v.ofLp = dotProduct (star e.ofLp) e.ofLp
    rw [dotProduct_comm (star v.ofLp), dotProduct_comm (star e.ofLp),
      ← EuclideanSpace.inner_eq_star_dotProduct, ← EuclideanSpace.inner_eq_star_dotProduct]
    simp [inner_self_eq_norm_sq_to_K,hv,e]
  obtain ⟨U,hU⟩ :=
    D5.S3.Quantum.Algebra.GramUnitaryExtension.exists_unitary_mul_eq_of_conjTranspose_mul_eq
      B A hGram
  refine ⟨U,fun i => ?_⟩
  have hi := congrFun (congrFun hU i) 0
  simpa [B,A,e,Matrix.mul_apply,Matrix.replicateCol] using hi.symm

private theorem pure_variance_norms {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ)) (v : EuclideanSpace ℂ (Fin n)) :
    variance A ((Matrix.vecMulVec (WithLp.ofLp v) (star (WithLp.ofLp v)))) =
      (‖Matrix.toEuclideanLin A v‖^2+‖Matrix.toEuclideanLin Aᴴ v‖^2)/2-
        Complex.normSq (inner ℂ v (Matrix.toEuclideanLin A v)) := by
  have hcast {k : ℕ} (M : Matrix (Fin k) (Fin k) ℂ) (x : EuclideanSpace ℂ (Fin k)) :
      Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) M x = Matrix.toEuclideanLin M x := by rfl
  let T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A
  have ha : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) Aᴴ = T.adjoint :=
    map_star (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) A
  have h1 : inner ℂ v (Matrix.toEuclideanLin (Aᴴ*A) v) = (‖Matrix.toEuclideanLin A v‖ : ℂ)^2 := by
    have he := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) => L v)
      (map_mul (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) Aᴴ A)
    change Matrix.toEuclideanLin (Aᴴ*A) v =
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) Aᴴ) (T v) at he
    rw [ha] at he
    rw [he,ContinuousLinearMap.adjoint_inner_right,inner_self_eq_norm_sq_to_K]
    rfl
  have h2 : inner ℂ v (Matrix.toEuclideanLin (A*Aᴴ) v) = (‖Matrix.toEuclideanLin Aᴴ v‖ : ℂ)^2 := by
    have he := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) => L v)
      (map_mul (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) A Aᴴ)
    change Matrix.toEuclideanLin (A*Aᴴ) v =
      T ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) Aᴴ) v) at he
    rw [ha] at he
    rw [he,←ContinuousLinearMap.adjoint_inner_left,inner_self_eq_norm_sq_to_K]
    rw [←ha]
    rfl
  rw [variance,cartesian,D5.S3.Quantum.BlockNorm.EssentiallyHermitian.outer_pairing_trace,hcast,D5.S3.Quantum.BlockNorm.EssentiallyHermitian.outer_pairing_trace,hcast]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),map_smul,map_add,
    LinearMap.smul_apply,LinearMap.add_apply,inner_smul_right,inner_add_right,h1,h2]
  simp [pow_two,Complex.mul_re,div_eq_mul_inv]
  ring

private theorem pure_first_variance {n : ℕ} (A : (Matrix (Fin (n+1)) (Fin (n+1)) ℂ)) :
    variance A ((Matrix.vecMulVec (WithLp.ofLp (EuclideanSpace.single 0 1)) (star (WithLp.ofLp (EuclideanSpace.single 0 1))))) =
      (((@norm (Matrix _ _ ℂ) Matrix.frobeniusSeminormedAddCommGroup.toNorm) ((fun (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) => A.submatrix (fun _ : Fin 1 => (0 : Fin (n+1))) Fin.succ) A))^2+‖(fun (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) => WithLp.toLp 2 (A.col 0 ∘ Fin.succ)) A‖^2)/2  := by
  rw [pure_variance_norms]
  simp [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin_apply,
    Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
    rectNorm_sq, EuclideanSpace.norm_sq_eq, Complex.normSq_eq_norm_sq,
    Complex.norm_conj, Complex.star_def]
  ring

private theorem unitary_inner {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    (x y : EuclideanSpace ℂ (Fin n)) :
    inner ℂ (Matrix.toEuclideanLin (U : (Matrix (Fin n) (Fin n) ℂ)) x) (Matrix.toEuclideanLin (U : (Matrix (Fin n) (Fin n) ℂ)) y) =
      inner ℂ x y := by
  have h := ContinuousLinearMap.inner_map_map_of_mem_unitary
    (Unitary.map_mem (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) U.property) x y
  have hcast (z : EuclideanSpace ℂ (Fin n)) :
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (U : Matrix (Fin n) (Fin n) ℂ) z =
        Matrix.toEuclideanLin (U : Matrix (Fin n) (Fin n) ℂ) z := by rfl
  simpa only [hcast] using h

private theorem unitary_vector_norm {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    (x : EuclideanSpace ℂ (Fin n)) : ‖Matrix.toEuclideanLin (U : (Matrix (Fin n) (Fin n) ℂ)) x‖=‖x‖ := by
  let T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (U : (Matrix (Fin n) (Fin n) ℂ))
  have hT : T ∈ unitary (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    Unitary.map_mem (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) U.property
  exact ContinuousLinearMap.norm_map_of_mem_unitary hT x

private theorem conjugation_intertwine {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ)) (U : Matrix.unitaryGroup (Fin n) ℂ)
    (w : EuclideanSpace ℂ (Fin n)) :
    Matrix.toEuclideanLin (U : (Matrix (Fin n) (Fin n) ℂ))
      (Matrix.toEuclideanLin ((U : (Matrix (Fin n) (Fin n) ℂ))ᴴ*A*(U : (Matrix (Fin n) (Fin n) ℂ))) w) =
        Matrix.toEuclideanLin A (Matrix.toEuclideanLin (U : (Matrix (Fin n) (Fin n) ℂ)) w) := by
  have hu : (U : (Matrix (Fin n) (Fin n) ℂ))*(U : (Matrix (Fin n) (Fin n) ℂ))ᴴ=1 := Unitary.mul_star_self_of_mem U.property
  have hm : (U : (Matrix (Fin n) (Fin n) ℂ))*((U : (Matrix (Fin n) (Fin n) ℂ))ᴴ*A*(U : (Matrix (Fin n) (Fin n) ℂ))) = A*(U : (Matrix (Fin n) (Fin n) ℂ)) := by
    rw [←Matrix.mul_assoc,←Matrix.mul_assoc,hu,Matrix.one_mul]
  have he := congrArg (fun X : (Matrix (Fin n) (Fin n) ℂ) => Matrix.toEuclideanLin X w) hm
  simpa only [Matrix.toLpLin_mul_same,LinearMap.comp_apply] using he

open scoped Matrix.Norms.L2Operator in
private theorem opSq_conjugation {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ)) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    opSq ((U : (Matrix (Fin n) (Fin n) ℂ))ᴴ*A*(U : (Matrix (Fin n) (Fin n) ℂ))) = opSq A := by
  change ‖(U : (Matrix (Fin n) (Fin n) ℂ))ᴴ*A*(U : (Matrix (Fin n) (Fin n) ℂ))‖^2 = ‖A‖^2
  rw [CStarRing.norm_mul_coe_unitary _ U]
  have hn := CStarRing.norm_coe_unitary_mul (star U) A
  change ‖(U : (Matrix (Fin n) (Fin n) ℂ))ᴴ*A‖=‖A‖ at hn
  exact congrArg (fun r : ℝ => r^2) hn

private theorem translated_conjugation {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ)) (U : Matrix.unitaryGroup (Fin n) ℂ) (c : ℂ) :
    (U : (Matrix (Fin n) (Fin n) ℂ))ᴴ*(A-c•1)*(U : (Matrix (Fin n) (Fin n) ℂ)) = (U : (Matrix (Fin n) (Fin n) ℂ))ᴴ*A*(U : (Matrix (Fin n) (Fin n) ℂ))-c•1 := by
  have hu : (U : (Matrix (Fin n) (Fin n) ℂ))ᴴ*(U : (Matrix (Fin n) (Fin n) ℂ))=1 := Unitary.star_mul_self_of_mem U.property
  simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.mul_one,hu]

private theorem pure_variance_conjugation {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ))
    (U : Matrix.unitaryGroup (Fin n) ℂ) (w : EuclideanSpace ℂ (Fin n)) :
    variance ((U : (Matrix (Fin n) (Fin n) ℂ))ᴴ*A*(U : (Matrix (Fin n) (Fin n) ℂ))) ((Matrix.vecMulVec (WithLp.ofLp w) (star (WithLp.ofLp w)))) =
      variance A ((Matrix.vecMulVec (WithLp.ofLp (Matrix.toEuclideanLin (U : (Matrix (Fin n) (Fin n) ℂ)) w)) (star (WithLp.ofLp (Matrix.toEuclideanLin (U : (Matrix (Fin n) (Fin n) ℂ)) w))))) := by
  let C := (U : (Matrix (Fin n) (Fin n) ℂ))ᴴ*A*(U : (Matrix (Fin n) (Fin n) ℂ))
  have hs : Cᴴ=(U : (Matrix (Fin n) (Fin n) ℂ))ᴴ*Aᴴ*(U : (Matrix (Fin n) (Fin n) ℂ)) := by
    simp only [C,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]
  have h1 : ‖Matrix.toEuclideanLin C w‖ =
      ‖Matrix.toEuclideanLin A (Matrix.toEuclideanLin (U : (Matrix (Fin n) (Fin n) ℂ)) w)‖ := by
    rw [←unitary_vector_norm U (Matrix.toEuclideanLin C w),conjugation_intertwine]
  have h2 : ‖Matrix.toEuclideanLin Cᴴ w‖ =
      ‖Matrix.toEuclideanLin Aᴴ (Matrix.toEuclideanLin (U : (Matrix (Fin n) (Fin n) ℂ)) w)‖ := by
    rw [hs,←unitary_vector_norm U (Matrix.toEuclideanLin ((U : (Matrix (Fin n) (Fin n) ℂ))ᴴ*Aᴴ*(U : (Matrix (Fin n) (Fin n) ℂ))) w),
      conjugation_intertwine]
  have hi : inner ℂ w (Matrix.toEuclideanLin C w) =
      inner ℂ (Matrix.toEuclideanLin (U : (Matrix (Fin n) (Fin n) ℂ)) w)
        (Matrix.toEuclideanLin A (Matrix.toEuclideanLin (U : (Matrix (Fin n) (Fin n) ℂ)) w)) := by
    rw [←unitary_inner U w (Matrix.toEuclideanLin C w),conjugation_intertwine]
  rw [pure_variance_norms,pure_variance_norms,h1,h2,hi]

private theorem maximizing_block_frame {n : ℕ} (A : (Matrix (Fin (n+1)) (Fin (n+1)) ℂ)) :
    ∃ U : Matrix.unitaryGroup (Fin (n+1)) ℂ,
      2*(Complex.normSq (((U : (Matrix (Fin (n+1)) (Fin (n+1)) ℂ))ᴴ*A*(U : (Matrix (Fin (n+1)) (Fin (n+1)) ℂ))) 0 0)+
        RHLinalg.frobSq (((U : (Matrix (Fin (n+1)) (Fin (n+1)) ℂ))ᴴ*A*(U : (Matrix (Fin (n+1)) (Fin (n+1)) ℂ))).submatrix Fin.succ Fin.succ)) ≤ gap A := by
  obtain ⟨v,hv,hm⟩ := pure_variance_maximizer (by omega : 0<n+1) A
  obtain ⟨U,hU⟩ := exists_unitary_first_column v hv
  refine ⟨U,?_⟩
  let C := (U : (Matrix (Fin (n+1)) (Fin (n+1)) ℂ))ᴴ*A*(U : (Matrix (Fin (n+1)) (Fin (n+1)) ℂ))
  have hw : Matrix.toEuclideanLin (U : (Matrix (Fin (n+1)) (Fin (n+1)) ℂ)) (EuclideanSpace.single 0 1) = v := by
    ext i
    simp [Matrix.toEuclideanLin_apply,Matrix.mulVec,dotProduct,hU]
  have hc := commutator_norm_bound_of_pure (by omega : 0<n+1) A v
    (commutator_pure_max_bound A v hv hm)
  have he := pure_variance_conjugation A U (EuclideanSpace.single 0 1)
  rw [hw,pure_first_variance] at he
  rw [←he] at hc
  have hf : RHLinalg.frobSq C=RHLinalg.frobSq A := by
    dsimp only [C]
    rw [frobSq_unitary_right]
    exact frobSq_unitary_left A (star U)
  have hb := frobSq_block C
  rw [rectNorm_sq_square] at hb
  change 2*(Complex.normSq (C 0 0)+RHLinalg.frobSq (C.submatrix Fin.succ Fin.succ)) ≤ _
  rw [gap,←hf]
  rw [Complex.normSq_eq_norm_sq]
  change ‖commOperator A‖^2 ≤ 4*((((@norm (Matrix _ _ ℂ) Matrix.frobeniusSeminormedAddCommGroup.toNorm) ((fun (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) => A.submatrix (fun _ : Fin 1 => (0 : Fin (n+1))) Fin.succ) C))^2+‖(fun (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) => WithLp.toLp 2 (A.col 0 ∘ Fin.succ)) C‖^2)/2) at hc
  nlinarith

theorem gap_nonnegative : ∀ n (A : (Matrix (Fin n) (Fin n) ℂ)), 0 ≤ gap A := by
  intro n A
  cases n with
  | zero =>
    have hA : A=0 := by ext i; exact Fin.elim0 i
    subst A
    have hc : commOperator (0 : (Matrix (Fin 0) (Fin 0) ℂ))=0 := by ext w; simp [commOperator,LinearMap.sub_apply,LinearMap.mulLeft_apply,LinearMap.mulRight_apply,D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator]
    simp [gap,RHLinalg.frobSq,hc,Matrix.trace]
  | succ n =>
    obtain ⟨U,hU⟩ := maximizing_block_frame A
    exact le_trans (mul_nonneg (by norm_num) (add_nonneg (Complex.normSq_nonneg _) (frobSq_nonneg _))) hU

theorem translation_gap : (∀ n (A : (Matrix (Fin n) (Fin n) ℂ)) (c : ℂ), opSq (A - c • (1 : (Matrix (Fin n) (Fin n) ℂ))) ≤
    RHLinalg.frobSq A + 2 * Complex.normSq c + 2 * ‖c‖ * Real.sqrt (gap A)) := by
  intro n A c
  cases n with
  | zero =>
    have hA : A=0 := by ext i; exact Fin.elim0 i
    subst A
    have hM : (0 : (Matrix (Fin 0) (Fin 0) ℂ))-c•1=0 := by ext i; exact Fin.elim0 i
    rw [hM,opSq]
    simp only [map_zero]
    simp only [norm_zero,zero_pow (by decide : (2 : ℕ)≠0)]
    exact add_nonneg (add_nonneg (frobSq_nonneg _) (mul_nonneg (by norm_num) (Complex.normSq_nonneg _)))
      (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (Real.sqrt_nonneg _))
  | succ n =>
    obtain ⟨U,hU⟩ := maximizing_block_frame A
    have h := translation_from_block n ((U : (Matrix (Fin (n+1)) (Fin (n+1)) ℂ))ᴴ*A*(U : (Matrix (Fin (n+1)) (Fin (n+1)) ℂ))) (gap A) hU c
    rw [←translated_conjugation,opSq_conjugation,frobSq_unitary_right] at h
    have hf := frobSq_unitary_left A (star U)
    change RHLinalg.frobSq ((U : (Matrix (Fin (n+1)) (Fin (n+1)) ℂ))ᴴ*A)=RHLinalg.frobSq A at hf
    rw [hf] at h
    exact h

#print axioms blockNorm_domination
#print axioms frobSq_unitary_right
#print axioms opSq_le_frobSq
#print axioms gap_nonnegative
#print axioms translation_gap

end D5.S3.Quantum.Matrix.CommutatorGap
