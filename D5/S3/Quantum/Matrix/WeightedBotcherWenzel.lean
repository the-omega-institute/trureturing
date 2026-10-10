/- GID: D5/S3/Quantum/Matrix/WeightedBotcherWenzel
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/WeightedBotcherWenzel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive weights satisfy the weighted Bottcher-Wenzel bound in every dimension. -/

/-
admission_basis: escape-witness
proof_shape: weighted_add: bind-only; consumer: frobSq_projection_partition, weighted_two_level; escape_witness: none
proof_shape: weighted_smul: bind-only; consumer: reduction_to_two_level, weighted_sum, weighted_two_level; escape_witness: none
proof_shape: weighted_one: bind-only; consumer: frobSq_projection_partition, reduction_to_two_level, weighted_two_level; escape_witness: none
proof_shape: projected_trace: bind-only; consumer: frobSq_projection_partition, weighted_two_level; escape_witness: none
proof_shape: two_unitary_average_of_svd: bind-only; consumer: two_unitary_average; escape_witness: none
proof_shape: complement_projection: bind-only; consumer: frobSq_projection_partition; escape_witness: none
proof_shape: frobSq_projection_partition: bind-only; consumer: frobSq_project_le; escape_witness: none
proof_shape: frobSq_project_le: bind-only; consumer: frobSq_left_project_le, projection_adjoint_bound; escape_witness: none
proof_shape: frobSq_left_project_le: bind-only; consumer: projection_adjoint_bound; escape_witness: none
proof_shape: scalarPencil_shift_identity: bind-only; consumer: scalarPencil_rayleigh; escape_witness: none
proof_shape: scalarPencil_rayleigh: bind-only; consumer: scalarPencil_translation_bound; escape_witness: none
proof_shape: scalarPencil_translation_bound: bind-only; consumer: unitary_pencil_bound; escape_witness: none
proof_shape: unitary_spectral: bind-only; consumer: unitary_pencil_bound; escape_witness: none
proof_shape: frobSq_columns: bind-only; consumer: frobSq_left_operator_bound, unitary_pencil_bound; escape_witness: none
proof_shape: trace_pairing_columns: bind-only; consumer: unitary_pencil_bound; escape_witness: none
proof_shape: trace_pairing_unitary_right: bind-only; consumer: unitary_pencil_bound; escape_witness: none
proof_shape: pencil_unitary_coordinates: bind-only; consumer: unitary_pencil_bound; escape_witness: none
proof_shape: column_mul: bind-only; consumer: frobSq_left_operator_bound; escape_witness: none
proof_shape: column_right_diagonal: bind-only; consumer: pencil_diagonal_column; escape_witness: none
proof_shape: pencil_diagonal_column: bind-only; consumer: unitary_pencil_bound; escape_witness: none
proof_shape: unitary_pencil_bound: bind-only; consumer: contraction_pencil_bound; escape_witness: none
proof_shape: two_unitary_average: bind-only; consumer: scaled_unitary_average; escape_witness: none
proof_shape: scaled_unitary_average: bind-only; consumer: contraction_pencil_bound; escape_witness: none
proof_shape: pencil_average: bind-only; consumer: contraction_pencil_bound; escape_witness: none
proof_shape: contraction_pencil_bound: bind-only; consumer: projection_adjoint_bound; escape_witness: none
proof_shape: frobSq_left_operator_bound: bind-only; consumer: projection_K_quadratic; escape_witness: none
proof_shape: comm_pairing: bind-only; consumer: comm_adjoint_quadratic, projection_comm_pairing; escape_witness: none
proof_shape: projection_comm_pairing: bind-only; consumer: projection_channel_from_translation; escape_witness: none
proof_shape: comm_adjoint_quadratic: bind-only; consumer: projection_adjoint_bound; escape_witness: none
proof_shape: trace_projection_right: bind-only; consumer: projection_adjoint_bound; escape_witness: none
proof_shape: projected_gram_identity: bind-only; consumer: projection_adjoint_bound; escape_witness: none
proof_shape: projection_K_quadratic: bind-only; consumer: projection_adjoint_bound; escape_witness: none
proof_shape: projection_adjoint_bound: bind-only; consumer: projection_channel_from_translation; escape_witness: none
proof_shape: projection_channel_from_translation: bind-only; consumer: projection_gap; escape_witness: none
proof_shape: projection_gap: content; escape_witness: sphere_image_eq_ball_image, pure_of_density_linear_max, blochPure_surjective
proof_shape: defect_expansion: bind-only; consumer: two_level_defect; escape_witness: none
proof_shape: weighted_two_level: bind-only; consumer: two_level_defect; escape_witness: none
proof_shape: two_level_defect: bind-only; consumer: defect_lower_bound; escape_witness: none
proof_shape: weighted_sum: bind-only; consumer: transfer_nonnegative_combination; escape_witness: none
proof_shape: transfer_nonnegative_combination: bind-only; consumer: reduction_to_two_level; escape_witness: none
proof_shape: unit_cube_mem_convexHull: bind-only; consumer: unitary_diagonal_mem_projection_hull; escape_witness: none
proof_shape: unitary_diagonal_mem_projection_hull: bind-only; consumer: bounded_weight_decomposition; escape_witness: none
proof_shape: bounded_weight_decomposition: bind-only; consumer: reduction_to_two_level; escape_witness: none
proof_shape: reduction_to_two_level: bind-only; consumer: result_conditional; escape_witness: none
proof_shape: square_completion: bind-only; consumer: defect_lower_bound; escape_witness: none
proof_shape: defect_lower_bound: bind-only; consumer: two_level_from_projection_gap; escape_witness: none
proof_shape: gap_bound: bind-only; consumer: two_level_from_projection_gap; escape_witness: none
proof_shape: two_level_from_projection_gap: bind-only; consumer: result_conditional; escape_witness: none
proof_shape: result_conditional: bind-only; consumer: result; escape_witness: none
proof_shape: result: content; escape_witness: sphere_image_eq_ball_image, pure_of_density_linear_max, blochPure_surjective
escape_witness: result (the live constructive variance and translation chain)
Direct frozen dependencies:
  owner GID: D5/S3/Weil/ZetaLinear/PosIndex; declaration: RHLinalg.frobSq
    declaration statement_id: sha256:a1114d4731d26d6c5ef81acb0a254cdc6e0ed6e629ccb2dcf75d7faa00f4ccce
  owner GID: D5/S3/Observer/HiddenFlow/ProjectionCommutatorIdentity; declaration: D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator
    declaration statement_id: sha256:4b14c2bab713c5f81d97b9a10d285ee0878e4a933dc5a6b66387f846355b44aa
  owner GID: D5/S3/Quantum/BlockNorm/EssentiallyHermitian; declaration: Matrix.exists_mem_unitaryGroup_star_mul_mul_eq_diagonal
    declaration statement_id: sha256:d62beb8157c961473226b2c53ec1ff9177dff9c428778acd1b29bcc47be97cec
  baseline-frozen owner GID: D5/S3/Quantum/Foundation/FiniteTraceDistance; public declaration: D5.S3.Quantum.Foundation.FiniteTraceDistance.exists_svd_sqrt_eigenvalues
    declaration statement_id (producing Lean report): sha256:e079c550fa808a0eb9281e4fd4662a1ea12091a4328d1330c268597ffc16be91
  Other lane imports are same-delivery prerequisites, not baseline-frozen dependencies.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S3.Quantum.Matrix.CommutatorGap
import D5.S3.Quantum.Foundation.FiniteTraceDistance
import Mathlib.Analysis.CStarAlgebra.Unitary.Span

noncomputable section
open Matrix Set Unitary
open scoped ComplexInnerProductSpace ComplexOrder Matrix.Norms.L2Operator MatrixOrder ComplexStarModule
namespace D5.S3.Quantum.Matrix.WeightedBotcherWenzel
open D5.S3.Quantum.Matrix.NumericalRange
open D5.S3.Quantum.Matrix.CartesianVariance
open D5.S3.Quantum.Matrix.CommutatorGap
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum
open D5.S3.Quantum.Fibers.PhysicalFiber
open D5.S3.Quantum.Foundation.FiniteTraceDistance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

def weightedSq {n : ℕ} (A W : (Matrix (Fin n) (Fin n) ℂ)) : ℝ :=
  (Matrix.trace (Aᴴ * A * W)).re

theorem weighted_add {n : ℕ} (A W V : (Matrix (Fin n) (Fin n) ℂ)) :
    weightedSq A (W + V) = weightedSq A W + weightedSq A V := by
  simp [weightedSq, Matrix.mul_add, Matrix.trace_add]

theorem weighted_smul {n : ℕ} (A W : (Matrix (Fin n) (Fin n) ℂ)) (t : ℝ) :
    weightedSq A (t • W) = t * weightedSq A W := by
  simp [weightedSq, Matrix.trace_smul]

theorem weighted_one {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ)) : weightedSq A 1 = RHLinalg.frobSq A := by
  simp [weightedSq, RHLinalg.frobSq]

theorem projected_trace {n : ℕ} (A P : (Matrix (Fin n) (Fin n) ℂ)) (hP : ((P).IsHermitian ∧ P * P = P)) :
    weightedSq A P = RHLinalg.frobSq (A * P) := by
  rcases hP with ⟨hstar, hsq⟩
  unfold weightedSq RHLinalg.frobSq
  congr 1
  rw [Matrix.conjTranspose_mul, hstar.eq]
  calc
    Matrix.trace (Aᴴ * A * P) = Matrix.trace (Aᴴ * A * (P * P)) := by rw [hsq]
    _ = Matrix.trace (P * (Aᴴ * A) * P) := by
      rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
    _ = Matrix.trace (P * Aᴴ * (A * P)) := by simp only [Matrix.mul_assoc]

private theorem two_unitary_average_of_svd {n : ℕ} (H : (Matrix (Fin n) (Fin n) ℂ))
    (V W : Matrix.unitaryGroup (Fin n) ℂ) (σ : Fin n → ℝ)
    (hσ : ∀ i, ‖σ i‖ ≤ 1)
    (hH : H = (V : (Matrix (Fin n) (Fin n) ℂ)) * Matrix.diagonal (fun i => (σ i : ℂ)) * (W : (Matrix (Fin n) (Fin n) ℂ))ᴴ) :
    ∃ Uplus Uminus : Matrix.unitaryGroup (Fin n) ℂ,
      H = (1 / 2 : ℝ) • ((Uplus : (Matrix (Fin n) (Fin n) ℂ)) + (Uminus : (Matrix (Fin n) (Fin n) ℂ))) := by
  classical
  let S : selfAdjoint (Matrix (Fin n) (Fin n) ℂ) :=
    ⟨Matrix.diagonal (fun i => (σ i : ℂ)), by
      change IsSelfAdjoint (Matrix.diagonal (fun i => (σ i : ℂ)))
      rw [isSelfAdjoint_iff]
      rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
      congr 1
      funext i
      simp⟩
  have hS : ‖S‖ ≤ 1 := by
    change ‖Matrix.diagonal (fun i => (σ i : ℂ))‖ ≤ 1
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg (by norm_num)).mpr (by simpa using hσ)
  let Q := selfAdjoint.unitarySelfAddISMul S hS
  have hd : (S : Matrix (Fin n) (Fin n) ℂ) =
      (1 / 2 : ℝ) • ((Q : Matrix (Fin n) (Fin n) ℂ) + (star Q : Matrix (Fin n) (Fin n) ℂ)) := by
    have hr := congrArg (fun X : selfAdjoint (Matrix (Fin n) (Fin n) ℂ) => (X : Matrix (Fin n) (Fin n) ℂ))
      (selfAdjoint.realPart_unitarySelfAddISMul S hS)
    simpa only [Q, realPart_apply_coe, Unitary.coe_star, one_div] using hr.symm
  refine ⟨V * Q * star W, V * star Q * star W, ?_⟩
  change H = (1 / 2 : ℝ) •
    ((V : Matrix (Fin n) (Fin n) ℂ) * (Q : Matrix (Fin n) (Fin n) ℂ) * (W : Matrix (Fin n) (Fin n) ℂ)ᴴ +
     (V : Matrix (Fin n) (Fin n) ℂ) * (star Q : Matrix (Fin n) (Fin n) ℂ) * (W : Matrix (Fin n) (Fin n) ℂ)ᴴ)
  rw [hH, show Matrix.diagonal (fun i => (σ i : ℂ)) = _ from hd]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add]

private theorem complement_projection {n : ℕ} (P : (Matrix (Fin n) (Fin n) ℂ)) (hP : ((P).IsHermitian ∧ P * P = P)) :
    (((1-P)).IsHermitian ∧ (1-P) * (1-P) = (1-P)) := by
  refine ⟨?_,?_⟩
  · exact Matrix.isHermitian_one.sub hP.1
  · simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one,hP.2]
    abel

private theorem frobSq_projection_partition {n : ℕ} (A P : (Matrix (Fin n) (Fin n) ℂ)) (hP : ((P).IsHermitian ∧ P * P = P)) :
    RHLinalg.frobSq A = RHLinalg.frobSq (A*P)+RHLinalg.frobSq (A*(1-P)) := by
  rw [←projected_trace A P hP,←projected_trace A (1-P) (complement_projection P hP),
    ←weighted_add]
  simp [weighted_one]

private theorem frobSq_project_le {n : ℕ} (A P : (Matrix (Fin n) (Fin n) ℂ)) (hP : ((P).IsHermitian ∧ P * P = P)) :
    RHLinalg.frobSq (A*P) ≤ RHLinalg.frobSq A := by
  rw [frobSq_projection_partition A P hP]
  exact le_add_of_nonneg_right (frobSq_nonneg _)

private theorem frobSq_left_project_le {n : ℕ} (A P : (Matrix (Fin n) (Fin n) ℂ)) (hP : ((P).IsHermitian ∧ P * P = P)) :
    RHLinalg.frobSq (P*A) ≤ RHLinalg.frobSq A := by
  have h := frobSq_project_le Aᴴ P hP
  rw [←frobSq_star (P*A),Matrix.conjTranspose_mul,hP.1.eq]
  simpa only [frobSq_star] using h

private def scalarPencil {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ)) (c : ℂ) : (Matrix (Fin n) (Fin n) ℂ) :=
  A*Aᴴ-star c•A-c•Aᴴ

private theorem scalarPencil_shift_identity {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ)) (c : ℂ) :
    scalarPencil A c = (A-c•1)*(A-c•1)ᴴ-(Complex.normSq c : ℂ)•1 := by
  simp only [scalarPencil,Matrix.conjTranspose_sub,Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,
    Matrix.smul_mul,Matrix.one_mul,Matrix.mul_one,smul_sub,smul_smul]
  have hc : star c*c = (Complex.normSq c : ℂ) := by
    simpa [Complex.star_def,mul_comm] using (Complex.normSq_eq_conj_mul_self (z := c)).symm
  rw [hc]
  module

private theorem scalarPencil_rayleigh {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ)) (c : ℂ)
    (v : EuclideanSpace ℂ (Fin n)) :
    (inner ℂ v (Matrix.toEuclideanLin (scalarPencil A c) v)).re ≤
      (opSq (A-c•1)-Complex.normSq c)*‖v‖^2 := by
  let B := A-c•(1 : (Matrix (Fin n) (Fin n) ℂ))
  let T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) B
  have hstar : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) Bᴴ = T.adjoint :=
    map_star (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) B
  have hprod : Matrix.toEuclideanLin (B*Bᴴ) v = T (T.adjoint v) := by
    have h := map_mul (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) B Bᴴ
    have he := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) => L v) h
    change Matrix.toEuclideanLin (B*Bᴴ) v = T ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) Bᴴ) v) at he
    rw [hstar] at he
    exact he
  have hquad : (inner ℂ v (Matrix.toEuclideanLin (scalarPencil A c) v)).re =
      ‖T.adjoint v‖^2-Complex.normSq c*‖v‖^2 := by
    rw [scalarPencil_shift_identity]
    simp only [map_sub,map_smul,Matrix.toLpLin_one,LinearMap.sub_apply,
      LinearMap.smul_apply,LinearMap.id_apply,inner_sub_right,inner_smul_right]
    change (inner ℂ v (Matrix.toEuclideanLin (B*Bᴴ) v)).re-
      ((Complex.normSq c : ℂ)*inner ℂ v v).re = _
    rw [hprod,←ContinuousLinearMap.adjoint_inner_left,inner_self_eq_norm_sq_to_K,
      inner_self_eq_norm_sq_to_K]
    simp [pow_two,Complex.mul_re]
  have h := T.adjoint.le_opNorm v
  have hn : ‖T.adjoint‖ = ‖T‖ := ContinuousLinearMap.adjoint.norm_map T
  rw [hn] at h
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  have he : ‖T‖^2 = opSq (A-c•1) := rfl
  rw [mul_pow,he] at hs
  rw [hquad]
  nlinarith

private theorem scalarPencil_translation_bound {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ)) (c : ℂ) (d : ℝ)
    (h : opSq (A-c•1) ≤ RHLinalg.frobSq A+2*Complex.normSq c+2*‖c‖*Real.sqrt d)
    (v : EuclideanSpace ℂ (Fin n)) :
    (inner ℂ v (Matrix.toEuclideanLin (scalarPencil A c) v)).re ≤
      (RHLinalg.frobSq A+Complex.normSq c+2*‖c‖*Real.sqrt d)*‖v‖^2 := by
  have hp := mul_le_mul_of_nonneg_right h (sq_nonneg ‖v‖)
  exact (scalarPencil_rayleigh A c v).trans (by nlinarith)

private theorem unitary_spectral {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ Q : Matrix.unitaryGroup (Fin n) ℂ, ∃ ζ : Fin n → ℂ,
      (∀ i, ‖ζ i‖ = 1) ∧
      (U : (Matrix (Fin n) (Fin n) ℂ)) = (Q : (Matrix (Fin n) (Fin n) ℂ))*Matrix.diagonal ζ*(Q : (Matrix (Fin n) (Fin n) ℂ))ᴴ := by
  classical
  let X := (U : Matrix (Fin n) (Fin n) ℂ)
  letI : IsStarNormal X := ⟨by
    change star X * X = X * star X
    exact (Unitary.star_mul_self_of_mem U.property).trans
      (Unitary.mul_star_self_of_mem U.property).symm⟩
  obtain ⟨Q,hQ,ζ,hζ⟩ := Matrix.exists_mem_unitaryGroup_star_mul_mul_eq_diagonal X
  let V : Matrix.unitaryGroup (Fin n) ℂ := ⟨Q,hQ⟩
  have he : X = Q * Matrix.diagonal ζ * Qᴴ := by
    calc
      X = (Q*star Q)*X*(Q*star Q) := by
        rw [Unitary.mul_star_self_of_mem hQ]
        simp
      _ = Q*(star Q*X*Q)*star Q := by simp only [Matrix.mul_assoc]
      _ = Q*Matrix.diagonal ζ*Qᴴ := by rw [hζ]; rfl

  refine ⟨V,ζ,?_,he⟩
  intro i
  have hd : Matrix.diagonal ζ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [←hζ]
    exact mul_mem (mul_mem (star_mem hQ) U.property) hQ
  have hh := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp hd) i) i
  have hz : star (ζ i)*ζ i = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.one_apply_eq,
      starRingEnd_apply, Pi.star_apply] using hh
  have hn := congrArg norm hz
  rw [norm_mul,norm_star,norm_one] at hn
  nlinarith [norm_nonneg (ζ i)]

private def pencil {n : ℕ} (A H Y : (Matrix (Fin n) (Fin n) ℂ)) : (Matrix (Fin n) (Fin n) ℂ) :=
  A*Aᴴ*Y-A*Y*Hᴴ-Aᴴ*Y*H

private theorem frobSq_columns {n : ℕ} (Y : (Matrix (Fin n) (Fin n) ℂ)) : RHLinalg.frobSq Y = ∑ j, ‖(fun (Y : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) => WithLp.toLp 2 (Y.col j)) Y j‖^2 := by
  simp only [frobSq_eq_sum,EuclideanSpace.norm_sq_eq,Matrix.col,
    Matrix.transpose_apply,Complex.normSq_eq_norm_sq]

private theorem trace_pairing_columns {n : ℕ} (Y Z : (Matrix (Fin n) (Fin n) ℂ)) :
    Matrix.trace (Yᴴ*Z) = ∑ j, inner ℂ ((fun (Y : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) => WithLp.toLp 2 (Y.col j)) Y j) ((fun (Y : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) => WithLp.toLp 2 (Y.col j)) Z j)  := by
  have h := matrix_pairing Y Z
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  change (∑ ij : Fin n × Fin n, Z ij.1 ij.2 * star (Y ij.1 ij.2)) =
    Matrix.trace (Yᴴ * Z) at h
  rw [Fintype.sum_prod_type, Finset.sum_comm] at h
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Matrix.col,
    Matrix.transpose_apply, Pi.star_apply] using h.symm

private theorem trace_pairing_unitary_right {n : ℕ} (Y Z : (Matrix (Fin n) (Fin n) ℂ)) (Q : Matrix.unitaryGroup (Fin n) ℂ) :
    Matrix.trace ((Y*(Q : (Matrix (Fin n) (Fin n) ℂ)))ᴴ*(Z*(Q : (Matrix (Fin n) (Fin n) ℂ)))) = Matrix.trace (Yᴴ*Z) := by
  have h := Matrix.trace_units_conj' (Unitary.toUnits Q) (Yᴴ * Z)
  change Matrix.trace ((Q : Matrix (Fin n) (Fin n) ℂ)ᴴ * (Yᴴ * Z) * (Q : Matrix (Fin n) (Fin n) ℂ)) = Matrix.trace (Yᴴ * Z) at h
  simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using h

private theorem pencil_unitary_coordinates {n : ℕ} (A Y : (Matrix (Fin n) (Fin n) ℂ)) (r : ℝ)
    (U Q : Matrix.unitaryGroup (Fin n) ℂ) (ζ : Fin n → ℂ)
    (hU : (U : (Matrix (Fin n) (Fin n) ℂ)) = (Q : (Matrix (Fin n) (Fin n) ℂ))*Matrix.diagonal ζ*(Q : (Matrix (Fin n) (Fin n) ℂ))ᴴ) :
    pencil A (r•(U : (Matrix (Fin n) (Fin n) ℂ))) Y*(Q : (Matrix (Fin n) (Fin n) ℂ)) =
      pencil A (r•Matrix.diagonal ζ) (Y*(Q : (Matrix (Fin n) (Fin n) ℂ))) := by
  have hQ : (Q : (Matrix (Fin n) (Fin n) ℂ))ᴴ*(Q : (Matrix (Fin n) (Fin n) ℂ)) = 1 := Unitary.star_mul_self_of_mem Q.property
  simp only [pencil,hU,Matrix.conjTranspose_smul,star_trivial,
    Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.sub_mul,
    Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_assoc,hQ,Matrix.mul_one]

private theorem column_mul {n : ℕ} (X Y : (Matrix (Fin n) (Fin n) ℂ)) (j : Fin n) :
    (fun (Y : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) => WithLp.toLp 2 (Y.col j)) (X*Y) j = Matrix.toEuclideanLin X ((fun (Y : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) => WithLp.toLp 2 (Y.col j)) Y j) := rfl

private theorem column_right_diagonal {n : ℕ} (Y : (Matrix (Fin n) (Fin n) ℂ)) (ζ : Fin n → ℂ) (j : Fin n) :
    (fun (Y : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) => WithLp.toLp 2 (Y.col j)) (Y*Matrix.diagonal ζ) j = ζ j•(fun (Y : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) => WithLp.toLp 2 (Y.col j)) Y j := by
  ext i
  simp [Matrix.mul_diagonal,mul_comm]

private theorem pencil_diagonal_column {n : ℕ} (A Y : (Matrix (Fin n) (Fin n) ℂ)) (r : ℝ) (ζ : Fin n → ℂ) (j : Fin n) :
    (fun (Y : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) => WithLp.toLp 2 (Y.col j)) (pencil A (r•Matrix.diagonal ζ) Y) j =
      Matrix.toEuclideanLin (scalarPencil A ((r : ℂ)*ζ j)) ((fun (Y : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) => WithLp.toLp 2 (Y.col j)) Y j) := by
  have hsub (X Z : Matrix (Fin n) (Fin n) ℂ) (k : Fin n) :
      (fun (Y : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) => WithLp.toLp 2 (Y.col j)) (X-Z) k = (fun (Y : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) => WithLp.toLp 2 (Y.col j)) X k-(fun (Y : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) => WithLp.toLp 2 (Y.col j)) Z k := rfl
  have hsmul (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (k : Fin n) :
      (fun (Y : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) => WithLp.toLp 2 (Y.col j)) (t•X) k = t•(fun (Y : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) => WithLp.toLp 2 (Y.col j)) X k := rfl
  simp only [pencil,Matrix.conjTranspose_smul,star_trivial,
    Matrix.diagonal_conjTranspose,Matrix.mul_smul,hsub,hsmul,
    column_right_diagonal]
  simp only [column_mul,scalarPencil,map_sub,map_smul,
    LinearMap.sub_apply,LinearMap.smul_apply,Pi.star_apply,star_mul,
    Complex.star_def,Complex.conj_ofReal]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),smul_smul]
  module

private theorem unitary_pencil_bound {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ)) (d r : ℝ) (hr : 0 ≤ r)
    (htrans : ∀ c : ℂ, opSq (A-c•1) ≤ RHLinalg.frobSq A+2*Complex.normSq c+2*‖c‖*Real.sqrt d)
    (U : Matrix.unitaryGroup (Fin n) ℂ) (Y : (Matrix (Fin n) (Fin n) ℂ)) :
    (Matrix.trace (Yᴴ*pencil A (r•(U : (Matrix (Fin n) (Fin n) ℂ))) Y)).re ≤
      (RHLinalg.frobSq A+r^2+2*r*Real.sqrt d)*RHLinalg.frobSq Y := by
  obtain ⟨Q,ζ,hζ,hU⟩ := unitary_spectral U
  calc
    _ = (Matrix.trace ((Y*(Q : (Matrix (Fin n) (Fin n) ℂ)))ᴴ*(pencil A (r•(U : (Matrix (Fin n) (Fin n) ℂ))) Y*(Q : (Matrix (Fin n) (Fin n) ℂ))))).re :=
      congrArg Complex.re (trace_pairing_unitary_right Y _ Q).symm
    _ = ∑ j, (inner ℂ ((fun (Y : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) => WithLp.toLp 2 (Y.col j)) (Y*(Q : (Matrix (Fin n) (Fin n) ℂ))) j)
        (Matrix.toEuclideanLin (scalarPencil A ((r : ℂ)*ζ j)) ((fun (Y : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) => WithLp.toLp 2 (Y.col j)) (Y*(Q : (Matrix (Fin n) (Fin n) ℂ))) j))).re := by
      rw [pencil_unitary_coordinates A Y r U Q ζ hU,trace_pairing_columns]
      simp only [Complex.re_sum,pencil_diagonal_column]
    _ ≤ ∑ j, (RHLinalg.frobSq A+r^2+2*r*Real.sqrt d)*‖(fun (Y : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) => WithLp.toLp 2 (Y.col j)) (Y*(Q : (Matrix (Fin n) (Fin n) ℂ))) j‖^2 := by
      apply Finset.sum_le_sum
      intro j _
      have hc : ‖(r : ℂ)*ζ j‖ = r := by
        rw [norm_mul,Complex.norm_real,hζ j,Real.norm_eq_abs,abs_of_nonneg hr,mul_one]
      have hs : Complex.normSq ((r : ℂ)*ζ j) = r^2 := by rw [Complex.normSq_eq_norm_sq,hc]
      simpa only [hc,hs] using scalarPencil_translation_bound A ((r : ℂ)*ζ j) d
        (htrans _) ((fun (Y : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) => WithLp.toLp 2 (Y.col j)) (Y*(Q : (Matrix (Fin n) (Fin n) ℂ))) j)
    _ = (RHLinalg.frobSq A+r^2+2*r*Real.sqrt d)*RHLinalg.frobSq (Y*(Q : (Matrix (Fin n) (Fin n) ℂ))) := by
      rw [←Finset.mul_sum,←frobSq_columns]
    _ = _ := by rw [frobSq_unitary_right]

private theorem two_unitary_average : (∀ n (H : (Matrix (Fin n) (Fin n) ℂ)), opSq H ≤ 1 → ∃ U V : Matrix.unitaryGroup (Fin n) ℂ,
    H = (1 / 2 : ℝ) • ((U : (Matrix (Fin n) (Fin n) ℂ)) + (V : (Matrix (Fin n) (Fin n) ℂ)))) := by
  intro n H hH
  classical
  let hS : (Hᴴ*H).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self H
  obtain ⟨V,W,hsvd⟩ : ∃ V W : Matrix.unitaryGroup (Fin n) ℂ,
      H = (V : (Matrix (Fin n) (Fin n) ℂ))*Matrix.diagonal (fun i => (Real.sqrt (hS.eigenvalues i) : ℂ))*(W : (Matrix (Fin n) (Fin n) ℂ))ᴴ := by
    simpa [hS] using exists_svd_sqrt_eigenvalues H
  have hop : ‖H‖ ≤ 1 := by
    have he : opSq H = ‖H‖^2 := rfl
    rw [he] at hH
    nlinarith [norm_nonneg H]
  have hn : ‖fun i => (Real.sqrt (hS.eigenvalues i) : ℂ)‖ = ‖H‖ := by
    calc
      _ = ‖Matrix.diagonal (fun i => (Real.sqrt (hS.eigenvalues i) : ℂ))‖ :=
        (Matrix.l2_opNorm_diagonal _).symm
      _ = ‖(V : (Matrix (Fin n) (Fin n) ℂ))*Matrix.diagonal (fun i => (Real.sqrt (hS.eigenvalues i) : ℂ))‖ :=
        (CStarRing.norm_coe_unitary_mul V _).symm
      _ = ‖(V : (Matrix (Fin n) (Fin n) ℂ))*Matrix.diagonal (fun i => (Real.sqrt (hS.eigenvalues i) : ℂ))*(W : (Matrix (Fin n) (Fin n) ℂ))ᴴ‖ := by
        exact (CStarRing.norm_mul_coe_unitary _ (star W)).symm
      _ = ‖H‖ := congrArg norm hsvd.symm
  apply two_unitary_average_of_svd H V W (fun i => Real.sqrt (hS.eigenvalues i)) _ hsvd
  intro i
  have h := (norm_le_pi_norm (fun i => (Real.sqrt (hS.eigenvalues i) : ℂ)) i).trans (hn.trans_le hop)
  simpa only [Complex.norm_real] using h

private theorem scaled_unitary_average {n : ℕ} (H : (Matrix (Fin n) (Fin n) ℂ)) (r : ℝ)
    (hr : 0 ≤ r) (hH : opSq H ≤ r^2) :
    ∃ U V : Matrix.unitaryGroup (Fin n) ℂ,
      H = (1/2 : ℝ)•(r•(U : (Matrix (Fin n) (Fin n) ℂ))+r•(V : (Matrix (Fin n) (Fin n) ℂ))) := by
  have hn : ‖H‖ ≤ r := (sq_le_sq₀ (norm_nonneg H) hr).mp hH
  by_cases hz : r=0
  · subst r
    have h0 : H=0 := norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
    exact ⟨1,1,by simp [h0]⟩
  · have hp : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
    have hc : opSq (r⁻¹•H) ≤ 1 := by
      change ‖r⁻¹•H‖^2 ≤ 1
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)]
      have h : r⁻¹*‖H‖ ≤ 1 := by
        calc
          _ ≤ r⁻¹*r := mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hr)
          _ = 1 := inv_mul_cancel₀ hz
      nlinarith [mul_nonneg (inv_nonneg.mpr hr) (norm_nonneg H)]
    obtain ⟨U,V,hUV⟩ := two_unitary_average n (r⁻¹•H) hc
    refine ⟨U,V,?_⟩
    have he := congrArg (fun X : (Matrix (Fin n) (Fin n) ℂ) => r•X) hUV
    simpa only [smul_smul,mul_inv_cancel₀ hz,one_smul,smul_add,mul_comm r (1/2)] using he

private theorem pencil_average {n : ℕ} (A Y : (Matrix (Fin n) (Fin n) ℂ)) (r : ℝ)
    (U V : Matrix.unitaryGroup (Fin n) ℂ) :
    pencil A ((1/2 : ℝ)•(r•(U : (Matrix (Fin n) (Fin n) ℂ))+r•(V : (Matrix (Fin n) (Fin n) ℂ)))) Y =
      (1/2 : ℝ)•(pencil A (r•(U : (Matrix (Fin n) (Fin n) ℂ))) Y+pencil A (r•(V : (Matrix (Fin n) (Fin n) ℂ))) Y) := by
  simp only [pencil,Matrix.conjTranspose_smul,star_trivial,Matrix.conjTranspose_add,
    Matrix.mul_smul,Matrix.mul_add,smul_add]
  module

private theorem contraction_pencil_bound {n : ℕ} (A H Y : (Matrix (Fin n) (Fin n) ℂ)) (d r : ℝ)
    (hr : 0 ≤ r) (hH : opSq H ≤ r^2)
    (htrans : ∀ c : ℂ, opSq (A-c•1) ≤ RHLinalg.frobSq A+2*Complex.normSq c+2*‖c‖*Real.sqrt d) :
    (Matrix.trace (Yᴴ*pencil A H Y)).re ≤
      (RHLinalg.frobSq A+r^2+2*r*Real.sqrt d)*RHLinalg.frobSq Y := by
  obtain ⟨U,V,hUV⟩ := scaled_unitary_average H r hr hH
  have hU := unitary_pencil_bound A d r hr htrans U Y
  have hV := unitary_pencil_bound A d r hr htrans V Y
  have he : (Matrix.trace (Yᴴ*pencil A H Y)).re =
      (1/2 : ℝ)*((Matrix.trace (Yᴴ*pencil A (r•(U : (Matrix (Fin n) (Fin n) ℂ))) Y)).re+
        (Matrix.trace (Yᴴ*pencil A (r•(V : (Matrix (Fin n) (Fin n) ℂ))) Y)).re) := by
    rw [hUV,pencil_average]
    simp [Matrix.mul_smul,Matrix.mul_add,Matrix.trace_smul,Matrix.trace_add,Complex.real_smul]
    ring
  rw [he]
  linarith

private theorem frobSq_left_operator_bound {n : ℕ} (A Y : (Matrix (Fin n) (Fin n) ℂ)) :
    RHLinalg.frobSq (A*Y) ≤ opSq A*RHLinalg.frobSq Y := by
  rw [frobSq_columns,frobSq_columns,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [column_mul]
  have h := (Matrix.toEuclideanLin A).toContinuousLinearMap.le_opNorm ((fun (Y : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) => WithLp.toLp 2 (Y.col j)) Y j)
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  change ‖(Matrix.toEuclideanLin A) ((fun (Y : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) => WithLp.toLp 2 (Y.col j)) Y j)‖^2 ≤ _ at hs
  rw [mul_pow] at hs
  exact hs

private theorem comm_pairing {n : ℕ} (A B Z : (Matrix (Fin n) (Fin n) ℂ)) :
    Matrix.trace ((D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B)ᴴ*Z) =
      Matrix.trace (Bᴴ*D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator Aᴴ Z) := by
  simp only [D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator,Matrix.conjTranspose_sub,Matrix.conjTranspose_mul,
    Matrix.mul_sub,Matrix.sub_mul,Matrix.trace_sub]
  have hc : Matrix.trace (Aᴴ*Bᴴ*Z) = Matrix.trace (Bᴴ*Z*Aᴴ) := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm Aᴴ (Bᴴ*Z)
  rw [hc]
  simp only [Matrix.mul_assoc]

private theorem projection_comm_pairing {n : ℕ} (A B P Y : (Matrix (Fin n) (Fin n) ℂ))
    (hP : ((P).IsHermitian ∧ P * P = P)) :
    Matrix.trace ((D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B*P)ᴴ*Y) =
      Matrix.trace (Bᴴ*D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator Aᴴ (Y*P)) := by
  rw [Matrix.conjTranspose_mul,hP.1.eq]
  have hc := Matrix.trace_mul_comm P ((D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B)ᴴ*Y)
  rw [Matrix.mul_assoc,hc,Matrix.mul_assoc,comm_pairing]

private theorem comm_adjoint_quadratic {n : ℕ} (A Z : (Matrix (Fin n) (Fin n) ℂ)) :
    RHLinalg.frobSq (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator Aᴴ Z) =
      (Matrix.trace (Zᴴ*D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator Aᴴ Z))).re := by
  have hc := comm_pairing A (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator Aᴴ Z) Z
  have he : (Matrix.trace ((D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator Aᴴ Z))ᴴ*Z)).re =
      (Matrix.trace (Zᴴ*D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator Aᴴ Z))).re := by
    rw [←matrix_pairing,←matrix_pairing]
    exact inner_re_symm (𝕜 := ℂ) _ _
  rw [←he,hc]
  rfl

private theorem trace_projection_right {n : ℕ} (Z X P : (Matrix (Fin n) (Fin n) ℂ))
    (hP : ((P).IsHermitian ∧ P * P = P)) (hZ : Z*P=Z) :
    Matrix.trace (Zᴴ*X) = Matrix.trace (Zᴴ*(X*P)) := by
  have hs : P*Zᴴ=Zᴴ := by
    have h := congrArg Matrix.conjTranspose hZ
    simpa only [Matrix.conjTranspose_mul,hP.1.eq] using h
  calc
    _ = Matrix.trace (P*Zᴴ*X) := by rw [hs]
    _ = Matrix.trace ((Zᴴ*X)*P) := by
      simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm P (Zᴴ*X)
    _ = _ := by simp only [Matrix.mul_assoc]

private theorem projected_gram_identity {n : ℕ} (A Z P : (Matrix (Fin n) (Fin n) ℂ))
    (hP : ((P).IsHermitian ∧ P * P = P)) (hZ : Z*P=Z) :
    D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator Aᴴ Z)*P =
      pencil A (P*A*P) Z+Z*(P*Aᴴ*A*P) := by
  have hZX : ∀ X : (Matrix (Fin n) (Fin n) ℂ), Z*(P*X)=Z*X := by
    intro X
    rw [←Matrix.mul_assoc,hZ]
  simp only [D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator,pencil,Matrix.conjTranspose_mul,hP.1.eq,
    Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc,hZ,hZX]
  abel

private theorem projection_K_quadratic {n : ℕ} (A Z P : (Matrix (Fin n) (Fin n) ℂ))
    (hP : ((P).IsHermitian ∧ P * P = P)) :
    (Matrix.trace (Zᴴ*(Z*(P*Aᴴ*A*P)))).re ≤ RHLinalg.frobSq (A*P)*RHLinalg.frobSq Z := by
  have he : (Matrix.trace (Zᴴ*(Z*(P*Aᴴ*A*P)))).re = RHLinalg.frobSq ((A*P)*Zᴴ) := by
    unfold RHLinalg.frobSq
    simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hP.1.eq]
    congr 1
    calc
      _ = Matrix.trace (Zᴴ*Z*((A*P)ᴴ*(A*P))) := by
        simp only [Matrix.conjTranspose_mul,hP.1.eq,Matrix.mul_assoc]
      _ = Matrix.trace (Z*((A*P)ᴴ*(A*P))*Zᴴ) := by
        simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm Zᴴ (Z*((A*P)ᴴ*(A*P)))
      _ = _ := by simp only [Matrix.conjTranspose_mul,hP.1.eq,Matrix.mul_assoc]
  rw [he]
  exact (frobSq_left_operator_bound (A*P) Zᴴ).trans (by
    rw [frobSq_star]
    exact mul_le_mul_of_nonneg_right (opSq_le_frobSq _) (frobSq_nonneg Z))

private theorem projection_adjoint_bound {n : ℕ} (A P Y : (Matrix (Fin n) (Fin n) ℂ)) (d : ℝ)
    (hP : ((P).IsHermitian ∧ P * P = P))
    (htrans : ∀ c : ℂ, opSq (A-c•1) ≤ RHLinalg.frobSq A+2*Complex.normSq c+2*‖c‖*Real.sqrt d) :
    RHLinalg.frobSq (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator Aᴴ (Y*P)) ≤
      (RHLinalg.frobSq A+2*RHLinalg.frobSq (A*P)+2*Real.sqrt (RHLinalg.frobSq (A*P))*Real.sqrt d)*RHLinalg.frobSq Y := by
  let Z := Y*P
  let b := RHLinalg.frobSq (A*P)
  let C := RHLinalg.frobSq A+2*b+2*Real.sqrt b*Real.sqrt d
  have hZ : Z*P=Z := by simp only [Z,Matrix.mul_assoc,hP.2]
  have hH : opSq (P*A*P) ≤ (Real.sqrt b)^2 := by
    rw [Real.sq_sqrt (frobSq_nonneg (A*P))]
    exact (opSq_le_frobSq _).trans (by
      simpa only [Matrix.mul_assoc,b] using frobSq_left_project_le (A*P) P hP)
  have hp := contraction_pencil_bound A (P*A*P) Z d (Real.sqrt b)
    (Real.sqrt_nonneg _) hH htrans
  rw [Real.sq_sqrt (frobSq_nonneg (A*P))] at hp
  have hk := projection_K_quadratic A Z P hP
  have hquad : RHLinalg.frobSq (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator Aᴴ Z) ≤ C*RHLinalg.frobSq Z := by
    rw [comm_adjoint_quadratic,trace_projection_right Z _ P hP hZ,
      projected_gram_identity A Z P hP hZ,Matrix.mul_add,Matrix.trace_add,Complex.add_re]
    dsimp [C,b] at *
    linarith
  have hC : 0 ≤ C := by
    dsimp [C,b]
    exact add_nonneg (add_nonneg (frobSq_nonneg _) (mul_nonneg (by norm_num) (frobSq_nonneg _)))
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  exact hquad.trans (mul_le_mul_of_nonneg_left (frobSq_project_le Y P hP) hC)

private theorem projection_channel_from_translation {n : ℕ} (A B P : (Matrix (Fin n) (Fin n) ℂ)) (d : ℝ)
    (hP : ((P).IsHermitian ∧ P * P = P))
    (htrans : ∀ c : ℂ, opSq (A-c•1) ≤ RHLinalg.frobSq A+2*Complex.normSq c+2*‖c‖*Real.sqrt d) :
    RHLinalg.frobSq (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B*P) ≤
      (RHLinalg.frobSq A+2*RHLinalg.frobSq (A*P)+2*Real.sqrt (RHLinalg.frobSq (A*P)*d))*RHLinalg.frobSq B := by
  let Y := D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B*P
  let C := RHLinalg.frobSq A+2*RHLinalg.frobSq (A*P)+2*Real.sqrt (RHLinalg.frobSq (A*P))*Real.sqrt d
  have ha := projection_adjoint_bound A P Y d hP htrans
  have hc := trace_product_cauchy Bᴴ (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator Aᴴ (Y*P))
  rw [frobSq_star,←projection_comm_pairing A B P Y hP] at hc
  have hre : (Matrix.trace ((D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B*P)ᴴ*Y)).re = RHLinalg.frobSq Y := rfl
  have hs : (RHLinalg.frobSq Y)^2 ≤ Complex.normSq (Matrix.trace ((D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B*P)ᴴ*Y)) := by
    rw [Complex.normSq_apply,hre]
    nlinarith [sq_nonneg (Matrix.trace ((D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B*P)ᴴ*Y)).im]
  have hm := mul_le_mul_of_nonneg_left ha (frobSq_nonneg B)
  have h : (RHLinalg.frobSq Y)^2 ≤ RHLinalg.frobSq Y*(C*RHLinalg.frobSq B) := by
    dsimp [C] at *
    nlinarith
  have hfinal : RHLinalg.frobSq Y ≤ C*RHLinalg.frobSq B := by
    by_cases hy : RHLinalg.frobSq Y=0
    · rw [hy]
      dsimp [C]
      exact mul_nonneg (add_nonneg (add_nonneg (frobSq_nonneg _)
        (mul_nonneg (by norm_num) (frobSq_nonneg _)))
        (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)))
        (frobSq_nonneg _)
    · exact le_of_mul_le_mul_left (by simpa only [pow_two] using h)
        (lt_of_le_of_ne (frobSq_nonneg Y) (Ne.symm hy))
  simpa only [C,Real.sqrt_mul (frobSq_nonneg (A*P)),Y,mul_assoc] using hfinal

theorem projection_gap : (∀ n (A B P : (Matrix (Fin n) (Fin n) ℂ)), ((P).IsHermitian ∧ P * P = P) →
    RHLinalg.frobSq (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B * P) ≤
      (RHLinalg.frobSq A + 2 * RHLinalg.frobSq (A * P) +
        2 * Real.sqrt (RHLinalg.frobSq (A * P) * gap A)) * RHLinalg.frobSq B) := by
  intro n A B P hP
  exact projection_channel_from_translation A B P (gap A) hP (translation_gap n A)


def SpectralExtrema {n : ℕ} (W : (Matrix (Fin n) (Fin n) ℂ)) (lo hi : ℝ) : Prop :=
  ∃ h : W.IsHermitian,
    (∀ i, lo ≤ h.eigenvalues i ∧ h.eigenvalues i ≤ hi) ∧
    (∃ i, h.eigenvalues i = lo) ∧ (∃ i, h.eigenvalues i = hi)

private theorem defect_expansion (a b u c d s : ℝ) :
    (2 + s) * (a + s * b) * u - (c + s * d) =
      (2 * a * u - c) + s * ((a + 2 * b) * u - d) + s ^ 2 * (b * u) := by
  ring

private theorem weighted_two_level {n : ℕ} (A P : (Matrix (Fin n) (Fin n) ℂ)) (s : ℝ)
    (hP : ((P).IsHermitian ∧ P * P = P)) :
    weightedSq A (1 + s • P) = RHLinalg.frobSq A + s * RHLinalg.frobSq (A * P) := by
  rw [weighted_add, weighted_one, weighted_smul, projected_trace A P hP]

private theorem two_level_defect {n : ℕ} (A B P : (Matrix (Fin n) (Fin n) ℂ)) (s : ℝ)
    (hP : ((P).IsHermitian ∧ P * P = P)) :
    (2 + s) * weightedSq A (1 + s • P) * RHLinalg.frobSq B -
      weightedSq (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B) (1 + s • P) =
      (2 * RHLinalg.frobSq A * RHLinalg.frobSq B - RHLinalg.frobSq (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B)) +
        s * ((RHLinalg.frobSq A + 2 * RHLinalg.frobSq (A * P)) * RHLinalg.frobSq B - RHLinalg.frobSq (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B * P)) +
        s ^ 2 * (RHLinalg.frobSq (A * P) * RHLinalg.frobSq B) := by
  rw [weighted_two_level A P s hP, weighted_two_level (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B) P s hP]
  exact defect_expansion _ _ _ _ _ _

private def weightedLinear {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ)) : (Matrix (Fin n) (Fin n) ℂ) →ₗ[ℝ] ℝ :=
  Complex.reLm.comp ((Matrix.traceLinearMap (Fin n) ℝ ℂ).comp
    (LinearMap.mulLeft ℝ (Aᴴ * A)))

private theorem weighted_sum {n : ℕ} {ι : Type*} (A : (Matrix (Fin n) (Fin n) ℂ)) (S : Finset ι)
    (t : ι → ℝ) (W : ι → (Matrix (Fin n) (Fin n) ℂ)) :
    weightedSq A (∑ i ∈ S, t i • W i) = ∑ i ∈ S, t i * weightedSq A (W i) := by
  calc
    weightedSq A (∑ i ∈ S, t i • W i) =
        ∑ i ∈ S, weightedSq A (t i • W i) := map_sum (weightedLinear A) _ S
    _ = ∑ i ∈ S, t i * weightedSq A (W i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact weighted_smul A (W i) (t i)

private theorem transfer_nonnegative_combination {n : ℕ} {ι : Type*}
    (A B : (Matrix (Fin n) (Fin n) ℂ)) (S : Finset ι) (t : ι → ℝ) (W : ι → (Matrix (Fin n) (Fin n) ℂ)) (k : ℝ)
    (ht : ∀ i ∈ S, 0 ≤ t i)
    (h : ∀ i ∈ S, weightedSq (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B) (W i) ≤ k * weightedSq A (W i) * RHLinalg.frobSq B) :
    weightedSq (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B) (∑ i ∈ S, t i • W i) ≤
      k * weightedSq A (∑ i ∈ S, t i • W i) * RHLinalg.frobSq B := by
  rw [weighted_sum, weighted_sum]
  calc
    ∑ i ∈ S, t i * weightedSq (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B) (W i) ≤
        ∑ i ∈ S, t i * (k * weightedSq A (W i) * RHLinalg.frobSq B) :=
      Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (h i hi) (ht i hi)
    _ = k * (∑ i ∈ S, t i * weightedSq A (W i)) * RHLinalg.frobSq B := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

private theorem unit_cube_mem_convexHull {n : ℕ} (t : Fin n → ℝ)
    (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) :
    t ∈ convexHull ℝ (Set.univ.pi fun _ : Fin n => ({0, 1} : Set ℝ)) := by
  rw [convexHull_pi]
  intro i hi
  rw [convexHull_pair, segment_eq_Icc (show (0 : ℝ) ≤ 1 by norm_num)]
  exact ht i

private theorem unitary_diagonal_mem_projection_hull {n : ℕ}
    (U : Matrix.unitaryGroup (Fin n) ℂ) (t : Fin n → ℝ)
    (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) :
    (conjStarAlgAut ℂ ((Matrix (Fin n) (Fin n) ℂ)) U) ((Matrix.diagonal (fun i => (t i : ℂ)))) ∈
      convexHull ℝ {P : (Matrix (Fin n) (Fin n) ℂ) | ((P).IsHermitian ∧ P * P = P)} := by
  let diagReal : (Fin n → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    (Matrix.diagonalLinearMap (n := Fin n) (R := ℝ) (α := ℂ)).comp
      (LinearMap.piMap fun _ : Fin n => Complex.ofRealLI.toLinearMap)
  let f : (Fin n → ℝ) →ₗ[ℝ] (Matrix (Fin n) (Fin n) ℂ) :=
    ((conjStarAlgAut ℂ ((Matrix (Fin n) (Fin n) ℂ)) U).toAlgEquiv.toLinearMap.restrictScalars ℝ).comp diagReal
  let vertices := Set.univ.pi fun _ : Fin n => ({0, 1} : Set ℝ)
  have hmem : f t ∈ convexHull ℝ (f '' vertices) := by
    rw [← f.image_convexHull]
    exact Set.mem_image_of_mem f (unit_cube_mem_convexHull _ ht)
  change f t ∈ convexHull ℝ {P : (Matrix (Fin n) (Fin n) ℂ) | ((P).IsHermitian ∧ P * P = P)}
  apply convexHull_mono (s := f '' vertices) (t := {P : (Matrix (Fin n) (Fin n) ℂ) | ((P).IsHermitian ∧ P * P = P)}) ?_ hmem
  rintro P ⟨v, hv, rfl⟩
  have hv01 : ∀ i, v i = 0 ∨ v i = 1 := by
    intro i
    have := hv i (Set.mem_univ i)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  have hd : ((Matrix.diagonal (fun i => (v i : ℂ)))).IsHermitian := by
    change (Matrix.diagonal fun i => (v i : ℂ)).IsHermitian
    rw [Matrix.isHermitian_diagonal_iff]
    intro i
    simp [IsSelfAdjoint]
  have hsq : (Matrix.diagonal (fun i => (v i : ℂ))) * (Matrix.diagonal (fun i => (v i : ℂ))) = (Matrix.diagonal (fun i => (v i : ℂ))) := by
    change (Matrix.diagonal fun i => (v i : ℂ)) *
      (Matrix.diagonal fun i => (v i : ℂ)) = Matrix.diagonal fun i => (v i : ℂ)
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rcases hv01 i with h | h <;> simp [h]
  constructor
  · change star ((conjStarAlgAut ℂ ((Matrix (Fin n) (Fin n) ℂ)) U) ((Matrix.diagonal (fun i => (v i : ℂ))))) =
      (conjStarAlgAut ℂ ((Matrix (Fin n) (Fin n) ℂ)) U) ((Matrix.diagonal (fun i => (v i : ℂ))))
    rw [← map_star]
    exact congrArg (conjStarAlgAut ℂ ((Matrix (Fin n) (Fin n) ℂ)) U) hd.eq
  · change (conjStarAlgAut ℂ ((Matrix (Fin n) (Fin n) ℂ)) U) ((Matrix.diagonal (fun i => (v i : ℂ)))) *
      (conjStarAlgAut ℂ ((Matrix (Fin n) (Fin n) ℂ)) U) ((Matrix.diagonal (fun i => (v i : ℂ)))) =
      (conjStarAlgAut ℂ ((Matrix (Fin n) (Fin n) ℂ)) U) ((Matrix.diagonal (fun i => (v i : ℂ))))
    rw [← map_mul, hsq]

def claim : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (W : (Matrix (Fin n) (Fin n) ℂ)) (lo hi : ℝ),
    W.PosDef → 0 < lo → SpectralExtrema W lo hi →
    ∀ A B : (Matrix (Fin n) (Fin n) ℂ),
      weightedSq (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B) W ≤ (1 + hi / lo) * weightedSq A W * RHLinalg.frobSq B

private theorem bounded_weight_decomposition {n : ℕ} (W : (Matrix (Fin n) (Fin n) ℂ)) (hW : W.IsHermitian)
    (lo hi : ℝ) (hlo : 0 < lo) (hhi : lo < hi)
    (hEig : ∀ i, lo ≤ hW.eigenvalues i ∧ hW.eigenvalues i ≤ hi) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (P : ι → (Matrix (Fin n) (Fin n) ℂ)),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ (∀ i, (((P i)).IsHermitian ∧ (P i) * (P i) = (P i))) ∧
      W = lo • (∑ i, w i • (1 + (hi / lo - 1) • P i)) := by
  classical
  let t : Fin n → ℝ := fun i => (hW.eigenvalues i - lo) / (hi - lo)
  have hs : 0 < hi - lo := by linarith
  have ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1 := by
    intro i
    constructor
    · exact div_nonneg (by linarith [(hEig i).1]) hs.le
    · apply (div_le_iff₀ hs).mpr
      linarith [(hEig i).2]
  let T := (conjStarAlgAut ℂ ((Matrix (Fin n) (Fin n) ℂ)) hW.eigenvectorUnitary) ((Matrix.diagonal (fun i => (t i : ℂ))))
  have hm : T ∈ convexHull ℝ {P : (Matrix (Fin n) (Fin n) ℂ) | ((P).IsHermitian ∧ P * P = P)} :=
    unitary_diagonal_mem_projection_hull _ _ ht
  obtain ⟨ι, inst, w, P, hw0, hw1, hP, hT⟩ := mem_convexHull_iff_exists_fintype.mp hm
  let _ := inst
  refine ⟨ι, inst, w, P, hw0, hw1, hP, ?_⟩
  have he : (Matrix.diagonal (fun i => (hW.eigenvalues i : ℂ))) = lo • (1 : (Matrix (Fin n) (Fin n) ℂ)) + (hi - lo) • (Matrix.diagonal (fun i => (t i : ℂ))) := by
    ext i j
    by_cases hij : i = j
    · subst j
      have hreal : hW.eigenvalues i = lo + (hi - lo) * t i := by
        dsimp [t]
        field_simp
        ring
      simpa [Matrix.diagonal] using congrArg (fun x : ℝ => (x : ℂ)) hreal
    · simp [hij]
  have hWT : W = lo • (1 : (Matrix (Fin n) (Fin n) ℂ)) + (hi - lo) • T := by
    rw [hW.spectral_theorem]
    change (conjStarAlgAut ℂ ((Matrix (Fin n) (Fin n) ℂ)) hW.eigenvectorUnitary)
      ((Matrix.diagonal (fun i => (hW.eigenvalues i : ℂ)))) = _
    rw [he, map_add]
    congr 1
    · calc
        _ = lo • ((conjStarAlgAut ℂ ((Matrix (Fin n) (Fin n) ℂ)) hW.eigenvectorUnitary) (1 : (Matrix (Fin n) (Fin n) ℂ))) :=
          (conjStarAlgAut ℂ ((Matrix (Fin n) (Fin n) ℂ)) hW.eigenvectorUnitary).toAlgEquiv.toLinearMap.map_smul_of_tower lo _
        _ = _ := by rw [map_one]
    · exact (conjStarAlgAut ℂ ((Matrix (Fin n) (Fin n) ℂ)) hW.eigenvectorUnitary).toAlgEquiv.toLinearMap.map_smul_of_tower (hi - lo) _
  have hsum : (∑ i, w i • (1 + (hi / lo - 1) • P i)) = 1 + (hi / lo - 1) • T := by
    simp only [smul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_smul, hw1, one_smul]
    rw [← hT]
    congr 1
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [smul_comm]
  rw [hsum, hWT, smul_add, smul_smul]
  congr 1
  field_simp

private theorem reduction_to_two_level (hTwo : (∀ (n : ℕ) (A B P : (Matrix (Fin n) (Fin n) ℂ)) (s : ℝ), ((P).IsHermitian ∧ P * P = P) → 0 ≤ s →
    weightedSq (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B) (1 + s • P) ≤
      (2 + s) * weightedSq A (1 + s • P) * RHLinalg.frobSq B)) : claim := by
  intro n hn W lo hi hpos hlo hspec A B
  classical
  obtain ⟨hW, hEig, hlo_mem, hhi_mem⟩ := hspec
  have hle : lo ≤ hi := by
    obtain ⟨i, hi⟩ := hlo_mem
    simpa [hi] using (hEig i).2
  by_cases heq : hi = lo
  · have hval : ∀ i, hW.eigenvalues i = lo := fun i => by
      have h := hEig i
      rw [heq] at h
      linarith
    have hW1 : W = lo • (1 : (Matrix (Fin n) (Fin n) ℂ)) := by
      rw [hW.spectral_theorem]
      have hd : Matrix.diagonal (RCLike.ofReal ∘ hW.eigenvalues) = lo • (1 : (Matrix (Fin n) (Fin n) ℂ)) := by
        ext i j
        by_cases hij : i = j <;> simp [hij, Function.comp_def, hval]
      rw [hd]
      calc
        _ = lo • ((conjStarAlgAut ℂ ((Matrix (Fin n) (Fin n) ℂ)) hW.eigenvectorUnitary) (1 : (Matrix (Fin n) (Fin n) ℂ))) :=
          (conjStarAlgAut ℂ ((Matrix (Fin n) (Fin n) ℂ)) hW.eigenvectorUnitary).toAlgEquiv.toLinearMap.map_smul_of_tower lo _
        _ = _ := by rw [map_one]
    have h := hTwo n A B 0 0 (by simp [Matrix.IsHermitian]) (by norm_num)
    simp only [zero_smul, add_zero, weighted_one, add_zero] at h
    rw [hW1, weighted_smul, weighted_smul, weighted_one, weighted_one, heq,
      div_self (ne_of_gt hlo)]
    nlinarith [mul_le_mul_of_nonneg_left h hlo.le]
  · obtain ⟨ι, inst, w, P, hw0, hw1, hP, hsum⟩ :=
      bounded_weight_decomposition W hW lo hi hlo (lt_of_le_of_ne hle (Ne.symm heq)) hEig
    let _ := inst
    have hs : 0 ≤ hi / lo - 1 := by
      have hdiv : 1 ≤ hi / lo := (le_div_iff₀ hlo).mpr (by simpa using hle)
      linarith
    have h := transfer_nonnegative_combination A B Finset.univ w
      (fun i => 1 + (hi / lo - 1) • P i) (2 + (hi / lo - 1))
      (fun i _ => hw0 i) (fun i _ => hTwo n A B (P i) (hi / lo - 1) (hP i) hs)
    rw [hsum, weighted_smul, weighted_smul]
    have hh := mul_le_mul_of_nonneg_left h hlo.le
    nlinarith [hh]

private theorem square_completion (d b s : ℝ) (hd : 0 ≤ d) (hb : 0 ≤ b) :
    d - 2 * s * Real.sqrt (b * d) + s ^ 2 * b =
      (Real.sqrt d - s * Real.sqrt b) ^ 2 := by
  rw [Real.sqrt_mul hb]
  have he := Real.sq_sqrt hd
  have hg := Real.sq_sqrt hb
  nlinarith

private theorem defect_lower_bound {n : ℕ} (A B P : (Matrix (Fin n) (Fin n) ℂ)) (s d : ℝ)
    (hP : ((P).IsHermitian ∧ P * P = P)) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (hgap : d * RHLinalg.frobSq B ≤ 2 * RHLinalg.frobSq A * RHLinalg.frobSq B - RHLinalg.frobSq (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B))
    (hcolumn : RHLinalg.frobSq (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B * P) ≤
      (RHLinalg.frobSq A + 2 * RHLinalg.frobSq (A * P) + 2 * Real.sqrt (RHLinalg.frobSq (A * P) * d)) * RHLinalg.frobSq B) :
    (Real.sqrt d - s * Real.sqrt (RHLinalg.frobSq (A * P))) ^ 2 * RHLinalg.frobSq B ≤
      (2 + s) * weightedSq A (1 + s • P) * RHLinalg.frobSq B -
        weightedSq (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B) (1 + s • P) := by
  rw [two_level_defect A B P s hP, ← square_completion d (RHLinalg.frobSq (A * P)) s hd (frobSq_nonneg _)]
  have hh := mul_le_mul_of_nonneg_left hcolumn hs
  nlinarith

private theorem gap_bound {n : ℕ} (A B : (Matrix (Fin n) (Fin n) ℂ)) :
    gap A * RHLinalg.frobSq B ≤ 2 * RHLinalg.frobSq A * RHLinalg.frobSq B - RHLinalg.frobSq (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B) := by
  have hn := (commOperator A).le_opNorm (vectorize n B)
  have hsq := mul_le_mul hn hn (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hl : commOperator A (vectorize n B) = vectorize n (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B) := rfl
  have hh : ‖vectorize n (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B)‖ ^ 2 ≤
      ‖commOperator A‖ ^ 2 * ‖vectorize n B‖ ^ 2 := by rw [hl] at hsq; nlinarith
  rw [vectorize_norm_sq, vectorize_norm_sq] at hh
  unfold gap
  nlinarith

private theorem two_level_from_projection_gap
    (hgap : ∀ n (A : (Matrix (Fin n) (Fin n) ℂ)), 0 ≤ gap A) (hproj : (∀ n (A B P : (Matrix (Fin n) (Fin n) ℂ)), ((P).IsHermitian ∧ P * P = P) →
    RHLinalg.frobSq (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B * P) ≤
      (RHLinalg.frobSq A + 2 * RHLinalg.frobSq (A * P) +
        2 * Real.sqrt (RHLinalg.frobSq (A * P) * gap A)) * RHLinalg.frobSq B)) : (∀ (n : ℕ) (A B P : (Matrix (Fin n) (Fin n) ℂ)) (s : ℝ), ((P).IsHermitian ∧ P * P = P) → 0 ≤ s →
    weightedSq (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B) (1 + s • P) ≤
      (2 + s) * weightedSq A (1 + s • P) * RHLinalg.frobSq B) := by
  intro n A B P s hP hs
  have h := defect_lower_bound A B P s (gap A) hP hs (hgap n A)
    (gap_bound A B) (hproj n A B P hP)
  have hsq := mul_nonneg (sq_nonneg (Real.sqrt (gap A) - s * Real.sqrt (RHLinalg.frobSq (A * P))))
    (frobSq_nonneg B)
  linarith

private theorem result_conditional
    (hgap : ∀ n (A : (Matrix (Fin n) (Fin n) ℂ)), 0 ≤ gap A) (hproj : (∀ n (A B P : (Matrix (Fin n) (Fin n) ℂ)), ((P).IsHermitian ∧ P * P = P) →
    RHLinalg.frobSq (D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator A B * P) ≤
      (RHLinalg.frobSq A + 2 * RHLinalg.frobSq (A * P) +
        2 * Real.sqrt (RHLinalg.frobSq (A * P) * gap A)) * RHLinalg.frobSq B)) : claim :=
  reduction_to_two_level (two_level_from_projection_gap hgap hproj)

theorem result : claim :=
  result_conditional gap_nonnegative projection_gap

#print axioms result

end D5.S3.Quantum.Matrix.WeightedBotcherWenzel
