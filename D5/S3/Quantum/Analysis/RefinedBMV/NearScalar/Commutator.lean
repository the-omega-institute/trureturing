/- GID: D5/S3/Quantum/Analysis/RefinedBMV/NearScalar/Commutator
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Proof component of the four-copy refined BMV comparison near a scalar. -/

import D5.S3.Quantum.GNSMatrix
import D5.S3.Quantum.Matrix.CartesianVariance

/-! Dimension-free commutator control for refined BMV. -/

open Matrix
open scoped Matrix Matrix.Norms.Frobenius

namespace D5.S3.Quantum.Analysis.RefinedBMVNearScalarCommutator

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem norm_sq_columns (A : Matrix n n ℂ) :
    ‖A‖ ^ 2 = ∑ j, ‖WithLp.toLp 2 (fun i => A i j)‖ ^ 2 := by
  change ‖WithLp.toLp 2 (fun i => WithLp.toLp 2 (A i))‖ ^ 2 = _
  simp only [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_comm

/-- The left ideal inequality, obtained by applying the Euclidean operator
norm estimate separately to every column. -/
theorem frobenius_mul_le_op (A X : Matrix n n ℂ) :
    ‖A * X‖ ≤ ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) A‖ * ‖X‖ := by
  classical
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, norm_sq_columns (A * X), norm_sq_columns X, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  let x : EuclideanSpace ℂ n := WithLp.toLp 2 (fun i => X i j)
  have hx : (EuclideanSpace.equiv n ℂ).symm (A *ᵥ x) =
      WithLp.toLp 2 (fun i => (A * X) i j) := by
    apply (EuclideanSpace.equiv n ℂ).injective
    funext i
    rfl
  have h : ‖WithLp.toLp 2 (fun i => (A * X) i j)‖ ≤
      ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) A‖ * ‖x‖ := by
    rw [← hx]
    exact Matrix.l2_opNorm_mulVec A x
  simpa only [mul_pow, x] using
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h

/-- Hilbert–Schmidt Cauchy–Schwarz, using the existing finite matrix pairing
and transporting the index type to `Fin`. -/
theorem trace_product_bound (Q X : Matrix n n ℂ) :
    ‖(Q * X).trace‖ ≤ ‖Q‖ * ‖X‖ := by
  let e := Fintype.equivFin n
  let R := Matrix.reindexRingEquiv ℂ e
  have hm (A C : Matrix n n ℂ) : R (A * C) = R A * R C := R.map_mul A C
  have ht (A : Matrix n n ℂ) : (R A).trace = A.trace :=
    e.symm.sum_comp (fun i => A i i)
  have hs (A : Matrix n n ℂ) : (R A)ᴴ = R Aᴴ := Matrix.conjTranspose_reindex e e A
  have hc := D5.S3.Quantum.Matrix.CartesianVariance.trace_product_cauchy (R Q) (R X)
  have hb : Complex.normSq (Q * X).trace ≤ (Qᴴ * Q).trace.re * (Xᴴ * X).trace.re := by
    simpa only [RHLinalg.frobSq, hs, ← hm, ht, RCLike.re_eq_complex_re] using hc
  rw [← D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace Q,
    ← D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace X,
    Complex.ofReal_re, Complex.ofReal_re, Complex.normSq_eq_norm_sq, ← mul_pow] at hb
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp hb

/-- Dimension-free commutator estimate for two Hermitian matrices.
The matrix norm is Frobenius, and the norm of `toEuclideanCLM H` is the
Euclidean operator norm of `H`. -/
theorem commutator_square_frobenius_le (H B : Matrix n n ℂ)
    (hH : H.IsHermitian) (hB : B.IsHermitian) :
    ‖(H * B - B * H) ^ 2‖ ≤
      2 * ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) H‖ * ‖B * (H * B - B * H)‖ := by
  classical
  let C := H * B - B * H
  change ‖C ^ 2‖ ≤ 2 * ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) H‖ * ‖B * C‖
  have hC : Cᴴ = -C := by
    change (H * B - B * H)ᴴ = -(H * B - B * H)
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hH.eq, hB.eq, neg_sub]
  have hC2 : (C ^ 2)ᴴ = C ^ 2 := by
    simp only [pow_two, Matrix.conjTranspose_mul, hC, neg_mul_neg]
  have hBC : ‖C * B‖ = ‖B * C‖ := by
    calc
      ‖C * B‖ = ‖(C * B)ᴴ‖ := (Matrix.frobenius_norm_conjTranspose _).symm
      _ = ‖B * C‖ := by rw [Matrix.conjTranspose_mul, hC, hB.eq, mul_neg, norm_neg]
  have htrace : (C ^ 4).trace = (H * (B * C ^ 3 - C ^ 3 * B)).trace := by
    calc
      (C ^ 4).trace = (C * C ^ 3).trace := by
        congr 1
        noncomm_ring
      _ = ((H * B) * C ^ 3).trace - ((B * H) * C ^ 3).trace := by
        change ((H * B - B * H) * C ^ 3).trace = _
        rw [sub_mul, Matrix.trace_sub]
      _ = (H * (B * C ^ 3 - C ^ 3 * B)).trace := by
        rw [Matrix.mul_sub, Matrix.trace_sub,
          ← Matrix.trace_mul_cycle H (C ^ 3) B]
        simp only [Matrix.mul_assoc]
  have htraceSq : ((‖C ^ 2‖ ^ 2 : ℝ) : ℂ) = (C ^ 4).trace := by
    rw [D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace, hC2]
    congr 1
    noncomm_ring
  have hfirst : ‖(H * (B * C ^ 3)).trace‖ ≤
      ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) H‖ * ‖B * C‖ * ‖C ^ 2‖ := by
    have heq : H * (B * C ^ 3) = (H * (B * C)) * C ^ 2 := by
      noncomm_ring
    rw [heq]
    exact (trace_product_bound _ _).trans
      (mul_le_mul_of_nonneg_right (frobenius_mul_le_op H (B * C)) (norm_nonneg _))
  have hsecond : ‖(H * (C ^ 3 * B)).trace‖ ≤
      ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) H‖ * ‖B * C‖ * ‖C ^ 2‖ := by
    have heq : H * (C ^ 3 * B) = (H * C ^ 2) * (C * B) := by
      noncomm_ring
    rw [heq]
    calc
      _ ≤ ‖H * C ^ 2‖ * ‖C * B‖ := trace_product_bound _ _
      _ ≤ (‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) H‖ * ‖C ^ 2‖) * ‖C * B‖ :=
        mul_le_mul_of_nonneg_right (frobenius_mul_le_op H (C ^ 2)) (norm_nonneg _)
      _ = _ := by rw [hBC]; ring
  have hsq :
      ‖C ^ 2‖ ^ 2 ≤
        2 * ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) H‖ * ‖B * C‖ * ‖C ^ 2‖ := by
    calc
      ‖C ^ 2‖ ^ 2 = ‖(C ^ 4).trace‖ := by
        rw [← htraceSq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      _ = ‖(H * (B * C ^ 3)).trace - (H * (C ^ 3 * B)).trace‖ := by
        rw [htrace, Matrix.mul_sub, Matrix.trace_sub]
      _ ≤ ‖(H * (B * C ^ 3)).trace‖ + ‖(H * (C ^ 3 * B)).trace‖ := norm_sub_le _ _
      _ ≤ _ := by linarith [add_le_add hfirst hsecond]
  by_cases hz : ‖C ^ 2‖ = 0
  · rw [hz]
    positivity
  · have hp : 0 < ‖C ^ 2‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    apply (mul_le_mul_iff_left₀ hp).mp
    simpa only [pow_two] using hsq

set_option maxHeartbeats 1000000 in
open scoped ComplexOrder MatrixOrder in
/-- The four-copy Hessian trace controls the Frobenius norm of the weighted commutator. -/
theorem four_copy_hessian_ge (H B : Matrix n n ℂ)
    (hH : H.IsHermitian) (hB : B.PosSemidef) :
    3 * ‖B * (H * B - B * H)‖ ^ 2 ≤
      (((3 : ℂ) • (H ^ 2 * B ^ 4) - (2 : ℂ) • (H * B * H * B ^ 3) -
        H * B ^ 2 * H * B ^ 2).trace).re := by
  let C := H * B - B * H
  let U : ℂ := (H ^ 2 * B ^ 4).trace
  let V : ℂ := (H * B * H * B ^ 3).trace
  let W : ℂ := (H * B ^ 2 * H * B ^ 2).trace
  have hC : Cᴴ = B * H - H * B := by
    simp only [C, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hH.eq,
      hB.isHermitian.eq]
  have hU : (H * B ^ 4 * H).trace = U := by
    calc
      _ = (H * H * B ^ 4).trace := Matrix.trace_mul_cycle H (B ^ 4) H
      _ = U := by rw [← pow_two H]
  have hV₁ : (B * H * B ^ 3 * H).trace = V := by
    calc
      _ = (H * (B * H * B ^ 3)).trace := Matrix.trace_mul_comm (B * H * B ^ 3) H
      _ = V := by
        change (H * (B * H * B ^ 3)).trace = (H * B * H * B ^ 3).trace
        rw [← Matrix.mul_assoc H (B * H) (B ^ 3), ← Matrix.mul_assoc H B H]
  have hV₂ : (H * B ^ 3 * H * B).trace = V := by
    calc
      _ = ((H * B ^ 3) * (H * B)).trace := by rw [Matrix.mul_assoc (H * B ^ 3) H B]
      _ = ((H * B) * (H * B ^ 3)).trace := Matrix.trace_mul_comm (H * B ^ 3) (H * B)
      _ = V := by
        change ((H * B) * (H * B ^ 3)).trace = (H * B * H * B ^ 3).trace
        rw [← Matrix.mul_assoc (H * B) H (B ^ 3)]
  have hV₃ : (B * (H * B * H * B ^ 2)).trace = V := by
    calc
      _ = (H * B * H * B ^ 2 * B).trace := Matrix.trace_mul_comm B (H * B * H * B ^ 2)
      _ = V := by
        dsimp only [V]
        rw [Matrix.mul_assoc (H * B * H) (B ^ 2) B, ← pow_succ B 2]
  have hW : (B * (H * B ^ 2 * H) * B).trace = W := by
    calc
      _ = (B * B * (H * B ^ 2 * H)).trace := Matrix.trace_mul_cycle B (H * B ^ 2 * H) B
      _ = ((H * B ^ 2 * H) * (B * B)).trace :=
        Matrix.trace_mul_comm (B * B) (H * B ^ 2 * H)
      _ = W := by rw [← pow_two B]
  have hBC : ((B * C)ᴴ * (B * C)).trace = U + W - 2 * V := by
    have hexpand : (B * C)ᴴ * (B * C) =
        B * (H * B ^ 2 * H) * B - B * H * B ^ 3 * H -
          H * B ^ 3 * H * B + H * B ^ 4 * H := by
      rw [Matrix.conjTranspose_mul, hB.isHermitian.eq, hC]
      dsimp only [C]
      noncomm_ring
    rw [hexpand, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, hW, hV₁, hV₂, hU]
    ring
  have hCBC : (Cᴴ * B * C * B).trace = 2 * (V - W) := by
    have hexpand : Cᴴ * B * C * B =
        B * (H * B * H * B ^ 2) - B * (H * B ^ 2 * H) * B -
          H * B ^ 2 * H * B ^ 2 + H * B ^ 3 * H * B := by
      rw [hC]
      dsimp only [C]
      noncomm_ring
    rw [hexpand, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, hV₃, hW, hV₂]
    change V - W - W + V = 2 * (V - W)
    ring
  let S := CFC.sqrt B
  have hSS : S * S = B := CFC.sqrt_mul_sqrt_self B hB.nonneg
  have hS : Sᴴ = S := (CFC.sqrt_nonneg B).posSemidef.isHermitian.eq
  have hfactor : (Cᴴ * B * C * B).trace = ((S * C * S)ᴴ * (S * C * S)).trace := by
    calc
      _ = (Cᴴ * B * C * S * S).trace := by
        rw [Matrix.mul_assoc (Cᴴ * B * C) S S, hSS]
      _ = (S * (Cᴴ * B * C) * S).trace :=
        Matrix.trace_mul_cycle (Cᴴ * B * C) S S
      _ = (S * (Cᴴ * (S * S) * C) * S).trace := by rw [hSS]
      _ = _ := by simp only [Matrix.conjTranspose_mul, hS, Matrix.mul_assoc]
  have hpos : 0 ≤ (Cᴴ * B * C * B).trace.re := by
    rw [hfactor, ← D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace, Complex.ofReal_re]
    exact sq_nonneg _
  have hessian_eq :
      ((3 : ℂ) • (H ^ 2 * B ^ 4) - (2 : ℂ) • (H * B * H * B ^ 3) -
        H * B ^ 2 * H * B ^ 2).trace =
        3 * ((‖B * C‖ ^ 2 : ℝ) : ℂ) + 2 * (Cᴴ * B * C * B).trace := by
    calc
      _ = 3 * U - 2 * V - W := by
        simp only [Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, U, V, W]
      _ = _ := by
        rw [D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace, hBC, hCBC]
        ring
  change 3 * ‖B * C‖ ^ 2 ≤ _
  rw [hessian_eq]
  have hre (x : ℝ) : (((x : ℂ) ^ 2).re) = x ^ 2 := by
    simp only [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
  norm_num [Complex.add_re, Complex.mul_re, Complex.ofReal_re]
  rw [hre]
  linarith only [hpos]

end D5.S3.Quantum.Analysis.RefinedBMVNearScalarCommutator
