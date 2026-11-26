/- GID: D5/S3/Quantum/Analysis/RefinedBMV/NearScalar/WordControl
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Proof component of the four-copy refined BMV comparison near a scalar. -/

import D5.S3.Quantum.Analysis.RefinedBMV.NearScalar.Commutator

/-! Frobenius estimates for the three- and four-commutator errors in the
four-copy near-scalar BMV word reordering argument. -/

open Matrix
open scoped Matrix Matrix.Norms.Frobenius

namespace D5.S3.Quantum.Analysis.RefinedBMVNearScalarWordControl

open D5.S3.Quantum.Analysis.RefinedBMVNearScalarCommutator

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "opNorm" =>
  fun A : Matrix n n ℂ => ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) A‖

private theorem opNorm_adjoint (T : Matrix n n ℂ) :
    opNorm Tᴴ = opNorm T := by
  exact Matrix.l2_opNorm_conjTranspose T

private theorem opNorm_pow_le (H : Matrix n n ℂ) (k : ℕ) :
    opNorm (H ^ k) ≤ opNorm H ^ k := by
  dsimp only
  rw [map_pow]
  induction k with
  | zero =>
      rw [pow_zero, pow_zero]
      exact ContinuousLinearMap.norm_id_le
  | succ k ih =>
      rw [pow_succ, pow_succ]
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right ih (norm_nonneg _))

private theorem frobenius_mul_right_le_op (X T : Matrix n n ℂ) :
    ‖X * T‖ ≤ ‖X‖ * opNorm T := by
  calc
    ‖X * T‖ = ‖(X * T)ᴴ‖ := (Matrix.frobenius_norm_conjTranspose _).symm
    _ = ‖Tᴴ * Xᴴ‖ := by rw [Matrix.conjTranspose_mul]
    _ ≤ opNorm Tᴴ * ‖Xᴴ‖ := frobenius_mul_le_op _ _
    _ = _ := by rw [opNorm_adjoint, Matrix.frobenius_norm_conjTranspose, mul_comm]

private theorem frobenius_mul_pow_le (X H : Matrix n n ℂ) (k : ℕ) :
    ‖X * H ^ k‖ ≤ ‖X‖ * opNorm H ^ k :=
  (frobenius_mul_right_le_op X (H ^ k)).trans
    (mul_le_mul_of_nonneg_left (opNorm_pow_le H k) (norm_nonneg _))

/-- For skew-Hermitian C, a sandwich by C is controlled by the Frobenius
norm of C squared and the Euclidean operator norm of its middle factor. -/
theorem frobenius_skew_sandwich_le (C T : Matrix n n ℂ)
    (hC : Cᴴ = -C) :
    ‖C * T * C‖ ≤ opNorm T * ‖C ^ 2‖ := by
  classical
  let P := -(C ^ 2)
  have hleft : Cᴴ * C = P := by simp only [P, hC, neg_mul, pow_two]
  have hright : C * Cᴴ = P := by simp only [P, hC, mul_neg, pow_two]
  have hP : ‖P‖ = ‖C ^ 2‖ := norm_neg _
  have htrace : (((C * T * C)ᴴ * (C * T * C)).trace) =
      (P * (T * P * Tᴴ)).trace := by
    calc
      _ = ((C * T * C) * (C * T * C)ᴴ).trace := Matrix.trace_mul_comm _ _
      _ = ((C * (T * (C * Cᴴ) * Tᴴ)) * Cᴴ).trace := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
        congr 1
        noncomm_ring
      _ = (Cᴴ * (C * (T * (C * Cᴴ) * Tᴴ))).trace :=
        Matrix.trace_mul_comm _ _
      _ = (P * (T * P * Tᴴ)).trace := by
        rw [← Matrix.mul_assoc Cᴴ C, hleft, hright]
  have hsq : ‖C * T * C‖ ^ 2 = ‖(P * (T * P * Tᴴ)).trace‖ := by
    rw [← htrace, ← D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hmiddle : ‖T * P * Tᴴ‖ ≤ opNorm T * ‖P‖ * opNorm T := by
    calc
      _ ≤ ‖T * P‖ * opNorm Tᴴ := frobenius_mul_right_le_op _ _
      _ ≤ (opNorm T * ‖P‖) * opNorm Tᴴ :=
        mul_le_mul_of_nonneg_right (frobenius_mul_le_op T P) (norm_nonneg _)
      _ = _ := by rw [opNorm_adjoint]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  calc
    ‖C * T * C‖ ^ 2 = ‖(P * (T * P * Tᴴ)).trace‖ := hsq
    _ ≤ ‖P‖ * ‖T * P * Tᴴ‖ := trace_product_bound _ _
    _ ≤ ‖P‖ * (opNorm T * ‖P‖ * opNorm T) :=
      mul_le_mul_of_nonneg_left hmiddle (norm_nonneg _)
    _ = (opNorm T * ‖C ^ 2‖) ^ 2 := by rw [hP]; ring

private theorem frobenius_skew_pair_pow_le (C H : Matrix n n ℂ)
    (hC : Cᴴ = -C) (a b : ℕ) :
    ‖C * H ^ a * C * H ^ b‖ ≤ opNorm H ^ (a + b) * ‖C ^ 2‖ := by
  have ha : ‖C * H ^ a * C‖ ≤ opNorm H ^ a * ‖C ^ 2‖ :=
    (frobenius_skew_sandwich_le C (H ^ a) hC).trans
      (mul_le_mul_of_nonneg_right (opNorm_pow_le H a) (norm_nonneg _))
  calc
    _ ≤ ‖C * H ^ a * C‖ * opNorm H ^ b := frobenius_mul_pow_le _ _ _
    _ ≤ (opNorm H ^ a * ‖C ^ 2‖) * opNorm H ^ b :=
      mul_le_mul_of_nonneg_right ha (pow_nonneg (norm_nonneg _) _)
    _ = _ := by rw [pow_add]; ring

/-- Four commutators with arbitrary gaps of powers of the same matrix. -/
theorem four_commutator_word_bound (C H : Matrix n n ℂ)
    (hC : Cᴴ = -C) (a b c d : ℕ) :
    |(C * H ^ a * C * H ^ b * C * H ^ c * C * H ^ d).trace.re| ≤
      opNorm H ^ (a + b + c + d) * ‖C ^ 2‖ ^ 2 := by
  let X := C * H ^ a * C * H ^ b
  let Y := C * H ^ c * C * H ^ d
  have hword : C * H ^ a * C * H ^ b * C * H ^ c * C * H ^ d = X * Y := by
    dsimp only [X, Y]
    noncomm_ring
  rw [hword]
  calc
    _ ≤ ‖(X * Y).trace‖ := Complex.abs_re_le_norm _
    _ ≤ ‖X‖ * ‖Y‖ := trace_product_bound _ _
    _ ≤ (opNorm H ^ (a + b) * ‖C ^ 2‖) *
        (opNorm H ^ (c + d) * ‖C ^ 2‖) :=
      mul_le_mul (frobenius_skew_pair_pow_le C H hC a b)
        (frobenius_skew_pair_pow_le C H hC c d) (norm_nonneg _) (by positivity)
    _ = _ := by simp only [pow_add]; ring

/-- Three commutators with a weighted commutator at the first position. -/
theorem three_commutator_word_bound (C H B : Matrix n n ℂ)
    (hC : Cᴴ = -C) (a b c : ℕ) :
    |(B * C * H ^ a * C * H ^ b * C * H ^ c).trace.re| ≤
      opNorm H ^ (a + b + c) * ‖B * C‖ * ‖C ^ 2‖ := by
  let X := B * C * H ^ a
  let Y := C * H ^ b * C * H ^ c
  have hword : B * C * H ^ a * C * H ^ b * C * H ^ c = X * Y := by
    dsimp only [X, Y]
    noncomm_ring
  rw [hword]
  calc
    _ ≤ ‖(X * Y).trace‖ := Complex.abs_re_le_norm _
    _ ≤ ‖X‖ * ‖Y‖ := trace_product_bound _ _
    _ ≤ (‖B * C‖ * opNorm H ^ a) * (opNorm H ^ (b + c) * ‖C ^ 2‖) :=
      mul_le_mul (frobenius_mul_pow_le (B * C) H a)
        (frobenius_skew_pair_pow_le C H hC b c) (norm_nonneg _) (by positivity)
    _ = _ := by simp only [pow_add]; ring

/-- The other orientation of the adjacent B is controlled by the same
weighted commutator norm when B is Hermitian. -/
theorem three_commutator_word_bound_right (C H B : Matrix n n ℂ)
    (hC : Cᴴ = -C) (hB : B.IsHermitian) (a b c : ℕ) :
    |(C * B * H ^ a * C * H ^ b * C * H ^ c).trace.re| ≤
      opNorm H ^ (a + b + c) * ‖B * C‖ * ‖C ^ 2‖ := by
  have hBC : ‖C * B‖ = ‖B * C‖ := by
    calc
      _ = ‖(C * B)ᴴ‖ := (Matrix.frobenius_norm_conjTranspose _).symm
      _ = _ := by rw [Matrix.conjTranspose_mul, hC, hB.eq, mul_neg, norm_neg]
  let X := C * B * H ^ a
  let Y := C * H ^ b * C * H ^ c
  have hword : C * B * H ^ a * C * H ^ b * C * H ^ c = X * Y := by
    dsimp only [X, Y]
    noncomm_ring
  rw [hword]
  calc
    _ ≤ ‖(X * Y).trace‖ := Complex.abs_re_le_norm _
    _ ≤ ‖X‖ * ‖Y‖ := trace_product_bound _ _
    _ ≤ (‖C * B‖ * opNorm H ^ a) * (opNorm H ^ (b + c) * ‖C ^ 2‖) :=
      mul_le_mul (frobenius_mul_pow_le (C * B) H a)
        (frobenius_skew_pair_pow_le C H hC b c) (norm_nonneg _) (by positivity)
    _ = _ := by rw [hBC]; simp only [pow_add]; ring

end D5.S3.Quantum.Analysis.RefinedBMVNearScalarWordControl
