/- GID: D5/S3/Quantum/Analysis/RefinedBMV/NearScalar/PowerReorder
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Proof component of the four-copy refined BMV comparison near a scalar. -/

import D5.S3.Quantum.Analysis.RefinedBMV.NearScalar.WordControl
import D5.S3.Quantum.Analysis.RefinedBMV.NearScalar.Commutator

/-! Bounds for cyclic traces after moving a matrix across a power. -/

open Matrix
open scoped Matrix Matrix.Norms.Frobenius BigOperators

namespace D5.S3.Quantum.Analysis.RefinedBMVNearScalarPowerReorder

open D5.S3.Quantum.Analysis.RefinedBMVNearScalarCommutator
open D5.S3.Quantum.Analysis.RefinedBMVNearScalarWordControl

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "opNorm" =>
  fun A : Matrix n n ℂ => ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) A‖

theorem power_commutator (H B : Matrix n n ℂ) (k : ℕ) :
    H ^ k * B - B * H ^ k =
      ∑ j ∈ Finset.range k, H ^ j * (H * B - B * H) * H ^ (k - 1 - j) := by
  classical
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      H ^ (k + 1) * B - B * H ^ (k + 1) =
          (H ^ k * B - B * H ^ k) * H + H ^ k * (H * B - B * H) := by
        simp only [pow_succ H k]
        noncomm_ring
      _ = (∑ j ∈ Finset.range k, H ^ j * (H * B - B * H) *
          H ^ (k - 1 - j) * H) + H ^ k * (H * B - B * H) := by
        rw [ih, Matrix.sum_mul]
      _ = _ := by
        rw [Finset.sum_range_succ]
        simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        have hj' := Finset.mem_range.mp hj
        have he : k - 1 - j + 1 = k - j := by omega
        rw [Matrix.mul_assoc, ← pow_succ, he]

private theorem split_power_add (k j t : ℕ) (hj : j < k) :
    j + (k - 1 - j) + t + 1 = k + t := by omega

omit [DecidableEq n] in
private theorem skew_commutator (H B : Matrix n n ℂ)
    (hH : H.IsHermitian) (hB : B.IsHermitian) :
    (H * B - B * H)ᴴ = -(H * B - B * H) := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, hH.eq, hB.eq, neg_sub]

private theorem trace_move_bound (H B P Q : Matrix n n ℂ) (k : ℕ)
    (A E : ℝ)
    (hA : |(P * (B * H ^ k) * Q).trace.re| ≤ A)
    (hE : ∀ j < k, |(P * (H ^ j * (H * B - B * H) *
      H ^ (k - 1 - j)) * Q).trace.re| ≤ E) :
    |(P * (H ^ k * B) * Q).trace.re| ≤ A + (k : ℝ) * E := by
  classical
  have hm := power_commutator H B k
  have he : H ^ k * B = B * H ^ k +
      ∑ j ∈ Finset.range k, H ^ j * (H * B - B * H) * H ^ (k - 1 - j) := by
    rw [← hm]
    abel
  rw [he, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.trace_add, Matrix.trace_sum, Complex.add_re, Complex.re_sum]
  calc
    _ ≤ |(P * (B * H ^ k) * Q).trace.re| +
        |∑ j ∈ Finset.range k, (P * (H ^ j * (H * B - B * H) *
          H ^ (k - 1 - j)) * Q).trace.re| := abs_add_le _ _
    _ ≤ A + ∑ j ∈ Finset.range k, E :=
      add_le_add hA ((Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun j hj => hE j (Finset.mem_range.mp hj)))
    _ = _ := by simp

theorem three_commutator_power_word_bound (H B : Matrix n n ℂ)
    (hH : H.IsHermitian) (hB : B.IsHermitian) (a b c d : ℕ) :
    let C := H * B - B * H
    |(C * H ^ a * B * H ^ b * C * H ^ c * C * H ^ d).trace.re| ≤
      (2 + 4 * (a : ℝ)) * opNorm H ^ (a + b + c + d + 1) * ‖B * C‖ ^ 2 := by
  classical
  dsimp only
  let C := H * B - B * H
  let M := opNorm H
  let K := ‖B * C‖
  let T := M ^ (a + b + c + d + 1) * K ^ 2
  have hC : Cᴴ = -C := skew_commutator H B hH hB
  have hsq : ‖C ^ 2‖ ≤ 2 * M * K := commutator_square_frobenius_le H B hH hB
  let Q := H ^ b * C * H ^ c * C * H ^ d
  have hword : C * H ^ a * B * H ^ b * C * H ^ c * C * H ^ d =
      C * (H ^ a * B) * Q := by
    dsimp only [Q]
    noncomm_ring
  change |(C * H ^ a * B * H ^ b * C * H ^ c * C * H ^ d).trace.re| ≤
    (2 + 4 * (a : ℝ)) * M ^ (a + b + c + d + 1) * K ^ 2
  rw [hword]
  have hadj : |(C * (B * H ^ a) * Q).trace.re| ≤ 2 * T := by
    have he : C * (B * H ^ a) * Q =
        C * B * H ^ (a + b) * C * H ^ c * C * H ^ d := by
      dsimp only [Q]
      rw [pow_add H a b]
      noncomm_ring
    rw [he]
    calc
      _ ≤ M ^ (a + b + c + d) * K * ‖C ^ 2‖ :=
        three_commutator_word_bound_right C H B hC hB (a + b) c d
      _ ≤ M ^ (a + b + c + d) * K * (2 * M * K) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = 2 * T := by dsimp only [T]; rw [pow_succ]; ring
  have herr (j : ℕ) (hj : j < a) :
      |(C * (H ^ j * (H * B - B * H) * H ^ (a - 1 - j)) * Q).trace.re| ≤
        4 * T := by
    let r := a - 1 - j
    have he : C * (H ^ j * C * H ^ r) * Q =
        C * H ^ j * C * H ^ (r + b) * C * H ^ c * C * H ^ d := by
      dsimp only [Q]
      rw [pow_add H r b]
      noncomm_ring
    change |(C * (H ^ j * C * H ^ r) * Q).trace.re| ≤ _
    rw [he]
    have hs : j + (r + b) + c + d + 1 = a + b + c + d := by
      have h := split_power_add a j (b + c + d) hj
      dsimp only [r]
      omega
    have hsq' : ‖C ^ 2‖ ^ 2 ≤ (2 * M * K) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hsq
    calc
      _ ≤ M ^ (j + (r + b) + c + d) * ‖C ^ 2‖ ^ 2 :=
        four_commutator_word_bound C H hC j (r + b) c d
      _ ≤ M ^ (j + (r + b) + c + d) * (2 * M * K) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq' (by positivity)
      _ = 4 * T := by
        dsimp only [T]
        rw [pow_succ M (a + b + c + d), ← hs, pow_succ M (j + (r + b) + c + d)]
        ring
  calc
    _ ≤ 2 * T + (a : ℝ) * (4 * T) :=
      trace_move_bound H B C Q a (2 * T) (4 * T) hadj herr
    _ = _ := by dsimp only [T]; ring

private theorem weighted_pair_pow_le (C H B : Matrix n n ℂ)
    (hC : Cᴴ = -C) (hB : B.IsHermitian) (k : ℕ) :
    ‖C * B * H ^ k‖ ≤ ‖B * C‖ * opNorm H ^ k := by
  have hBC : ‖C * B‖ = ‖B * C‖ := by
    calc
      _ = ‖(C * B)ᴴ‖ := (Matrix.frobenius_norm_conjTranspose _).symm
      _ = _ := by rw [Matrix.conjTranspose_mul, hC, hB.eq, mul_neg, norm_neg]
  have hp : opNorm (H ^ k) ≤ opNorm H ^ k := by
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
  calc
    _ = ‖(H ^ k)ᴴ * (C * B)ᴴ‖ := by
      rw [← Matrix.conjTranspose_mul, Matrix.frobenius_norm_conjTranspose]
    _ ≤ opNorm ((H ^ k)ᴴ) * ‖(C * B)ᴴ‖ := frobenius_mul_le_op _ _
    _ = opNorm (H ^ k) * ‖B * C‖ := by
      have hAdj : opNorm ((H ^ k)ᴴ) = opNorm (H ^ k) :=
        Matrix.l2_opNorm_conjTranspose (H ^ k)
      rw [hAdj, Matrix.frobenius_norm_conjTranspose, hBC]
    _ ≤ _ := by
      rw [mul_comm ‖B * C‖]
      exact mul_le_mul_of_nonneg_right hp (norm_nonneg _)

theorem alternating_two_commutator_power_word_bound (H B : Matrix n n ℂ)
    (hH : H.IsHermitian) (hB : B.IsHermitian) (a b c d : ℕ) :
    let C := H * B - B * H
    |(C * H ^ a * B * H ^ b * C * H ^ c * B * H ^ d).trace.re| ≤
      (1 + 2 * (c : ℝ) + (a : ℝ) * (2 + 4 * (c : ℝ))) *
        opNorm H ^ (a + b + c + d) * ‖B * C‖ ^ 2 := by
  classical
  dsimp only
  let C := H * B - B * H
  let M := opNorm H
  let K := ‖B * C‖
  let T := M ^ (a + b + c + d) * K ^ 2
  have hC : Cᴴ = -C := skew_commutator H B hH hB
  have hsq : ‖C ^ 2‖ ≤ 2 * M * K := commutator_square_frobenius_le H B hH hB
  let P := C * B * H ^ (a + b) * C
  let Q := H ^ b * C * H ^ c * B * H ^ d
  change |(C * H ^ a * B * H ^ b * C * H ^ c * B * H ^ d).trace.re| ≤ _
  have hw : C * H ^ a * B * H ^ b * C * H ^ c * B * H ^ d =
      C * (H ^ a * B) * Q := by dsimp only [Q]; noncomm_ring
  rw [hw]
  have hadj : |(C * (B * H ^ a) * Q).trace.re| ≤ (1 + 2 * (c : ℝ)) * T := by
    have he : C * (B * H ^ a) * Q = P * (H ^ c * B) * H ^ d := by
      dsimp only [P, Q]
      rw [pow_add H a b]
      noncomm_ring
    rw [he]
    have hbase : |(P * (B * H ^ c) * H ^ d).trace.re| ≤ T := by
      have he' : P * (B * H ^ c) * H ^ d =
          (C * B * H ^ (a + b)) * (C * B * H ^ (c + d)) := by
        dsimp only [P]
        rw [pow_add H c d]
        noncomm_ring
      rw [he']
      calc
        _ ≤ ‖((C * B * H ^ (a + b)) * (C * B * H ^ (c + d))).trace‖ :=
          Complex.abs_re_le_norm _
        _ ≤ ‖C * B * H ^ (a + b)‖ * ‖C * B * H ^ (c + d)‖ :=
          trace_product_bound _ _
        _ ≤ (K * M ^ (a + b)) * (K * M ^ (c + d)) :=
          mul_le_mul (weighted_pair_pow_le C H B hC hB (a + b))
            (weighted_pair_pow_le C H B hC hB (c + d)) (norm_nonneg _) (by positivity)
        _ = T := by dsimp only [T]; simp only [pow_add]; ring
    have herr (j : ℕ) (hj : j < c) :
        |(P * (H ^ j * (H * B - B * H) * H ^ (c - 1 - j)) * H ^ d).trace.re| ≤
          2 * T := by
      let r := c - 1 - j
      have he' : P * (H ^ j * C * H ^ r) * H ^ d =
          C * B * H ^ (a + b) * C * H ^ j * C * H ^ (r + d) := by
        dsimp only [P]
        rw [pow_add H r d]
        noncomm_ring
      change |(P * (H ^ j * C * H ^ r) * H ^ d).trace.re| ≤ _
      rw [he']
      have hs : a + b + j + (r + d) + 1 = a + b + c + d := by
        dsimp only [r]
        omega
      calc
        _ ≤ M ^ (a + b + j + (r + d)) * K * ‖C ^ 2‖ :=
          three_commutator_word_bound_right C H B hC hB (a + b) j (r + d)
        _ ≤ M ^ (a + b + j + (r + d)) * K * (2 * M * K) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = 2 * T := by dsimp only [T]; rw [← hs, pow_succ]; ring
    calc
      _ ≤ T + (c : ℝ) * (2 * T) := trace_move_bound H B P (H ^ d) c T (2 * T) hbase herr
      _ = _ := by ring
  have herr (j : ℕ) (hj : j < a) :
      |(C * (H ^ j * (H * B - B * H) * H ^ (a - 1 - j)) * Q).trace.re| ≤
        (2 + 4 * (c : ℝ)) * T := by
    let r := a - 1 - j
    let X := C * H ^ j * C * H ^ (r + b)
    let Y := C * H ^ c * B * H ^ d
    have he : C * (H ^ j * C * H ^ r) * Q = X * Y := by
      dsimp only [Q, X, Y]
      rw [pow_add H r b]
      noncomm_ring
    change |(C * (H ^ j * C * H ^ r) * Q).trace.re| ≤ _
    rw [he, Matrix.trace_mul_comm X Y]
    have he' : Y * X = C * H ^ c * B * H ^ d * C * H ^ j * C * H ^ (r + b) := by
      dsimp only [X, Y]
      noncomm_ring
    rw [he']
    have hs : c + d + j + (r + b) + 1 = a + b + c + d := by
      dsimp only [r]
      omega
    calc
      _ ≤ (2 + 4 * (c : ℝ)) * M ^ (c + d + j + (r + b) + 1) * K ^ 2 :=
        three_commutator_power_word_bound H B hH hB c d j (r + b)
      _ = _ := by rw [hs]; dsimp only [T]; ring
  calc
    _ ≤ (1 + 2 * (c : ℝ)) * T + (a : ℝ) * ((2 + 4 * (c : ℝ)) * T) :=
      trace_move_bound H B C Q a _ _ hadj herr
    _ = _ := by dsimp only [T]; ring

end D5.S3.Quantum.Analysis.RefinedBMVNearScalarPowerReorder
