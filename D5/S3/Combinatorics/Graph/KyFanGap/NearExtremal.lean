/- GID: D5/S3/Combinatorics/Graph/KyFanGap/NearExtremal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/KyFanGap/NearExtremal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Order.Chebyshev, mathlib/module/Mathlib.Analysis.Matrix.Normed, mathlib/module/Mathlib.LinearAlgebra.Matrix.Vec]
   utility: none
   digest: Mean-square kernel approximation and row concentration control the compressed polynomial defects. -/

import D5.S3.Combinatorics.Graph.KyFanGap.UniformGap
import D5.S3.Combinatorics.Graph.KyFanGap.SignedVariational
import D5.S3.Arith.Lattices.Klartag.Completion.Discharge
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Vec

/-! Pointwise sign stability and the finite Cauchy--Schwarz inequality connect
matrix approximation errors with the two polynomial defects. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Matrix
open scoped BigOperators
open scoped InnerProductSpace Matrix.Norms.Frobenius

namespace D5.S3.Combinatorics.Graph.KyFanGap

private theorem sign_error_le (u b M : ℝ) (hb : b = -1 ∨ b = 1)
    (hu : |u| ≤ M) : (u ^ 2 - 1) ^ 2 ≤ (M + 1) ^ 2 * (u - b) ^ 2 := by
  have hbn : |b| = 1 := by rcases hb with rfl | rfl <;> norm_num
  have hbsq : b ^ 2 = 1 := by rcases hb with rfl | rfl <;> norm_num
  have hsum : |u + b| ≤ M + 1 := (abs_add_le u b).trans (by linarith)
  have hm : 0 ≤ M + 1 := le_trans (abs_nonneg _) hsum
  have hs : (u + b) ^ 2 ≤ (M + 1) ^ 2 := by
    exact sq_le_sq.mpr (by simpa only [abs_of_nonneg hm] using hsum)
  have hh := mul_le_mul_of_nonneg_right hs (sq_nonneg (u - b))
  have he : (u ^ 2 - 1) ^ 2 = (u + b) ^ 2 * (u - b) ^ 2 := by
    rw [← hbsq]
    ring
  rw [he]
  exact hh

private theorem row_error_le {n : ℕ}
    (H B : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (r : Fin n) :
    ((∑ s, H r s) / n - c) ^ 2 ≤
      2 * ((∑ s, (H r s - B r s) ^ 2) / n) +
        2 * ((∑ s, B r s) / n - c) ^ 2 := by
  have hcs : ((∑ s, (H r s - B r s)) / n) ^ 2 ≤
      (∑ s, (H r s - B r s) ^ 2) / n := by
    simpa using (sum_div_card_sq_le_sum_sq_div_card
      (s := Finset.univ) (f := fun s => H r s - B r s))
  have he : (∑ s, H r s) / n - c =
      (∑ s, (H r s - B r s)) / n + ((∑ s, B r s) / n - c) := by
    rw [Finset.sum_sub_distrib, sub_div]
    ring
  rw [he]
  nlinarith [sq_nonneg ((∑ s, (H r s - B r s)) / n - ((∑ s, B r s) / n - c))]

private theorem empiricalDefect_le {k n : ℕ} (hn : 0 < n)
    (q : Fin k → ℝ) (x : Fin n → Fin k → ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (c M : ℝ)
    (hB : ∀ r s, B r s = -1 ∨ B r s = 1)
    (hbound : ∀ r s, |bilinearKernel q (x r) (x s)| ≤ M) :
    empiricalDefect q x c ≤
      ((M + 1) ^ 2 + 2) *
        ((∑ r, ∑ s, (bilinearKernel q (x r) (x s) - B r s) ^ 2) / (n : ℝ) ^ 2) +
      2 * ((∑ r, ((∑ s, B r s) / n - c) ^ 2) / n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hf :
      (∑ r, ∑ s, (bilinearKernel q (x r) (x s) ^ 2 - 1) ^ 2) / (n : ℝ) ^ 2 ≤
        (M + 1) ^ 2 *
          ((∑ r, ∑ s, (bilinearKernel q (x r) (x s) - B r s) ^ 2) / (n : ℝ) ^ 2) := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s _
    exact sign_error_le _ _ _ (hB r s) (hbound r s)
  have hg :
      (∑ r, ((∑ s, bilinearKernel q (x r) (x s)) / n - c) ^ 2) / n ≤
        2 * ((∑ r, ∑ s, (bilinearKernel q (x r) (x s) - B r s) ^ 2) / (n : ℝ) ^ 2) +
          2 * ((∑ r, ((∑ s, B r s) / n - c) ^ 2) / n) := by
    calc
      _ ≤ (∑ r, (2 * ((∑ s, (bilinearKernel q (x r) (x s) - B r s) ^ 2) / n) +
          2 * ((∑ s, B r s) / n - c) ^ 2)) / (n : ℝ) := by
        apply div_le_div_of_nonneg_right _ hnpos.le
        exact Finset.sum_le_sum fun r _ =>
          row_error_le (fun r s => bilinearKernel q (x r) (x s)) B c r
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
        ring
  unfold empiricalDefect
  linarith

/-- A bounded rank-coordinate kernel cannot both approximate a sign matrix in
mean square and have that matrix's normalized row sums concentrate at the
inverse square root of a nonsquare coordinate dimension. -/
theorem bilinear_approximation_gap {k : ℕ} (hk : ¬ IsSquare k) (M : ℝ) :
    ∃ ε > 0, ∀ (n : ℕ), 0 < n → ∀ (q : Fin k → ℝ) (x : Fin n → Fin k → ℝ)
      (B : Matrix (Fin n) (Fin n) ℝ),
      (∀ r s, B r s = -1 ∨ B r s = 1) →
      (∀ r s, |bilinearKernel q (x r) (x s)| ≤ M) →
      ε ≤ ((∑ r, ∑ s, (bilinearKernel q (x r) (x s) - B r s) ^ 2) / (n : ℝ) ^ 2) +
        ((∑ r, ((∑ s, B r s) / n - 1 / Real.sqrt k) ^ 2) / n) := by
  obtain ⟨η, hη, hg⟩ := bilinear_defect_gap hk M
  let C : ℝ := (M + 1) ^ 2 + 2
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨η / C, div_pos hη hC, ?_⟩
  intro n hn q x B hB hb
  have hgap := hg n hn q x hb
  have hupper := empiricalDefect_le hn q x B (1 / Real.sqrt k) M hB hb
  have hr : 0 ≤ (∑ r, ((∑ s, B r s) / n - 1 / Real.sqrt k) ^ 2) / (n : ℝ) := by
    positivity
  apply (div_le_iff₀ hC).mpr
  dsimp [C]
  nlinarith [mul_nonneg (sq_nonneg (M + 1)) hr]

private def witnessColumns {k n : ℕ} (W : SignedWitness k n) : Matrix (Fin n) (Fin k) ℝ :=
  fun r i => W.vectors i r

private def witnessMatrix {k n : ℕ} (W : SignedWitness k n) : Matrix (Fin n) (Fin n) ℝ :=
  witnessColumns W * Matrix.diagonal W.signs * (witnessColumns W).transpose

private theorem witnessColumns_gram {k n : ℕ} (W : SignedWitness k n) :
    (witnessColumns W).transpose * witnessColumns W = 1 := by
  classical
  ext i j
  simpa [Matrix.mul_apply, Matrix.one_apply, witnessColumns, PiLp.inner_apply, mul_comm]
    using orthonormal_iff_ite.mp W.orthonormal_vectors i j

private theorem witnessSigns_sq {k n : ℕ} (W : SignedWitness k n) :
    Matrix.diagonal W.signs * Matrix.diagonal W.signs = 1 := by
  classical
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    simpa [Matrix.diagonal_apply, pow_two] using W.signs_sq i
  · simp [Matrix.diagonal_apply, Matrix.one_apply, h]

private theorem witnessMatrix_symm {k n : ℕ} (W : SignedWitness k n) :
    (witnessMatrix W).IsSymm := by
  unfold witnessMatrix
  rw [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.diagonal_transpose, Matrix.mul_assoc]

private theorem witnessMatrix_sq {k n : ℕ} (W : SignedWitness k n) :
    witnessMatrix W * witnessMatrix W = witnessColumns W * (witnessColumns W).transpose := by
  simp only [witnessMatrix, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (witnessColumns W).transpose, witnessColumns_gram, Matrix.one_mul]
  rw [← Matrix.mul_assoc (Matrix.diagonal W.signs), witnessSigns_sq, Matrix.one_mul]

private theorem witnessMatrix_cube {k n : ℕ} (W : SignedWitness k n) :
    witnessMatrix W * witnessMatrix W * witnessMatrix W = witnessMatrix W := by
  rw [witnessMatrix_sq]
  simp only [witnessMatrix, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (witnessColumns W).transpose, witnessColumns_gram, Matrix.one_mul]

private theorem real_frobenius_sq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖A‖ ^ 2 = ∑ r, ∑ s, A r s ^ 2 := by
  change ‖WithLp.toLp 2 (fun r => WithLp.toLp 2 (A r))‖ ^ 2 = _
  simp [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]

private theorem witnessMatrix_norm_sq {k n : ℕ} (W : SignedWitness k n) :
    ‖witnessMatrix W‖ ^ 2 = k := by
  calc
    _ = (witnessMatrix W).vec ⬝ᵥ (witnessMatrix W).vec := by
      rw [real_frobenius_sq]
      simp only [dotProduct, Matrix.vec, Fintype.sum_prod_type, pow_two]
      exact Finset.sum_comm
    _ = k := by
      rw [Matrix.vec_dotProduct_vec, (witnessMatrix_symm W).eq, witnessMatrix_sq,
        Matrix.trace_mul_comm, witnessColumns_gram]
      simp

private theorem witnessMatrix_apply {k n : ℕ} (W : SignedWitness k n)
    (x : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin (witnessMatrix W) x =
      ∑ i, (W.signs i * ⟪W.vectors i, x⟫_ℝ) • W.vectors i := by
  ext r
  simp only [witnessMatrix, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    Matrix.mulVec_mulVec]
  simp [Matrix.mulVec, Matrix.mul_apply, dotProduct, witnessColumns, Matrix.diagonal_apply,
    PiLp.inner_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm]
  rw [Finset.sum_comm]

private theorem witnessMatrix_contracts {k n : ℕ} (W : SignedWitness k n)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanLin (witnessMatrix W) x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [witnessMatrix_apply, ← real_inner_self_eq_norm_sq]
  rw [W.orthonormal_vectors.inner_sum]
  have hsign (i : Fin k) :
      (starRingEnd ℝ) (W.signs i * ⟪W.vectors i, x⟫_ℝ) *
        (W.signs i * ⟪W.vectors i, x⟫_ℝ) = ‖⟪W.vectors i, x⟫_ℝ‖ ^ 2 := by
    simp only [starRingEnd_apply, star_trivial, Real.norm_eq_abs, sq_abs]
    nlinarith [W.signs_sq i]
  simp_rw [hsign]
  exact W.orthonormal_vectors.sum_inner_products_le x

private theorem witnessMatrix_trace {k n : ℕ} (W : SignedWitness k n)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.trace (witnessMatrix W * M) = signedPairing W M := by
  have hdiag (i : Fin k) :
      ((witnessColumns W).transpose * M * witnessColumns W) i i =
        ⟪W.vectors i, Matrix.toEuclideanLin M (W.vectors i)⟫_ℝ := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, witnessColumns,
      Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      PiLp.inner_apply, Real.inner_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    ring
  calc
    _ = Matrix.trace (Matrix.diagonal W.signs *
        ((witnessColumns W).transpose * M * witnessColumns W)) := by
      simp only [witnessMatrix, Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    _ = _ := by
      simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply,
        signedPairing, ← hdiag]

private theorem frobenius_sub_smul_sq {n : ℕ}
    (M Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.IsSymm) (c : ℝ) :
    ‖M - c • Q‖ ^ 2 = ‖M‖ ^ 2 + c ^ 2 * ‖Q‖ ^ 2 -
      (2 * c) * Matrix.trace (Q * M) := by
  have hcross : Matrix.trace (Q * M) = ∑ r, ∑ s, M r s * Q r s := by
    rw [Matrix.trace_mul_comm]
    exact D5.S3.Arith.Lattices.Klartag.Completion.Discharge.trace_mul_eq_frobenius hQ
  have hid (a b : ℝ) : (a - c * b) ^ 2 = a ^ 2 + c ^ 2 * b ^ 2 -
      (2 * c) * (a * b) := by ring
  simp only [real_frobenius_sq, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, hcross]
  simp_rw [hid, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

private theorem map_norm_le_frobenius {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanLin M x‖ ≤ ‖M‖ * ‖x‖ := by
  have he : M * Matrix.replicateCol Unit x.ofLp =
      Matrix.replicateCol Unit (M *ᵥ x.ofLp) := by
    ext r j
    rfl
  have h := Matrix.frobenius_norm_mul M (Matrix.replicateCol Unit x.ofLp)
  rw [he, Matrix.frobenius_norm_replicateCol, Matrix.frobenius_norm_replicateCol] at h
  exact h

private theorem smoothed_matrix_bound {k n : ℕ} (W : SignedWitness k n)
    (T : Matrix (Fin n) (Fin n) ℝ) (hT : ‖T‖ = 1) (c : ℝ) (hc : 0 < c) :
    ‖c⁻¹ • (T * witnessMatrix W * T) - T‖ ≤
      (c⁻¹ * Real.sqrt k + (k : ℝ) + 1) * ‖T - c • witnessMatrix W‖ := by
  let Q := witnessMatrix W
  let E := T - c • Q
  have hQ : ‖Q‖ = Real.sqrt k := by
    rw [← Real.sqrt_sq (norm_nonneg Q), witnessMatrix_norm_sq]
  have he : c⁻¹ • (T * Q * T) - T =
      c⁻¹ • (E * Q * T) + Q * Q * E - E := by
    simp only [E, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
      Matrix.mul_smul, smul_sub, smul_smul]
    rw [witnessMatrix_cube, inv_mul_cancel₀ hc.ne', one_smul]
    abel
  rw [he]
  calc
    _ ≤ ‖c⁻¹ • (E * Q * T)‖ + ‖Q * Q * E‖ + ‖E‖ :=
      (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ c⁻¹ * (‖E‖ * ‖Q‖ * ‖T‖) + ‖Q‖ * ‖Q‖ * ‖E‖ + ‖E‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
      gcongr
      · exact (Matrix.frobenius_norm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (Matrix.frobenius_norm_mul _ _) (norm_nonneg _))
      · exact (Matrix.frobenius_norm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (Matrix.frobenius_norm_mul _ _) (norm_nonneg _))
    _ = _ := by
      rw [hT, hQ]
      change c⁻¹ * (‖E‖ * Real.sqrt k * 1) + Real.sqrt k * Real.sqrt k * ‖E‖ +
        ‖E‖ = (c⁻¹ * Real.sqrt k + k + 1) * ‖E‖
      nlinarith [congrArg (fun a : ℝ => a * ‖E‖) (Real.sq_sqrt (Nat.cast_nonneg k))]

private def smoothedCoordinates {k n : ℕ} (W : SignedWitness k n)
    (T : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) : Fin n → Fin k → ℝ :=
  fun r i => (Real.sqrt n / c) * Matrix.toEuclideanLin T (W.vectors i) r

private theorem smoothed_kernel_eq {k n : ℕ} (W : SignedWitness k n)
    (T : Matrix (Fin n) (Fin n) ℝ) (hT : T.IsSymm) (c : ℝ) (hc : c ≠ 0)
    (r s : Fin n) :
    bilinearKernel (fun i => c * W.signs i) (smoothedCoordinates W T c r)
      (smoothedCoordinates W T c s) =
        ((n : ℝ) / c) * (T * witnessMatrix W * T) r s := by
  classical
  have hmap (a : Fin n) (i : Fin k) :
      (T * witnessColumns W) a i = Matrix.toEuclideanLin T (W.vectors i) a := by
    rfl
  have hmat : T * witnessMatrix W * T =
      (T * witnessColumns W) * Matrix.diagonal W.signs * (T * witnessColumns W).transpose := by
    simp only [Matrix.transpose_mul, hT.eq, witnessMatrix, Matrix.mul_assoc]
  have hentry : (T * witnessMatrix W * T) r s =
      ∑ i, W.signs i * Matrix.toEuclideanLin T (W.vectors i) r *
        Matrix.toEuclideanLin T (W.vectors i) s := by
    rw [hmat]
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply, hmap, witnessColumns,
      Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      mul_assoc, mul_comm, mul_left_comm]
  have hcoeff : c * (Real.sqrt n / c) ^ 2 = (n : ℝ) / c := by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    field_simp
  rw [hentry]
  calc
    _ = (c * (Real.sqrt n / c) ^ 2) *
        ∑ i, W.signs i * Matrix.toEuclideanLin T (W.vectors i) r *
          Matrix.toEuclideanLin T (W.vectors i) s := by
      simp only [bilinearKernel, smoothedCoordinates, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [hcoeff]

private theorem smoothed_coordinate_bound {k n : ℕ} (hn : 0 < n)
    (W : SignedWitness k n) (T : Matrix (Fin n) (Fin n) ℝ)
    (hentry : ∀ r s, T r s ^ 2 = 1 / (n : ℝ) ^ 2)
    (c : ℝ) (hc : 0 < c) (hc2 : c ^ 2 * k = 1) (r : Fin n) (i : Fin k) :
    |smoothedCoordinates W T c r i| ≤ Real.sqrt k := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hu : (∑ s, W.vectors i s ^ 2) = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, W.orthonormal_vectors.norm_eq_one]
    norm_num
  have hrow : (∑ s, T r s ^ 2) = 1 / (n : ℝ) := by
    simp only [hentry, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun s => T r s)
    (fun s => W.vectors i s)
  rw [hu, hrow, mul_one] at hcs
  have hcs' : (∑ s, T r s * W.vectors i s) ^ 2 * (n : ℝ) ≤ 1 :=
    (le_div_iff₀ hnpos).mp hcs
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs, Real.sq_sqrt (Nat.cast_nonneg k)]
  change ((Real.sqrt n / c) * (∑ s, T r s * W.vectors i s)) ^ 2 ≤ (k : ℝ)
  rw [mul_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg n), div_mul_eq_mul_div]
  apply (div_le_iff₀ (sq_pos_of_pos hc)).mpr
  nlinarith

private theorem smoothed_kernel_bound {k n : ℕ} (hn : 0 < n)
    (W : SignedWitness k n) (T : Matrix (Fin n) (Fin n) ℝ)
    (hentry : ∀ r s, T r s ^ 2 = 1 / (n : ℝ) ^ 2)
    (c : ℝ) (hc : 0 < c) (hc2 : c ^ 2 * k = 1) (r s : Fin n) :
    |bilinearKernel (fun i => c * W.signs i) (smoothedCoordinates W T c r)
      (smoothedCoordinates W T c s)| ≤ c * (k : ℝ)^2 := by
  have hsign (i : Fin k) : |W.signs i| = 1 := by
    nlinarith [W.signs_sq i, sq_abs (W.signs i), abs_nonneg (W.signs i)]
  calc
    _ ≤ ∑ i, |c * W.signs i * smoothedCoordinates W T c r i *
        smoothedCoordinates W T c s i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin k, c * (Real.sqrt k) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos hc, hsign, mul_one]
      have hr := smoothed_coordinate_bound hn W T hentry c hc hc2 r i
      have hs := smoothed_coordinate_bound hn W T hentry c hc hc2 s i
      calc
        _ ≤ c * Real.sqrt k * Real.sqrt k := by gcongr
        _ = _ := by ring
    _ = _ := by
      simp only [Real.sq_sqrt (Nat.cast_nonneg k), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      ring

set_option maxHeartbeats 800000 in
/-- Every positive nonsquare prefix has a uniform Ky Fan gap. -/
theorem uniform_gap
    {k : ℕ} (hk1 : 1 ≤ k) (hk : ¬ IsSquare k) :
    ∃ δ > 0, ∀ n : ℕ, k ≤ n → ∀ A : Matrix (Fin n) (Fin n) ℝ,
      A.IsSymm → (∀ i j, A i j = 0 ∨ A i j = 1) →
        kyFan k A / n ≤ (1 + Real.sqrt k) / 2 - δ := by
  classical
  let c : ℝ := 1 / Real.sqrt k
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hspos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hkpos
  have hc : 0 < c := one_div_pos.mpr hspos
  have hcroot : c * Real.sqrt k = 1 := by dsimp [c]; field_simp
  have hc2 : c ^ 2 * k = 1 := by
    dsimp [c]
    rw [div_pow, one_pow, Real.sq_sqrt hkpos.le]
    field_simp
  let C : ℝ := c⁻¹ * Real.sqrt k + k + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let K : ℝ := 2 * c * C ^ 2 + 4 * c + 4 * c ^ 2
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨ε, hε, hgap⟩ := bilinear_approximation_gap hk (c * (k : ℝ)^2)
  refine ⟨ε / (2 * K), div_pos hε (by positivity), ?_⟩
  intro n hkn A hA h01
  have hn : 0 < n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
  obtain ⟨W, hW⟩ := exists_signed_pairing_eq_kyFan hkn A hA
  let B : Matrix (Fin n) (Fin n) ℝ := fun r s => 2 * A r s - 1
  let J : Matrix (Fin n) (Fin n) ℝ := fun _ _ => 1
  let T : Matrix (Fin n) (Fin n) ℝ := (1 / (n : ℝ)) • B
  let Q := witnessMatrix W
  let E := T - c • Q
  let e : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun _ => 1)
  let α := Matrix.trace (Q * T)
  let β := Matrix.trace (Q * J) / (n : ℝ)
  let d₁ := Real.sqrt (k : ℝ) - α
  let d₂ := 1 - β
  let D := (1 + Real.sqrt (k : ℝ)) - 2 * kyFan k A / (n : ℝ)
  have hB (r s : Fin n) : B r s = -1 ∨ B r s = 1 := by
    rcases h01 r s with h | h
    · left; simp [B, h]
    · right; norm_num [B, h]
  have hTentry (r s : Fin n) : T r s ^ 2 = 1 / (n : ℝ) ^ 2 := by
    rcases hB r s with h | h <;> simp [T, h, mul_pow, div_pow]
  have hTnorm : ‖T‖ = 1 := by
    have hh : ‖T‖ ^ 2 = 1 := by
      rw [real_frobenius_sq]
      simp only [hTentry, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp
    nlinarith [norm_nonneg T]
  have hTsym : T.IsSymm := by
    apply Matrix.IsSymm.ext
    intro r s
    change (1 / (n : ℝ)) * (2 * A s r - 1) =
      (1 / (n : ℝ)) * (2 * A r s - 1)
    rw [hA.apply]
  have hcentering : T = (2 / (n : ℝ)) • A - (1 / (n : ℝ)) • J := by
    ext r s
    change (1 / (n : ℝ)) * (2 * A r s - 1) =
      (2 / (n : ℝ)) * A r s - (1 / (n : ℝ)) * 1
    ring
  have hα : α = 2 * kyFan k A / (n : ℝ) - β := by
    dsimp [α, β, Q]
    rw [hcentering, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, witnessMatrix_trace, hW]
    ring
  have hD : d₁ + d₂ = D := by dsimp [d₁, d₂, D]; rw [hα]; ring
  have hE : ‖E‖ ^ 2 = 2 * c * d₁ := by
    dsimp [E, d₁, α, Q]
    rw [frobenius_sub_smul_sq T _ (witnessMatrix_symm W), hTnorm, witnessMatrix_norm_sq]
    nlinarith [hc2, hcroot]
  have hd₁ : 0 ≤ d₁ := by nlinarith [sq_nonneg ‖E‖]
  have henorm : ‖e‖ ^ 2 = (n : ℝ) := by
    simp [EuclideanSpace.real_norm_sq_eq, e]
  have hones : Matrix.trace (Q * J) = ⟪e, Matrix.toEuclideanLin Q e⟫_ℝ := by
    change (∑ i, ∑ j, Q i j * 1) = ⟪e, Matrix.toEuclideanLin Q e⟫_ℝ
    simp [e, Matrix.toEuclideanLin,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, PiLp.inner_apply]
  have hvec : ‖Matrix.toEuclideanLin Q e - e‖ ^ 2 ≤ 2 * (n : ℝ) * d₂ := by
    have hh := witnessMatrix_contracts W e
    have hd : (n : ℝ) * d₂ = (n : ℝ) - Matrix.trace (Q * J) := by
      dsimp [d₂, β]
      field_simp
    rw [norm_sub_sq_real, real_inner_comm, ← hones, henorm]
    rw [henorm] at hh
    nlinarith
  have hd₂ : 0 ≤ d₂ := by
    nlinarith [sq_nonneg ‖Matrix.toEuclideanLin Q e - e‖]
  let x := smoothedCoordinates W T c
  let q : Fin k → ℝ := fun i => c * W.signs i
  let F : Matrix (Fin n) (Fin n) ℝ := c⁻¹ • (T * Q * T) - T
  have hF : ‖F‖ ^ 2 ≤ C ^ 2 * ‖E‖ ^ 2 := by
    have hh := smoothed_matrix_bound W T hTnorm c hc
    have h := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC.le (norm_nonneg E))).mpr hh
    simpa only [mul_pow] using h
  have happrox :
      ((∑ r, ∑ s, (bilinearKernel q (x r) (x s) - B r s) ^ 2) / (n : ℝ) ^ 2) = ‖F‖ ^ 2 := by
    have he (r s : Fin n) : bilinearKernel q (x r) (x s) - B r s =
        (n : ℝ) * F r s := by
      have hh := smoothed_kernel_eq W T hTsym c hc.ne' r s
      dsimp [q, x, F, Q] at *
      rw [hh]
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, T]
      field_simp
    simp_rw [he, mul_pow]
    simp only [← Finset.mul_sum]
    rw [← real_frobenius_sq]
    field_simp
  have hroweq :
      ((∑ r, ((∑ s, B r s) / (n : ℝ) - c) ^ 2) / (n : ℝ)) =
        ‖Matrix.toEuclideanLin T e - c • e‖ ^ 2 / (n : ℝ) := by
    congr 1
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro r _
    congr 1
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      T, e, Finset.mul_sum, div_eq_mul_inv, mul_comm]
  have hrow : ‖Matrix.toEuclideanLin T e - c • e‖ ^ 2 / (n : ℝ) ≤
      2 * ‖E‖ ^ 2 + 4 * c ^ 2 * d₂ := by
    let u := Matrix.toEuclideanLin E e
    let v := c • (Matrix.toEuclideanLin Q e - e)
    have heq : Matrix.toEuclideanLin T e - c • e = u + v := by
      dsimp [u, v, E]
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply]
      module
    have hu : ‖u‖ ^ 2 ≤ ‖E‖ ^ 2 * (n : ℝ) := by
      have hh := map_norm_le_frobenius E e
      have hh' := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hh
      simpa only [mul_pow, henorm] using hh'
    have hv : ‖v‖ ^ 2 ≤ c ^ 2 * (2 * (n : ℝ) * d₂) := by
      dsimp [v]
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      exact mul_le_mul_of_nonneg_left hvec (sq_nonneg c)
    have hadd := norm_add_le u v
    rw [heq]
    apply (div_le_iff₀ hnpos).mpr
    nlinarith [sq_nonneg (‖u‖ - ‖v‖), norm_nonneg (u + v), norm_nonneg u, norm_nonneg v]
  have hlower := hgap n hn q x B hB (smoothed_kernel_bound hn W T hTentry c hc hc2)
  rw [happrox, hroweq] at hlower
  have hfinal : ε ≤ K * D := by
    have hnon1 : 0 ≤ 2 * c * C ^ 2 := by positivity
    have hnon2 : 0 ≤ 4 * c := by positivity
    have hnon3 : 0 ≤ 4 * c ^ 2 := by positivity
    have hd1 : 0 ≤ D - d₁ := by linarith
    have hd2 : 0 ≤ D - d₂ := by linarith
    dsimp [K]
    nlinarith [mul_nonneg hnon1 hd1, mul_nonneg hnon2 hd1, mul_nonneg hnon3 hd2]
  have hdelta : ε / (2 * K) ≤ (1 + Real.sqrt k) / 2 - kyFan k A / n := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * K)).mpr
    dsimp [D] at hfinal
    convert hfinal using 1 <;> ring
  linarith

end D5.S3.Combinatorics.Graph.KyFanGap
