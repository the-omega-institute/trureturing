/- GID: D5/S3/Quantum/Reduction/WeightedWordDefect
   generality: G
   mirror-B: D5/B/S3/Quantum/Reduction/WeightedWordDefect
   mirror-E: none(waiver:analytic-word-estimate)
   anchors: []
   utility: none
   digest: Weighted pair defects control finite Hermitian words under a UCP map. -/

import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.Quantum.Reduction.IsometricCompression

/-! # Weighted errors of finite Hermitian words

A finite Kraus dilation identifies the multiplicative defect with a discarded
Gram product. Unbounded finite-word induction gives the full weighted pair sum
in the Euclidean operator norm, including zero norms and empty coordinate types.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators Matrix CStarAlgebra ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Reduction.WeightedWordDefect

open Matrix D5.S3.Quantum.Reduction.IsometricCompression

variable {d k n s : Type*} [Fintype d] [DecidableEq d]
  [Fintype k] [DecidableEq k] [Fintype n] [DecidableEq n]
  [Fintype s] [DecidableEq s]

/-- The total weight of all single deletions, with no division by a letter's norm. -/
def singleWeight {α : Type*} (M ε : α → ℝ) : List α → ℝ
  | [] => 0
  | a :: w => ε a * (w.map M).prod + M a * singleWeight M ε w

/-- The total weight of all ordered-position pairs, each with its two norms deleted. -/
def pairWeight {α : Type*} (M ε : α → ℝ) : List α → ℝ
  | [] => 0
  | a :: w => ε a * singleWeight M ε w + M a * pairWeight M ε w

private lemma complement_star (V : Matrix n k ℂ) :
    (1 - support V)ᴴ = 1 - support V := by
  simp [support]

private lemma complement_sq (V : Matrix n k ℂ) (hV : Vᴴ * V = 1) :
    (1 - support V) * (1 - support V) = 1 - support V := by
  have hP : support V * support V = support V := by
    simp [support, Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V, hV]
  calc
    (1 - support V) * (1 - support V) =
        1 - support V - support V + support V * support V := by noncomm_ring
    _ = 1 - support V := by rw [hP]; abel

private lemma complement_norm (V : Matrix n k ℂ) (hV : Vᴴ * V = 1) :
    ‖1 - support V‖ ≤ 1 := by
  apply IsStarProjection.norm_le
  exact ⟨complement_sq V hV, complement_star V⟩

private lemma frame_norm (V : Matrix n k ℂ) (hV : Vᴴ * V = 1) : ‖V‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self V
  rw [hV] at h
  have h1 : ‖(1 : Matrix k k ℂ)‖ ≤ 1 :=
    IsStarProjection.norm_le _ (IsStarProjection.one _)
  nlinarith [norm_nonneg V]

private lemma compression_norm (V : Matrix n k ℂ) (hV : Vᴴ * V = 1)
    (A : Matrix n n ℂ) : ‖compress V A‖ ≤ ‖A‖ := by
  calc
    ‖compress V A‖ ≤ (‖Vᴴ‖ * ‖A‖) * ‖V‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ ‖A‖ := by
      rw [Matrix.l2_opNorm_conjTranspose]
      have hv := frame_norm V hV
      nlinarith [norm_nonneg V, norm_nonneg A, mul_nonneg (norm_nonneg V) (norm_nonneg A)]

private lemma gram (V : Matrix n k ℂ) (hV : Vᴴ * V = 1)
    (X Y : Matrix n n ℂ) :
    compress V (Xᴴ * Y) - (compress V X)ᴴ * compress V Y =
      (normal V (X * V))ᴴ * normal V (Y * V) := by
  have hQ := complement_sq V hV
  simp only [normal, compress, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    complement_star, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (1 - support V) (1 - support V), hQ]
  simp [support, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

private lemma normal_residual (V : Matrix n k ℂ) (A : Matrix n n ℂ) :
    normal V (A * V) = A * V - V * compress V A := by
  simp [normal, support, compress, Matrix.sub_mul, Matrix.mul_assoc]

/-- Finite amplification of a matrix on a labelled environment. -/
def amplify : Matrix d d ℂ →⋆ₐ[ℂ] Matrix (d × s) (d × s) ℂ where
  toFun A := blockDiagonal (fun _ : s => A)
  map_one' := blockDiagonal_one
  map_mul' A B := blockDiagonal_mul _ _
  map_zero' := blockDiagonal_zero
  map_add' A B := blockDiagonal_add _ _
  commutes' z := by
    ext ⟨i,r⟩ ⟨j,t⟩
    simp [blockDiagonal_apply, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply,
      Matrix.one_apply, Prod.ext_iff, ite_and]
    split_ifs <;> simp_all
  map_star' A := by exact (blockDiagonal_conjTranspose _).symm


private lemma norm_one_le_matrix : ‖(1 : Matrix d d ℂ)‖ ≤ 1 :=
  IsStarProjection.norm_le _ (IsStarProjection.one _)

private lemma mapped_norm_prod_le
    (π : Matrix d d ℂ →⋆ₐ[ℂ] Matrix n n ℂ)
    (V : Matrix n k ℂ) (hV : Vᴴ * V = 1) (w : List (Matrix d d ℂ)) :
    ‖(w.map (fun a => compress V (π a))).prod‖ ≤ (w.map norm).prod := by
  by_cases hw : w = []
  · subst w
    simpa using (norm_one_le_matrix (d := k))
  have hp := List.norm_prod_le' (l := w.map (fun a => compress V (π a)))
    (by simpa using hw)
  simp only [List.map_map, Function.comp_def] at hp
  exact hp.trans (List.prod_map_le_prod_map₀ _ _ (fun _ _ => norm_nonneg _)
    (fun a _ => (compression_norm V hV _).trans
      (NonUnitalStarAlgHom.norm_apply_le π a)))

private lemma residual_product (π : Matrix d d ℂ →⋆ₐ[ℂ] Matrix n n ℂ)
    (V : Matrix n k ℂ) (a : Matrix d d ℂ) (w : List (Matrix d d ℂ)) :
    π ((a :: w).prod) * V - V * ((a :: w).map (fun a => compress V (π a))).prod =
      π a * (π w.prod * V - V * (w.map (fun a => compress V (π a))).prod) +
        normal V (π a * V) * (w.map (fun a => compress V (π a))).prod := by
  simp only [List.prod_cons, List.map_cons, map_mul, normal_residual,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

private lemma residual_bound (π : Matrix d d ℂ →⋆ₐ[ℂ] Matrix n n ℂ)
    (V : Matrix n k ℂ) (hV : Vᴴ * V = 1) (w : List (Matrix d d ℂ)) :
    ‖π w.prod * V - V * (w.map (fun a => compress V (π a))).prod‖ ≤
      singleWeight norm (fun a => ‖normal V (π a * V)‖) w := by
  induction w with
  | nil => simp [singleWeight]
  | cons a w ih =>
      rw [residual_product]
      calc
        _ ≤ ‖π a‖ * ‖π w.prod * V - V * (w.map (fun a => compress V (π a))).prod‖ +
            ‖normal V (π a * V)‖ * ‖(w.map (fun a => compress V (π a))).prod‖ :=
          (norm_add_le _ _).trans (add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _))
        _ ≤ ‖a‖ * singleWeight norm (fun a => ‖normal V (π a * V)‖) w +
            ‖normal V (π a * V)‖ * (w.map norm).prod :=
          add_le_add (mul_le_mul (NonUnitalStarAlgHom.norm_apply_le π a) ih
            (norm_nonneg _) (norm_nonneg _))
            (mul_le_mul_of_nonneg_left (mapped_norm_prod_le π V hV w) (norm_nonneg _))
        _ = _ := by simp [singleWeight, add_comm]

private lemma leakage_bound (π : Matrix d d ℂ →⋆ₐ[ℂ] Matrix n n ℂ)
    (V : Matrix n k ℂ) (hV : Vᴴ * V = 1) (w : List (Matrix d d ℂ)) :
    ‖normal V (π w.prod * V)‖ ≤
      singleWeight norm (fun a => ‖normal V (π a * V)‖) w := by
  have hQV : (1 - support V) * V = 0 := by
    simp [support, Matrix.sub_mul, Matrix.mul_assoc, hV]
  have heq : normal V (π w.prod * V) =
      (1 - support V) * (π w.prod * V - V * (w.map (fun a => compress V (π a))).prod) := by
    simp [normal, Matrix.mul_sub, ← Matrix.mul_assoc (1 - support V) V, hQV]
  rw [heq]
  exact (Matrix.l2_opNorm_mul _ _).trans
    ((mul_le_mul_of_nonneg_right (complement_norm V hV) (norm_nonneg _)).trans
      (by simpa using residual_bound π V hV w))

private lemma compression_word_bound (π : Matrix d d ℂ →⋆ₐ[ℂ] Matrix n n ℂ)
    (V : Matrix n k ℂ) (hV : Vᴴ * V = 1) (w : List (Matrix d d ℂ))
    (hw : ∀ a ∈ w, aᴴ = a) :
    ‖compress V (π w.prod) - (w.map (fun a => compress V (π a))).prod‖ ≤
      pairWeight norm (fun a => ‖normal V (π a * V)‖) w := by
  induction w with
  | nil => simp [compress, hV, pairWeight]
  | cons a w ih =>
      have ha : (π a)ᴴ = π a := by
        change star (π a) = π a
        rw [← map_star]
        exact congrArg π (hw a (by simp))
      have hca : (compress V (π a))ᴴ = compress V (π a) := by
        simp [compress, ha, Matrix.mul_assoc]
      have hg := gram V hV (π a) (π w.prod)
      rw [ha, hca] at hg
      have heq : compress V (π ((a :: w).prod)) -
          ((a :: w).map (fun a => compress V (π a))).prod =
          (normal V (π a * V))ᴴ * normal V (π w.prod * V) +
          compress V (π a) * (compress V (π w.prod) -
            (w.map (fun a => compress V (π a))).prod) := by
        rw [← hg]
        simp only [List.prod_cons, List.map_cons, map_mul, Matrix.mul_sub]
        abel
      rw [heq]
      calc
        _ ≤ ‖normal V (π a * V)‖ * ‖normal V (π w.prod * V)‖ +
            ‖compress V (π a)‖ * ‖compress V (π w.prod) -
              (w.map (fun a => compress V (π a))).prod‖ := by
          have hn := Matrix.l2_opNorm_mul (normal V (π a * V))ᴴ (normal V (π w.prod * V))
          rw [Matrix.l2_opNorm_conjTranspose] at hn
          exact (norm_add_le _ _).trans (add_le_add hn (Matrix.l2_opNorm_mul _ _))
        _ ≤ ‖normal V (π a * V)‖ * singleWeight norm (fun a => ‖normal V (π a * V)‖) w +
            ‖a‖ * pairWeight norm (fun a => ‖normal V (π a * V)‖) w :=
          add_le_add (mul_le_mul_of_nonneg_left (leakage_bound π V hV w) (norm_nonneg _))
            (mul_le_mul ((compression_norm V hV _).trans
              (NonUnitalStarAlgHom.norm_apply_le π a))
              (ih (fun b hb => hw b (by simp [hb]))) (norm_nonneg _) (norm_nonneg _))
        _ = _ := rfl


local notation "matrixAction" => (fun
    (Φ : CompletelyPositiveMap (CStarMatrix d d ℂ) (CStarMatrix k k ℂ))
    (A : Matrix d d ℂ) => CStarMatrix.ofMatrix.symm (Φ (CStarMatrix.ofMatrix A)))

/-- Stack the adjoints of the original rectangular Kraus witnesses. -/
def krausFrame (K : s → Matrix k d ℂ) : Matrix (d × s) k ℂ :=
  fun p i => star (K p.2 i p.1)

private lemma frame_compress (K : s → Matrix k d ℂ) (A : Matrix d d ℂ) :
    compress (krausFrame K) (amplify (s := s) A) = ∑ r, K r * A * (K r)ᴴ := by
  ext i j
  change (((krausFrame K)ᴴ * blockDiagonal (fun _ : s => A)) * krausFrame K) i j = _
  simp only [Matrix.mul_apply, krausFrame, Matrix.conjTranspose_apply, star_star,
    blockDiagonal_apply, Matrix.sum_apply, Fintype.sum_prod_type, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact Finset.sum_comm

private lemma actual_frame_isometry
    (Φ : CompletelyPositiveMap (CStarMatrix d d ℂ) (CStarMatrix k k ℂ))
    (hΦ : Φ 1 = 1) :
    let K := (D5.S3.Quantum.Foundation.FiniteKrausChannel.krausRepresentation Φ).1
    (krausFrame K)ᴴ * krausFrame K = 1 := by
  intro K
  have h := (D5.S3.Quantum.Foundation.FiniteKrausChannel.krausRepresentation Φ).2 (1 : Matrix d d ℂ)
  simp only [Matrix.mul_one] at h
  have h1 : matrixAction Φ 1 = 1 := by
    change CStarMatrix.ofMatrix.symm (Φ 1) = 1
    rw [hΦ]
    rfl
  have h2 := frame_compress K (1 : Matrix d d ℂ)
  rw [map_one] at h2
  simp only [compress, Matrix.mul_one] at h2
  exact h2.trans (h.symm.trans h1)

private lemma actual_compress
    (Φ : CompletelyPositiveMap (CStarMatrix d d ℂ) (CStarMatrix k k ℂ))
    (A : Matrix d d ℂ) :
    compress (krausFrame (D5.S3.Quantum.Foundation.FiniteKrausChannel.krausRepresentation Φ).1)
        (amplify (s := k × d) A) = matrixAction Φ A := by
  rw [frame_compress]
  exact ((D5.S3.Quantum.Foundation.FiniteKrausChannel.krausRepresentation Φ).2 A).symm

private lemma leakage_sqrt (π : Matrix d d ℂ →⋆ₐ[ℂ] Matrix n n ℂ)
    (V : Matrix n k ℂ) (hV : Vᴴ * V = 1) (A : Matrix d d ℂ) :
    ‖normal V (π A * V)‖ = Real.sqrt
      ‖compress V (π (Aᴴ * A)) - (compress V (π A))ᴴ * compress V (π A)‖ := by
  have h := gram V hV (π A) (π A)
  have hp : π (Aᴴ * A) = (π A)ᴴ * π A := by
    rw [map_mul]
    change π (star A) * π A = star (π A) * π A
    rw [map_star]
  rw [hp, h, Matrix.l2_opNorm_conjTranspose_mul_self, ← sq]
  exact (Real.sqrt_sq (norm_nonneg _)).symm

/-- The complete weighted error estimate for the actual finite UCP matrix map.
The list may be empty, may repeat letters, and may contain zero matrices. -/
private lemma ucp_pairWeight_bound
    (Φ : CompletelyPositiveMap (CStarMatrix d d ℂ) (CStarMatrix k k ℂ))
    (hΦ : Φ 1 = 1) (w : List (Matrix d d ℂ)) (hw : ∀ A ∈ w, Aᴴ = A) :
    ‖matrixAction Φ w.prod - (w.map (matrixAction Φ)).prod‖ ≤
      pairWeight norm (fun A => Real.sqrt
        ‖matrixAction Φ (Aᴴ * A) - (matrixAction Φ A)ᴴ * matrixAction Φ A‖) w := by
  let K := (D5.S3.Quantum.Foundation.FiniteKrausChannel.krausRepresentation Φ).1
  let V := krausFrame K
  have hV : Vᴴ * V = 1 := actual_frame_isometry Φ hΦ
  have h := compression_word_bound (amplify (s := k × d)) V hV w hw
  have hc : ∀ A, compress V (amplify (s := k × d) A) = matrixAction Φ A :=
    actual_compress Φ
  have he : ∀ A, ‖normal V (amplify (s := k × d) A * V)‖ =
      Real.sqrt ‖matrixAction Φ (Aᴴ * A) - (matrixAction Φ A)ᴴ * matrixAction Φ A‖ := by
    intro A
    rw [leakage_sqrt (amplify (s := k × d)) V hV A, hc, hc]
  simp_rw [hc, he] at h
  exact h




private def singleSum {ℓ : ℕ} (M ε : Fin ℓ → ℝ) : ℝ :=
  ∑ i, ε i * ∏ r, if r = i then 1 else M r

/-- The explicit sum over all positional pairs i < j, omitting exactly those two norms. -/
def pairSum {ℓ : ℕ} (M ε : Fin ℓ → ℝ) : ℝ :=
  ∑ i, ∑ j, if i < j then ε i * ε j * ∏ r, if r = i ∨ r = j then 1 else M r else 0

private lemma singleSum_succ {ℓ : ℕ} (M ε : Fin (ℓ + 1) → ℝ) :
    singleSum M ε = ε 0 * (∏ r : Fin ℓ, M r.succ) +
      M 0 * singleSum (fun r => M r.succ) (fun r => ε r.succ) := by
  simp only [singleSum, Fin.sum_univ_succ, Fin.prod_univ_succ]
  simp only [Fin.succ_ne_zero, (Ne.symm (Fin.succ_ne_zero _)), Fin.succ_inj, ite_true, ite_false,
    one_mul, mul_one]
  rw [Finset.mul_sum]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma pairSum_succ {ℓ : ℕ} (M ε : Fin (ℓ + 1) → ℝ) :
    pairSum M ε = ε 0 * singleSum (fun r => M r.succ) (fun r => ε r.succ) +
      M 0 * pairSum (fun r => M r.succ) (fun r => ε r.succ) := by
  simp only [pairSum, Fin.sum_univ_succ, Fin.prod_univ_succ]
  simp only [Fin.lt_irrefl, Fin.succ_pos, Fin.not_lt_zero, Fin.succ_lt_succ_iff,
    Fin.succ_ne_zero, (Ne.symm (Fin.succ_ne_zero _)), Fin.succ_inj, false_or, or_false, true_or,
    ite_true, ite_false, zero_add, mul_one, one_mul]
  simp only [singleSum, Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring

private lemma singleWeight_ofFn {α : Type*} (M ε : α → ℝ) {ℓ : ℕ} (A : Fin ℓ → α) :
    singleWeight M ε (List.ofFn A) = singleSum (fun i => M (A i)) (fun i => ε (A i)) := by
  induction ℓ with
  | zero => simp [singleWeight, singleSum]
  | succ ℓ ih =>
      rw [List.ofFn_succ, singleWeight, singleSum_succ, ih]
      simp [List.map_ofFn, List.prod_ofFn]

private lemma pairWeight_ofFn {α : Type*} (M ε : α → ℝ) {ℓ : ℕ} (A : Fin ℓ → α) :
    pairWeight M ε (List.ofFn A) = pairSum (fun i => M (A i)) (fun i => ε (A i)) := by
  induction ℓ with
  | zero => simp [pairWeight, pairSum]
  | succ ℓ ih =>
      rw [List.ofFn_succ, pairWeight, pairSum_succ, singleWeight_ofFn, ih]

/-- The complete weighted pair bound for an arbitrary finite ordered Hermitian word
under one actual finite-dimensional unital completely positive map. -/
theorem ucp_word_pair_bound
    (Φ : CompletelyPositiveMap (CStarMatrix d d ℂ) (CStarMatrix k k ℂ))
    (hΦ : Φ 1 = 1) (w : List (Matrix d d ℂ)) (hw : ∀ A ∈ w, Aᴴ = A) :
    ‖matrixAction Φ w.prod - (w.map (matrixAction Φ)).prod‖ ≤
      pairSum (fun i : Fin w.length => ‖w.get i‖) (fun i => Real.sqrt
        ‖matrixAction Φ ((w.get i)ᴴ * w.get i) -
          (matrixAction Φ (w.get i))ᴴ * matrixAction Φ (w.get i)‖) := by
  have h := ucp_pairWeight_bound Φ hΦ w hw
  have heq := pairWeight_ofFn norm (fun A => Real.sqrt
    ‖matrixAction Φ (Aᴴ * A) - (matrixAction Φ A)ᴴ * matrixAction Φ A‖) w.get
  rw [List.ofFn_get] at heq
  exact h.trans_eq heq

#print axioms ucp_word_pair_bound

end D5.S3.Quantum.Reduction.WeightedWordDefect
