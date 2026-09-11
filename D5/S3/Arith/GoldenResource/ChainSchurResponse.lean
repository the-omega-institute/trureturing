/- GID: D5/S3/Arith/GoldenResource/ChainSchurResponse
   generality: G
   mirror-B: D5/B/S3/Arith/GoldenResource/ChainSchurResponse
   mirror-E: none(waiver:general-matrix-family)
   anchors: []
   utility: none
   digest: Chain Schur responses have exact linear coefficients and a quadratic remainder. -/

import D5.S3.Arith.GoldenResource.ChainBlockPencil
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.Matrix.Normed

namespace D5.S3.Arith.GoldenResource.ChainSchurResponse

open Matrix TridiagonalChainInverse ChainBlockPencil
open scoped BigOperators Matrix.Norms.Operator

noncomputable section

/-- Two uses of the inverse-difference identity give an exact second-order remainder. -/
theorem inverse_first_order {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A E : Matrix ι ι ℝ) (hA : IsUnit A) (hAE : IsUnit (A + E)) :
    (A + E)⁻¹ = A⁻¹ - A⁻¹ * E * A⁻¹ + A⁻¹ * E * A⁻¹ * E * (A + E)⁻¹ := by
  have h := Matrix.inv_sub_inv (show IsUnit A ↔ IsUnit (A + E) from
    ⟨fun _ => hAE, fun _ => hA⟩)
  rw [add_sub_cancel_left] at h
  have hfirst : (A + E)⁻¹ = A⁻¹ - A⁻¹ * E * (A + E)⁻¹ := by
    rw [← h]
    abel
  calc
    (A + E)⁻¹ = A⁻¹ - A⁻¹ * E * (A + E)⁻¹ := hfirst
    _ = A⁻¹ - A⁻¹ * E * (A⁻¹ - A⁻¹ * E * (A + E)⁻¹) := by
      conv_lhs => arg 2; arg 2; rw [hfirst]
    _ = _ := by noncomm_ring

/-- The first inverse column of one chain; chain length is `n + 1`. -/
def w (n : ℕ) : Fin (n + 1) → ℝ := (H (n + 1))⁻¹ *ᵥ Pi.single 0 1

/-- The common visible mass coefficient, using the Euclidean sum of squares. -/
def z (n : ℕ) : ℝ := 1 + ∑ i, w n i ^ 2

/-- Transfer from the first to the last vertex of one chain. -/
def t (n : ℕ) : ℝ := w n (Fin.last n)

/-- The endpoint square divided by the common mass coefficient. -/
def eta (n : ℕ) : ℝ := t n ^ 2 / z n

/-- The hidden spatial block is taken from the existing block pencil. -/
def hiddenSpatial (n : ℕ) (k b : ℝ) : Matrix (Hidden n) (Hidden n) ℝ :=
  (G n k b).submatrix Sum.inr Sum.inr

/-- The hidden perturbation of the mass matrix. -/
def perturbation (n : ℕ) (k b s μ : ℝ) : Matrix (Hidden n) (Hidden n) ℝ :=
  μ • hiddenSpatial n k b - s • 1

/-- The visible Schur response of the two-chain pencil. -/
def response (n : ℕ) (k b s μ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 + k * μ - s) • 1 -
    B n * (hiddenBlock n + perturbation n k b s μ)⁻¹ * (B n)ᵀ

/-- The negative spectral coefficient before normalization. -/
def Z (n : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  1 + (B n * (hiddenBlock n)⁻¹) * ((hiddenBlock n)⁻¹ * (B n)ᵀ)

/-- The spatial coefficient before normalization. -/
def C (n : ℕ) (k b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  k • 1 + (B n * (hiddenBlock n)⁻¹) * hiddenSpatial n k b *
    ((hiddenBlock n)⁻¹ * (B n)ᵀ)

/-- The actual matrix product used for the normalized effective principal part. -/
def effective (n : ℕ) (k b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (Z n)⁻¹ * C n k b

/-- The signed exact Schur remainder has two explicit perturbation factors. -/
def remainder (n : ℕ) (k b s μ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  -(B n * ((hiddenBlock n)⁻¹ * perturbation n k b s μ * (hiddenBlock n)⁻¹ *
    perturbation n k b s μ * (hiddenBlock n + perturbation n k b s μ)⁻¹) * (B n)ᵀ)

private theorem hidden_posDef (n : ℕ) : (hiddenBlock n).PosDef := by
  have he : (K n).submatrix Sum.inr Sum.inr = hiddenBlock n := by
    ext i j
    rfl
  rw [← he]
  exact (mass_posDef n).submatrix Sum.inr_injective

private theorem hidden_inverse (n : ℕ) :
    (hiddenBlock n)⁻¹ = fromBlocks (H (n + 1))⁻¹ 0 0 (H (n + 1))⁻¹ := by
  simpa [hiddenBlock] using
    inv_fromBlocks_zero₂₁_of_isUnit_iff (H (n + 1)) 0 (H (n + 1)) Iff.rfl

private def W (n : ℕ) : Matrix (Hidden n) (Fin 2) ℝ :=
  Sum.elim (fun i j => if j = 0 then w n i else 0)
    (fun i j => if j = 0 then 0 else w n i)

private theorem inverse_coupling (n : ℕ) : (hiddenBlock n)⁻¹ * (B n)ᵀ = W n := by
  rw [hidden_inverse]
  ext i j
  rcases i with i | i <;> fin_cases j <;>
    simp [Matrix.mul_apply, B, W, w, mulVec, dotProduct,
      Pi.single_apply]

private theorem coupling_inverse (n : ℕ) : B n * (hiddenBlock n)⁻¹ = (W n)ᵀ := by
  have hs : (hiddenBlock n)ᵀ = hiddenBlock n :=
    (isHermitian_iff_isSymm.mp (hidden_posDef n).isHermitian).eq
  have h := congrArg Matrix.transpose (inverse_coupling n)
  simpa only [transpose_mul, transpose_transpose, transpose_nonsing_inv, hs] using h

/-- The common mass coefficient is strictly positive. -/
theorem z_pos (n : ℕ) : 0 < z n := by
  have hs : 0 ≤ ∑ i, w n i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  dsimp [z]
  linarith

/-- The endpoint formula reuses the inverse column of the chain. -/
theorem endpoint_formula (n : ℕ) : t n = 1 / (chainDet (n + 1) : ℝ) :=
  chain_endpoint_transfer n

/-- The negative spectral coefficient is the same scalar on both visible coordinates. -/
theorem Z_eq (n : ℕ) : Z n = z n • 1 := by
  rw [Z, coupling_inverse, inverse_coupling]
  ext i j
  change (1 : Matrix (Fin 2) (Fin 2) ℝ) i j +
    (∑ a, W n a i * W n a j) = z n * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j
  fin_cases i <;> fin_cases j <;>
    simp [Fintype.sum_sum_type, W, z, pow_two]

private theorem hidden_spatial_diagonal (n : ℕ) (k b : ℝ) :
    hiddenSpatial n k b = diagonal
      (Sum.elim (fun i => k - if i = Fin.last n then b else 0) (fun _ => k)) := by
  ext i j
  simp [hiddenSpatial, G, spatialWeight, Matrix.submatrix_apply, Matrix.diagonal_apply]

private theorem weighted_column (n : ℕ) (k b : ℝ) :
    (∑ i, w n i * (k - if i = Fin.last n then b else 0) * w n i) =
      k * (∑ i, w n i ^ 2) - b * t n ^ 2 := by
  calc
    _ = ∑ i, (k * w n i ^ 2 - if i = Fin.last n then b * t n ^ 2 else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = Fin.last n
      · subst i
        simp only [if_true, t]
        ring
      · simp only [hi, if_false]
        ring
    _ = _ := by simp [Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- The spatial coefficient differs from the common scalar only at the first endpoint. -/
theorem C_eq (n : ℕ) (k b : ℝ) :
    C n k b = (k * z n) • 1 - (b * t n ^ 2) • diagonal ![1, 0] := by
  have hc : (∑ i, w n i * k * w n i) = k * (∑ i, w n i ^ 2) := by
    simpa using weighted_column n k 0
  rw [C, coupling_inverse, inverse_coupling, hidden_spatial_diagonal]
  ext i j
  change k * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j +
    (∑ a, ((W n)ᵀ * diagonal
      (Sum.elim (fun a : Fin (n + 1) => k - if a = Fin.last n then b else 0)
        (fun _ : Fin (n + 1) => k)) : Matrix (Fin 2) (Hidden n) ℝ) i a *
        W n a j) = _
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Fintype.sum_sum_type, W, weighted_column, hc, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul]
  all_goals dsimp [z]; ring

/-- The normalized principal part is computed from the actual inverse of Z. -/
theorem effective_eq (n : ℕ) (k b : ℝ) :
    effective n k b = diagonal ![k - b * eta n, k] := by
  have hz : z n ≠ 0 := ne_of_gt (z_pos n)
  let : Invertible (z n) := invertibleOfNonzero hz
  rw [effective, Z_eq, C_eq,
    Matrix.inv_smul (1 : Matrix (Fin 2) (Fin 2) ℝ) (z n) (by simp)]
  simp only [invOf_eq_inv, inv_one, Matrix.smul_mul, Matrix.one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, eta]
  all_goals field_simp

/-- For every invertible hidden perturbation, the response has this exact expansion. -/
theorem response_expansion (n : ℕ) (k b s μ : ℝ)
    (h : IsUnit (hiddenBlock n + perturbation n k b s μ)) :
    response n k b s μ = response n k b 0 0 - s • Z n + μ • C n k b +
      remainder n k b s μ := by
  have hi := inverse_first_order (hiddenBlock n) (perturbation n k b s μ)
    (hidden_posDef n).isUnit h
  unfold response
  rw [hi]
  simp only [perturbation, zero_smul, sub_zero, add_zero, mul_zero, Z, C, remainder]
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_sub, smul_smul,
    Matrix.mul_one, Matrix.mul_assoc, add_smul, sub_smul, one_smul]
  module

private theorem norm_mul_bound {p q r : Type*} [Fintype p] [Fintype q] [Fintype r]
    (A : Matrix p q ℝ) (D : Matrix q r ℝ) {a d : ℝ}
    (hA : ‖A‖ ≤ a) (hD : ‖D‖ ≤ d) : ‖A * D‖ ≤ a * d :=
  (Matrix.linfty_opNorm_mul A D).trans
    (mul_le_mul hA hD (norm_nonneg _) ((norm_nonneg _).trans hA))

/-- In the maximum absolute row-sum norm, the remainder has two perturbation factors. -/
theorem remainder_bound (n : ℕ) (k b s μ : ℝ) :
    ‖remainder n k b s μ‖ ≤
      (‖B n‖ * ‖(hiddenBlock n)⁻¹‖ ^ 2 *
        ‖(hiddenBlock n + perturbation n k b s μ)⁻¹‖ * ‖(B n)ᵀ‖) *
          ‖perturbation n k b s μ‖ ^ 2 := by
  unfold remainder
  rw [norm_neg]
  calc
    _ ≤ ‖B n‖ * (‖(hiddenBlock n)⁻¹‖ * ‖perturbation n k b s μ‖ *
      ‖(hiddenBlock n)⁻¹‖ * ‖perturbation n k b s μ‖ *
      ‖(hiddenBlock n + perturbation n k b s μ)⁻¹‖) * ‖(B n)ᵀ‖ := by
      repeat first | exact le_rfl | apply norm_mul_bound
    _ = _ := by ring

/-- A bound M on the perturbed inverse gives a fixed quadratic remainder constant. -/
theorem remainder_bound_of_inverse_bound (n : ℕ) (k b s μ M : ℝ)
    (hM : ‖(hiddenBlock n + perturbation n k b s μ)⁻¹‖ ≤ M) :
    ‖remainder n k b s μ‖ ≤
      (‖B n‖ * ‖(hiddenBlock n)⁻¹‖ ^ 2 * M * ‖(B n)ᵀ‖) *
        ‖perturbation n k b s μ‖ ^ 2 := by
  apply (remainder_bound n k b s μ).trans
  gcongr

private theorem perturbed_inverse_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A E : Matrix ι ι ℝ) (hA : IsUnit A) (hAE : IsUnit (A + E))
    (hsmall : ‖A⁻¹‖ * ‖E‖ ≤ 1 / 2) : ‖(A + E)⁻¹‖ ≤ 2 * ‖A⁻¹‖ := by
  have hi := Matrix.inv_sub_inv (show IsUnit A ↔ IsUnit (A + E) from
    ⟨fun _ => hAE, fun _ => hA⟩)
  rw [add_sub_cancel_left] at hi
  have he : (A + E)⁻¹ = A⁻¹ - A⁻¹ * E * (A + E)⁻¹ := by
    rw [← hi]
    abel
  have hn : ‖(A + E)⁻¹‖ ≤ ‖A⁻¹‖ + ‖A⁻¹‖ * ‖E‖ * ‖(A + E)⁻¹‖ := by
    calc
      _ = ‖A⁻¹ - A⁻¹ * E * (A + E)⁻¹‖ := congrArg norm he
      _ ≤ ‖A⁻¹‖ + ‖A⁻¹ * E * (A + E)⁻¹‖ := norm_sub_le _ _
      _ ≤ _ := by
        gcongr
        exact norm_mul_bound _ _ (Matrix.linfty_opNorm_mul _ _) le_rfl
  have hs := mul_le_mul_of_nonneg_right hsmall (norm_nonneg (A + E)⁻¹)
  linarith

/-- Small invertible perturbations admit a fixed, explicit quadratic error constant. -/
theorem response_first_order (n : ℕ) (k b s μ : ℝ)
    (h : IsUnit (hiddenBlock n + perturbation n k b s μ))
    (hsmall : ‖(hiddenBlock n)⁻¹‖ * ‖perturbation n k b s μ‖ ≤ 1 / 2) :
    response n k b s μ = response n k b 0 0 - s • Z n + μ • C n k b +
      remainder n k b s μ ∧
    ‖remainder n k b s μ‖ ≤
      (2 * ‖B n‖ * ‖(hiddenBlock n)⁻¹‖ ^ 3 * ‖(B n)ᵀ‖) *
        ‖perturbation n k b s μ‖ ^ 2 := by
  refine ⟨response_expansion n k b s μ h, ?_⟩
  have hQ := perturbed_inverse_bound (hiddenBlock n) (perturbation n k b s μ)
    (hidden_posDef n).isUnit h hsmall
  convert remainder_bound_of_inverse_bound n k b s μ (2 * ‖(hiddenBlock n)⁻¹‖) hQ
    using 1 <;> ring

#print axioms C_eq
#print axioms effective_eq
#print axioms response_expansion
#print axioms remainder_bound
#print axioms remainder_bound_of_inverse_bound
#print axioms response_first_order

#print axioms inverse_first_order
#print axioms z_pos
#print axioms endpoint_formula
#print axioms Z_eq

end

end D5.S3.Arith.GoldenResource.ChainSchurResponse
