/- GID: D5/S3/Quantum/Foundation/ThreeLegChoiCompression
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/ThreeLegChoiCompression
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The explicit three-string readout of the normalized GHZ projector. -/

import D5.S3.Quantum.Foundation.FiniteKrausRepresentation

/-! # The explicit three-leg Choi compression

The common frame fixes the GHZ dyad and three-string readout independently of the map.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Foundation.ThreeLegChoiCompression

open FiniteKrausChannel.PhyslibLeaf
open scoped BigOperators Matrix ComplexOrder MatrixOrder

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Right-associated computational coordinates for three copies. -/
abbrev Triple (d : Type*) := d × (d × d)

/-- Put the output coordinate in the selected position and repeat the input coordinate. -/
def word (l : Fin 3) (p : d × d) : Triple d :=
  ![(p.1, p.2, p.2), (p.2, p.1, p.2), (p.2, p.2, p.1)] l

/-- The repeated-label embedding for an individual position. -/
def embedding (l : Fin 3) : Matrix (Triple d) (d × d) ℂ :=
  fun x p => if x = word l p then 1 else 0

/-- Projection onto diagonal matrix-unit coordinates. -/
def diagonalCoordinates : Matrix (d × d) (d × d) ℂ :=
  Matrix.diagonal fun p => if p.1 = p.2 then 1 else 0

/-- The source readout: diagonal units have one string, other units have three strings. -/
def readout : Matrix (Triple d) (d × d) ℂ :=
  fun x p => if p.1 = p.2 then (embedding (d := d)) 0 x p
    else (embedding (d := d)) 0 x p + (embedding (d := d)) 1 x p + (embedding (d := d)) 2 x p

/-- Exchange position zero with the selected position. -/
def exchange (l : Fin 3) (x : Triple d) : Triple d :=
  ![x, (x.2.1, x.1, x.2.2), (x.2.2, x.2.1, x.1)] l

/-- The unnormalized diagonal GHZ vector. -/
def diagonalVector (x : Triple d) : ℂ :=
  if x.1 = x.2.1 ∧ x.2.1 = x.2.2 then 1 else 0

/-- The normalized GHZ projector, written without square roots. -/
def ghz : Matrix (Triple d) (Triple d) ℂ :=
  ((Fintype.card d : ℂ)⁻¹) • Matrix.vecMulVec
    ((diagonalVector (d := d))) (star ((diagonalVector (d := d))))

/-- The normalized diagonal GHZ vector in the common frame. -/
def ghzVector (x : Triple d) : ℂ :=
  ((Real.sqrt (Fintype.card d : ℝ))⁻¹ : ℂ) * (diagonalVector (d := d)) x

/-- The same matrix map on one selected leg, with both spectators unchanged. -/
def leg (l : Fin 3) (Phi : MatrixMap d d ℂ) : MatrixMap (Triple d) (Triple d) ℂ :=
  (MatrixMap.submatrix ℂ (exchange l)) ∘ₗ
    (Phi.kron (LinearMap.id : MatrixMap (d × d) (d × d) ℂ)) ∘ₗ
    (MatrixMap.submatrix ℂ (exchange l))

/-- The actual weighted sum of the three legs of one map. -/
def averaged (alpha : Fin 3 → ℝ) (Phi : MatrixMap d d ℂ) :
    MatrixMap (Triple d) (Triple d) ℂ :=
  ∑ l, (alpha l : ℂ) • leg l Phi

omit [Fintype d] [DecidableEq d] in
private theorem word_overlap (l m : Fin 3) (p q : d × d) :
    word l p = word m q ↔
      if l = m then p = q else p.1 = p.2 ∧ p = q := by
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, e⟩
  fin_cases l <;> fin_cases m <;> simp [word, Prod.mk.injEq] <;> aesop

set_option backward.isDefEq.respectTransparency false in
private theorem embedding_gram (l m : Fin 3) :
    ((embedding (d := d) l)ᴴ * embedding (d := d) m :
      Matrix (d × d) (d × d) ℂ) =
      if l = m then (1 : Matrix (d × d) (d × d) ℂ)
      else diagonalCoordinates (d := d) := by
  have hentry (p q : d × d) :
      ((embedding (d := d) l)ᴴ * embedding (d := d) m :
        Matrix (d × d) (d × d) ℂ) p q =
        if word l p = word m q then 1 else 0 := by
    change (∑ x : Triple d, star (if x = word l p then (1 : ℂ) else 0) *
      (if x = word m q then 1 else 0)) = _
    simp only [apply_ite (star : ℂ → ℂ), star_one, star_zero,
      ite_mul, one_mul, zero_mul]
    exact Fintype.sum_ite_eq' (word l p) _
  by_cases h : l = m
  · subst m
    simp only [↓reduceIte]
    apply Matrix.ext
    intro p q
    simpa only [word_overlap, ↓reduceIte, Matrix.one_apply] using hentry p q
  · simp only [h, ↓reduceIte]
    apply Matrix.ext
    intro p q
    by_cases hpq : p = q <;>
      simpa [word_overlap, h, hpq, diagonalCoordinates, Matrix.diagonal_apply] using hentry p q

private theorem diagonal_idempotent :
    (diagonalCoordinates (d := d)) * (diagonalCoordinates (d := d)) = (diagonalCoordinates (d := d)) := by
  rw [diagonalCoordinates, Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  split_ifs <;> norm_num

private theorem readout_expansion :
    (readout (d := d)) = (embedding (d := d)) 0 + (embedding (d := d)) 1 + (embedding (d := d)) 2 -
      (2 : ℂ) • ((embedding (d := d)) 0 * (diagonalCoordinates (d := d))) := by
  ext x ⟨a, b⟩
  by_cases h : a = b
  · subst b
    simp [readout, embedding, word, diagonalCoordinates, Matrix.mul_diagonal]
    split_ifs <;> simp_all <;> norm_num
  · simp [readout, h, diagonalCoordinates, Matrix.mul_diagonal]

private theorem readout_embedding (l : Fin 3) :
    (readout (d := d))ᴴ * (embedding (d := d)) l = 1 := by
  rw [readout_expansion]
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_assoc]
  have hdiag : ((diagonalCoordinates (d := d)))ᴴ = (diagonalCoordinates (d := d)) := by
    ext p q
    by_cases hpq : p = q <;>
      simp [diagonalCoordinates, Matrix.conjTranspose_apply, hpq, apply_ite (starRingEnd ℂ), eq_comm]
  rw [hdiag]
  simp only [embedding_gram]
  fin_cases l <;> simp [diagonal_idempotent] <;> module

private theorem readout_gram :
    (readout (d := d))ᴴ * (readout (d := d)) =
      (3 : ℂ) • (1 : Matrix (d × d) (d × d) ℂ) - (2 : ℂ) • (diagonalCoordinates (d := d)) := by
  conv_lhs => rhs; rw [readout_expansion]
  rw [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_add,
    Matrix.mul_smul, ← Matrix.mul_assoc]
  simp only [readout_embedding, Matrix.one_mul]
  module

private theorem readout_gram_diagonal :
    (readout (d := d))ᴴ * (readout (d := d)) =
      Matrix.diagonal (fun p => if p.1 = p.2 then (1 : ℂ) else 3) := by
  rw [readout_gram]
  ext p q
  by_cases h : p = q <;>
    simp [h, diagonalCoordinates, Matrix.diagonal_apply, Matrix.one_apply] <;>
      (try split_ifs) <;> norm_num

private theorem readout_injective : Function.Injective (readout (d := d)).mulVec := by
  have hleft : ((embedding (d := d)) 0)ᴴ * (readout (d := d)) = 1 := by
    have h := congrArg Matrix.conjTranspose (readout_embedding (d := d) 0)
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_one] using h
  intro v w h
  have hv := congrArg (((embedding (d := d)) 0)ᴴ.mulVec) h
  simpa only [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec] using hv

private theorem readout_bound :
    ((3 : ℂ) • (1 : Matrix (d × d) (d × d) ℂ) -
      (readout (d := d))ᴴ * (readout (d := d))).PosSemidef := by
  rw [readout_gram]
  have heq : (3 : ℂ) • (1 : Matrix (d × d) (d × d) ℂ) -
      ((3 : ℂ) • 1 - (2 : ℂ) • (diagonalCoordinates (d := d))) =
      Matrix.diagonal (fun p => if p.1 = p.2 then (2 : ℂ) else 0) := by
    ext p q
    by_cases h : p = q <;>
      simp [h, diagonalCoordinates, Matrix.diagonal_apply, Matrix.one_apply]
  rw [heq, Matrix.posSemidef_diagonal_iff]
  intro p
  split_ifs <;> positivity

private theorem ghz_positive : ((ghz (d := d))).PosSemidef := by
  exact (Matrix.posSemidef_vecMulVec_self_star (diagonalVector (d := d))).smul (by positivity)

private theorem ghz_trace [Nonempty d] : Matrix.trace ((ghz (d := d))) = 1 := by
  have hn : (Fintype.card d : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [Matrix.trace, ghz, diagonalVector, Matrix.vecMulVec, Fintype.sum_prod_type,
    ite_and, hn]

private theorem ghz_projector : (ghz (d := d)) =
    Matrix.vecMulVec ((ghzVector (d := d))) (star ((ghzVector (d := d)))) := by
  have hs : ((Real.sqrt (Fintype.card d : ℝ) : ℂ)) ^ 2 = (Fintype.card d : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card d))
  have hc : (((Real.sqrt (Fintype.card d : ℝ))⁻¹ : ℂ)) *
      star (((Real.sqrt (Fintype.card d : ℝ))⁻¹ : ℂ)) = (Fintype.card d : ℂ)⁻¹ := by
    simp only [Complex.star_def, map_inv₀, Complex.conj_ofReal]
    rw [← mul_inv, ← pow_two, hs]
  ext x y
  simp only [ghz, ghzVector, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply, Pi.star_apply, star_mul]
  rw [← hc]
  ring

omit [Fintype d] [DecidableEq d] in
private theorem exchange_involutive (l : Fin 3) :
    Function.Involutive (exchange (d := d) l) := by
  intro x
  fin_cases l <;> rfl

omit [Fintype d] [DecidableEq d] in
private theorem exchange_word (l : Fin 3) (p : d × d) :
    exchange l (word (d := d) l p) = word 0 p := by
  fin_cases l <;> rfl

omit [Fintype d] in
private theorem diagonalVector_exchange (l : Fin 3) (x : Triple d) :
    diagonalVector (exchange l x) = diagonalVector x := by
  rcases x with ⟨a, b, c⟩
  fin_cases l
  · rfl
  · simp only [exchange, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
      Prod.fst, Prod.snd, diagonalVector]
    congr 1
    exact propext (by aesop)
  · simp only [exchange, Fin.isValue, Matrix.cons_val_two, Matrix.cons_val_one,
      Matrix.cons_val_zero, Prod.fst, Prod.snd, diagonalVector]
    congr 1
    exact propext (by aesop)

private theorem ghz_exchange (l : Fin 3) :
    (ghz (d := d)).submatrix (exchange l) (exchange l) = ghz := by
  ext x y
  simp [ghz, Matrix.vecMulVec, Matrix.submatrix_apply, diagonalVector_exchange]

private theorem first_ghz :
    ∀ (Phi : MatrixMap d d ℂ),
    (Phi.kron (LinearMap.id : MatrixMap (d × d) (d × d) ℂ)) (ghz (d := d)) =
      (Fintype.card d : ℂ)⁻¹ •
        ((embedding (d := d)) 0 * Phi.choi_matrix * ((embedding (d := d)) 0)ᴴ) := by
  intro Phi
  ext ⟨a, b, c⟩ ⟨e, f, g⟩
  by_cases hbc : b = c <;> by_cases hfg : f = g <;>
    simp [hbc, hfg, eq_comm, apply_ite (starRingEnd ℂ), mul_comm,
    MatrixMap.kron_def, ghz, diagonalVector, Matrix.vecMulVec,
    Matrix.mul_apply, Matrix.conjTranspose_apply, embedding, word,
    MatrixMap.choi_matrix, Matrix.single, Fintype.sum_prod_type, ite_and]

omit [Fintype d] in
private theorem embedding_exchange (l : Fin 3) (x : Triple d) (p : d × d) :
    embedding (d := d) 0 (exchange l x) p = embedding l x p := by
  have hx : exchange l x = word 0 p ↔ x = word l p := by
    constructor
    · intro h
      apply (exchange_involutive l).injective
      simpa only [exchange_word] using h
    · rintro rfl
      exact exchange_word l p
  simp only [embedding, hx]

private theorem embedding_reindex (l : Fin 3) (J : Matrix (d × d) (d × d) ℂ) :
    (embedding (d := d) 0 * J * (embedding (d := d) 0)ᴴ).submatrix
      (exchange l) (exchange l) = embedding (d := d) l * J * (embedding (d := d) l)ᴴ := by
  ext x y
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    embedding_exchange]

private theorem leg_ghz (l : Fin 3) (Phi : MatrixMap d d ℂ) :
    leg l Phi (ghz (d := d)) = (Fintype.card d : ℂ)⁻¹ •
      ((embedding (d := d)) l * Phi.choi_matrix * ((embedding (d := d)) l)ᴴ) := by
  change ((Phi.kron LinearMap.id)
    (((ghz (d := d))).submatrix (exchange l) (exchange l))).submatrix
    (exchange l) (exchange l) = _
  rw [ghz_exchange, first_ghz]
  change (Fintype.card d : ℂ)⁻¹ •
    ((embedding (d := d) 0 * Phi.choi_matrix * (embedding (d := d) 0)ᴴ).submatrix
      (exchange l) (exchange l)) = _
  rw [embedding_reindex]

/-- Each leg of an arbitrary complex-linear map has the same exact Choi compression.
Hermiticity preservation and positivity of the map are unnecessary. -/
private theorem three_leg_choi_compression (Phi : MatrixMap d d ℂ) (alpha : Fin 3 → ℝ)
    (halpha : ∑ l, alpha l = 1) :
    (readout (d := d))ᴴ * averaged alpha Phi (ghz (d := d)) * (readout (d := d)) =
      (Fintype.card d : ℂ)⁻¹ • Phi.choi_matrix := by
  have hone (l : Fin 3) :
      (readout (d := d))ᴴ * leg l Phi (ghz (d := d)) * (readout (d := d)) =
        (Fintype.card d : ℂ)⁻¹ • Phi.choi_matrix := by
    rw [leg_ghz, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, readout_embedding,
      Matrix.one_mul, Matrix.mul_assoc]
    have hright : ((embedding (d := d)) l)ᴴ * (readout (d := d)) = 1 := by
      have h := congrArg Matrix.conjTranspose (readout_embedding (d := d) l)
      simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.conjTranspose_one] using h
    rw [hright, Matrix.mul_one]
  simp only [averaged, LinearMap.sum_apply, LinearMap.smul_apply,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, hone]
  rw [← Finset.sum_smul]
  have hcast : ∑ l, (alpha l : ℂ) = 1 := by exact_mod_cast halpha
  rw [hcast, one_smul]

/-- The explicit normalized GHZ readout, with its exact Gram matrix and CP detection.
The compression holds for every complex-linear map and all real weights of sum one. -/
theorem three_leg_choi_detector [Nonempty d] (Phi : MatrixMap d d ℂ)
    (alpha : Fin 3 → ℝ) (halpha : ∑ l, alpha l = 1) :
    (ghz (d := d)) = Matrix.vecMulVec (ghzVector (d := d)) (star (ghzVector (d := d))) ∧
    ((ghz (d := d))).PosSemidef ∧ Matrix.trace ((ghz (d := d))) = 1 ∧
    (readout (d := d))ᴴ * averaged alpha Phi (ghz (d := d)) * (readout (d := d)) =
      (Fintype.card d : ℂ)⁻¹ • Phi.choi_matrix ∧
    (readout (d := d))ᴴ * (readout (d := d)) =
      Matrix.diagonal (fun p => if p.1 = p.2 then (1 : ℂ) else 3) ∧
    Function.Injective (readout (d := d)).mulVec ∧
    ((3 : ℂ) • (1 : Matrix (d × d) (d × d) ℂ) -
      (readout (d := d))ᴴ * (readout (d := d))).PosSemidef ∧
    ((averaged alpha Phi (ghz (d := d))).PosSemidef → Phi.IsCompletelyPositive) := by
  refine ⟨ghz_projector, ghz_positive, ghz_trace,
    three_leg_choi_compression Phi alpha halpha, readout_gram_diagonal,
    readout_injective, readout_bound, ?_⟩
  intro h
  apply (MatrixMap.choi_PSD_iff_CP_map Phi).mpr
  have hc := h.conjTranspose_mul_mul_same (readout (d := d))
  rw [three_leg_choi_compression Phi alpha halpha] at hc
  have hp := hc.smul (a := (Fintype.card d : ℂ)) (by positivity)
  have hn : (Fintype.card d : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simpa only [smul_smul, mul_inv_cancel₀ hn, one_smul] using hp

end D5.S3.Quantum.Foundation.ThreeLegChoiCompression
