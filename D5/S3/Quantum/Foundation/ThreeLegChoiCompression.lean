/- GID: D5/S3/Quantum/Foundation/ThreeLegChoiCompression
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/ThreeLegChoiCompression
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The explicit three-string readout of the normalized GHZ projector. -/

import D5.S3.Quantum.Foundation.FiniteKrausRepresentation

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
  fun x p => if p.1 = p.2 then embedding 0 x p
    else embedding 0 x p + embedding 1 x p + embedding 2 x p

/-- Exchange position zero with the selected position. -/
def exchange (l : Fin 3) (x : Triple d) : Triple d :=
  ![x, (x.2.1, x.1, x.2.2), (x.2.2, x.2.1, x.1)] l

/-- The unnormalized diagonal GHZ vector. -/
def diagonalVector (x : Triple d) : ℂ :=
  if x.1 = x.2.1 ∧ x.2.1 = x.2.2 then 1 else 0

/-- The normalized GHZ projector, written without square roots. -/
def ghz : Matrix (Triple d) (Triple d) ℂ :=
  ((Fintype.card d : ℂ)⁻¹) • Matrix.vecMulVec
    (diagonalVector (d := d)) (star (diagonalVector (d := d)))

/-- The normalized diagonal GHZ vector in the common frame. -/
def ghzVector (x : Triple d) : ℂ :=
  ((Real.sqrt (Fintype.card d : ℝ))⁻¹ : ℂ) * diagonalVector x

/-- The same matrix map on one selected leg, with both spectators unchanged. -/
def leg (l : Fin 3) (Phi : MatrixMap d d ℂ) : MatrixMap (Triple d) (Triple d) ℂ :=
  (MatrixMap.submatrix ℂ (exchange l)) ∘ₗ
    (Phi.kron (LinearMap.id : MatrixMap (d × d) (d × d) ℂ)) ∘ₗ
    (MatrixMap.submatrix ℂ (exchange l))

/-- The actual weighted sum of the three legs of one map. -/
def averaged (alpha : Fin 3 → ℝ) (Phi : MatrixMap d d ℂ) :
    MatrixMap (Triple d) (Triple d) ℂ :=
  ∑ l, (alpha l : ℂ) • leg l Phi

private theorem word_overlap (l m : Fin 3) (p q : d × d) :
    word l p = word m q ↔
      if l = m then p = q else p.1 = p.2 ∧ p = q := by
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, e⟩
  fin_cases l <;> fin_cases m <;> simp [word, Prod.mk.injEq] <;> aesop

private theorem embedding_gram (l m : Fin 3) :
    (embedding (d := d) l).conjTranspose * embedding m =
      if l = m then 1 else diagonalCoordinates := by
  ext p q
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, embedding,
    star_ite, star_one, star_zero, ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [word_overlap]
  by_cases h : l = m
  · simp [h, Matrix.one_apply, eq_comm]
  · simp only [h, ↓reduceIte, diagonalCoordinates, Matrix.diagonal_apply]
    by_cases hpq : p = q <;> simp [hpq, eq_comm]

private theorem diagonal_idempotent :
    diagonalCoordinates (d := d) * diagonalCoordinates = diagonalCoordinates := by
  ext p q
  simp [diagonalCoordinates, Matrix.diagonal_mul_diagonal]

private theorem embedding_diagonal (l : Fin 3) :
    embedding (d := d) l * diagonalCoordinates = embedding 0 * diagonalCoordinates := by
  ext x p
  simp only [diagonalCoordinates, Matrix.mul_diagonal]
  by_cases h : p.1 = p.2
  · rcases p with ⟨a, b⟩
    simp only at h
    subst b
    fin_cases l <;> simp [embedding, word]
  · simp [h]

private theorem readout_expansion :
    readout (d := d) = embedding 0 + embedding 1 + embedding 2 -
      (2 : ℂ) • (embedding 0 * diagonalCoordinates) := by
  ext x ⟨a, b⟩
  by_cases h : a = b
  · subst b
    simp [readout, embedding, word, diagonalCoordinates, Matrix.mul_diagonal]
    ring
  · simp [readout, h, diagonalCoordinates, Matrix.mul_diagonal]

private theorem readout_embedding (l : Fin 3) :
    (readout (d := d)).conjTranspose * embedding l = 1 := by
  rw [readout_expansion]
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_assoc]
  have hdiag : (diagonalCoordinates (d := d)).conjTranspose = diagonalCoordinates := by
    ext p q
    simp [diagonalCoordinates, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  rw [hdiag]
  simp only [embedding_gram]
  fin_cases l <;> simp [diagonal_idempotent] <;> module

private theorem readout_gram :
    (readout (d := d)).conjTranspose * readout =
      (3 : ℂ) • (1 : Matrix (d × d) (d × d) ℂ) - (2 : ℂ) • diagonalCoordinates := by
  conv_lhs => rhs; rw [readout_expansion]
  rw [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_add,
    Matrix.mul_smul, ← Matrix.mul_assoc]
  simp only [readout_embedding, Matrix.one_mul]
  module

private theorem readout_gram_diagonal :
    (readout (d := d)).conjTranspose * readout =
      Matrix.diagonal (fun p => if p.1 = p.2 then (1 : ℂ) else 3) := by
  rw [readout_gram]
  ext p q
  by_cases h : p = q <;>
    simp [h, diagonalCoordinates, Matrix.diagonal_apply, Matrix.one_apply]

private theorem readout_injective : Function.Injective (readout (d := d)).mulVec := by
  have hleft : (embedding (d := d) 0).conjTranspose * readout = 1 := by
    have h := congrArg Matrix.conjTranspose (readout_embedding (d := d) 0)
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_one] using h
  intro v w h
  have hv := congrArg ((embedding (d := d) 0).conjTranspose.mulVec) h
  simpa only [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec] using hv

private theorem readout_bound :
    ((3 : ℂ) • (1 : Matrix (d × d) (d × d) ℂ) -
      (readout (d := d)).conjTranspose * readout).PosSemidef := by
  rw [readout_gram]
  have heq : (3 : ℂ) • (1 : Matrix (d × d) (d × d) ℂ) -
      ((3 : ℂ) • 1 - (2 : ℂ) • diagonalCoordinates) =
      Matrix.diagonal (fun p => if p.1 = p.2 then (2 : ℂ) else 0) := by
    ext p q
    by_cases h : p = q <;>
      simp [h, diagonalCoordinates, Matrix.diagonal_apply, Matrix.one_apply]
  rw [heq, Matrix.posSemidef_diagonal_iff]
  intro p
  split_ifs <;> positivity

private theorem ghz_positive : (ghz (d := d)).PosSemidef := by
  exact (Matrix.posSemidef_vecMulVec_self_star diagonalVector).smul (by positivity)

private theorem ghz_trace [Nonempty d] : Matrix.trace (ghz (d := d)) = 1 := by
  have hn : (Fintype.card d : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [Matrix.trace, ghz, diagonalVector, Matrix.vecMulVec, Finset.sum_prod_type,
    mul_inv_cancel₀ hn]

private theorem ghz_projector : ghz (d := d) =
    Matrix.vecMulVec (ghzVector (d := d)) (star (ghzVector (d := d))) := by
  have hs : ((Real.sqrt (Fintype.card d : ℝ) : ℂ)) ^ 2 = (Fintype.card d : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card d))
  have hc : (((Real.sqrt (Fintype.card d : ℝ))⁻¹ : ℂ)) *
      star (((Real.sqrt (Fintype.card d : ℝ))⁻¹ : ℂ)) = (Fintype.card d : ℂ)⁻¹ := by
    simp only [Complex.ofReal_inv, star_inv, Complex.star_def, Complex.conj_ofReal]
    rw [← mul_inv, ← pow_two, hs]
  ext x y
  simp only [ghz, ghzVector, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply, Pi.star_apply, star_mul]
  rw [show (((Real.sqrt (Fintype.card d : ℝ))⁻¹ : ℂ)) * diagonalVector x *
      (star (((Real.sqrt (Fintype.card d : ℝ))⁻¹ : ℂ)) * star (diagonalVector y)) =
      ((((Real.sqrt (Fintype.card d : ℝ))⁻¹ : ℂ)) *
        star (((Real.sqrt (Fintype.card d : ℝ))⁻¹ : ℂ))) *
        (diagonalVector x * star (diagonalVector y)) by ring]
  rw [hc]

private theorem exchange_involutive (l : Fin 3) :
    Function.Involutive (exchange (d := d) l) := by
  intro x
  fin_cases l <;> rfl

private theorem exchange_word (l : Fin 3) (p : d × d) :
    exchange l (word (d := d) l p) = word 0 p := by
  fin_cases l <;> rfl

private theorem ghz_exchange (l : Fin 3) :
    (ghz (d := d)).submatrix (exchange l) (exchange l) = ghz := by
  ext ⟨a, b, c⟩ ⟨e, f, g⟩
  fin_cases l <;> simp [exchange, ghz, diagonalVector, Matrix.vecMulVec,
    Matrix.submatrix_apply, and_comm, and_left_comm, and_assoc] <;>
    congr 1 <;> split_ifs <;> simp_all

private theorem first_ghz :
    ∀ (Phi : MatrixMap d d ℂ),
    (Phi.kron (LinearMap.id : MatrixMap (d × d) (d × d) ℂ)) ghz =
      (Fintype.card d : ℂ)⁻¹ •
        (embedding 0 * Phi.choi_matrix * (embedding 0).conjTranspose) := by
  intro Phi
  ext ⟨a, b, c⟩ ⟨e, f, g⟩
  simp [MatrixMap.kron_def, ghz, diagonalVector, Matrix.vecMulVec,
    Matrix.mul_apply, Matrix.conjTranspose_apply, embedding, word,
    MatrixMap.choi_matrix, Matrix.single, Finset.sum_prod_type, ite_and]

private theorem embedding_reindex (l : Fin 3) (J : Matrix (d × d) (d × d) ℂ) :
    (embedding 0 * J * (embedding 0).conjTranspose).submatrix
      (exchange l) (exchange l) = embedding l * J * (embedding l).conjTranspose := by
  ext x y
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  congr 1
  funext p
  congr 1
  · congr 1
    funext q
    congr 1
    simp only [embedding]
    have hx : exchange l x = word 0 q ↔ x = word l q := by
      constructor
      · intro h
        have := congrArg (exchange l) h
        rw [exchange_involutive] at this
        simpa only [← exchange_word l q, exchange_involutive] using this
      · rintro rfl
        exact exchange_word l q
    rw [hx]
  · simp only [embedding, star_ite, star_one, star_zero]
    have hy : exchange l y = word 0 p ↔ y = word l p := by
      constructor
      · intro h
        have := congrArg (exchange l) h
        rw [exchange_involutive] at this
        simpa only [← exchange_word l p, exchange_involutive] using this
      · rintro rfl
        exact exchange_word l p
    rw [hy]

private theorem leg_ghz (l : Fin 3) (Phi : MatrixMap d d ℂ) :
    leg l Phi ghz = (Fintype.card d : ℂ)⁻¹ •
      (embedding l * Phi.choi_matrix * (embedding l).conjTranspose) := by
  change ((Phi.kron LinearMap.id)
    ((ghz (d := d)).submatrix (exchange l) (exchange l))).submatrix
    (exchange l) (exchange l) = _
  rw [ghz_exchange, first_ghz, Matrix.submatrix_smul, embedding_reindex]

/-- Each leg of an arbitrary complex-linear map has the same exact Choi compression.
Hermiticity preservation and positivity of the map are unnecessary. -/
private theorem three_leg_choi_compression (Phi : MatrixMap d d ℂ) (alpha : Fin 3 → ℝ)
    (halpha : ∑ l, alpha l = 1) :
    (readout (d := d)).conjTranspose * averaged alpha Phi ghz * readout =
      (Fintype.card d : ℂ)⁻¹ • Phi.choi_matrix := by
  have hone (l : Fin 3) :
      readout.conjTranspose * leg l Phi ghz * readout =
        (Fintype.card d : ℂ)⁻¹ • Phi.choi_matrix := by
    rw [leg_ghz, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, readout_embedding,
      Matrix.one_mul, Matrix.mul_assoc]
    have hright : (embedding (d := d) l).conjTranspose * readout = 1 := by
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
    ghz (d := d) = Matrix.vecMulVec ghzVector (star ghzVector) ∧
    (ghz (d := d)).PosSemidef ∧ Matrix.trace (ghz (d := d)) = 1 ∧
    readout.conjTranspose * averaged alpha Phi ghz * readout =
      (Fintype.card d : ℂ)⁻¹ • Phi.choi_matrix ∧
    (readout (d := d)).conjTranspose * readout =
      Matrix.diagonal (fun p => if p.1 = p.2 then (1 : ℂ) else 3) ∧
    Function.Injective (readout (d := d)).mulVec ∧
    ((3 : ℂ) • (1 : Matrix (d × d) (d × d) ℂ) -
      (readout (d := d)).conjTranspose * readout).PosSemidef ∧
    ((averaged alpha Phi ghz).PosSemidef → Phi.IsCompletelyPositive) := by
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
