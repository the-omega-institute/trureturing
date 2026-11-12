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


section DirectSum

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (D : I → Type*) [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]

/-- The finite direct sum, with its original componentwise algebra operations. -/
abbrev BlockAlgebra := ∀ i, Matrix (D i) (D i) ℂ

/-- The original map's input-i/output-j rectangular component. -/
def component (Phi : BlockAlgebra D →ₗ[ℂ] BlockAlgebra D) (j i : I) :
    MatrixMap (D i) (D j) ℂ :=
  (LinearMap.proj j).comp (Phi.comp (LinearMap.single ℂ _ i))

/-- Flatten an auxiliary matrix over the original algebra at a central component. -/
def matrixBlock {T : Type*} (X : Matrix T T (BlockAlgebra D)) (i : I) :
    Matrix (D i × T) (D i × T) ℂ := fun p q => X p.2 q.2 i p.1 q.1

/-- Positivity at every auxiliary size of the entrywise action of the original map.
This is a universal amplification condition, independently of the rectangular components. -/
def AmplificationPositive (Phi : BlockAlgebra D →ₗ[ℂ] BlockAlgebra D) : Prop :=
  ∀ k (X : Matrix (Fin k) (Fin k) (BlockAlgebra D)),
    (∀ i, (matrixBlock D X i).PosSemidef) →
    ∀ j, (matrixBlock D (X.map Phi) j).PosSemidef

private theorem component_reconstruction (Phi : BlockAlgebra D →ₗ[ℂ] BlockAlgebra D)
    (X : BlockAlgebra D) (j : I) : Phi X j = ∑ i, component D Phi j i (X i) := by
  have h := LinearMap.sum_single_apply X
  conv_lhs => rw [← h]
  simp [component]

private theorem kron_id_entry {a b T : Type*}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype T] [DecidableEq T] (f : MatrixMap a b ℂ)
    (X : Matrix (a × T) (a × T) ℂ) (p q : b × T) :
    (f.kron (LinearMap.id : MatrixMap T T ℂ)) X p q =
      f (fun r s => X (r, p.2) (s, q.2)) p.1 q.1 := by
  have hexp (M : Matrix a a ℂ) :
      f M = ∑ r, ∑ s, M r s • f (Matrix.single r s 1) := by
    have h : M = ∑ r, ∑ s, M r s • Matrix.single r s 1 := by
      ext r s
      simp [Matrix.single, Matrix.sum_apply, ite_and]
    conv_lhs => rw [h]
    simp only [map_sum, map_smul]
  rw [hexp, MatrixMap.kron_def]
  simp [Matrix.single, Matrix.sum_apply, ite_and, mul_comm]

private theorem amplification_components (Phi : BlockAlgebra D →ₗ[ℂ] BlockAlgebra D)
    {T : Type*} [Fintype T] [DecidableEq T]
    (X : Matrix T T (BlockAlgebra D)) (j : I) :
    matrixBlock D (X.map Phi) j =
      ∑ i, ((component D Phi j i).kron (LinearMap.id : MatrixMap T T ℂ))
        (matrixBlock D X i) := by
  ext p q
  simp only [Matrix.sum_apply, kron_id_entry, matrixBlock, Matrix.map_apply]
  exact congrFun (congrFun (component_reconstruction D Phi (X p.2 q.2) j) p.1) q.1

private theorem amplification_iff_components
    (Phi : BlockAlgebra D →ₗ[ℂ] BlockAlgebra D) :
    AmplificationPositive D Phi ↔ ∀ j i, (component D Phi j i).IsCompletelyPositive := by
  constructor
  · intro h j i k M hM
    let X : Matrix (Fin k) (Fin k) (BlockAlgebra D) :=
      fun r s => Pi.single i (fun a b => M (a, r) (b, s))
    have hX : ∀ t, (matrixBlock D X t).PosSemidef := by
      intro t
      by_cases ht : t = i
      · subst t
        simpa [matrixBlock, X] using hM
      · have hz : matrixBlock D X t = 0 := by
          ext p q
          simp [matrixBlock, X, Pi.single_eq_of_ne ht]
        rw [hz]
        exact Matrix.PosSemidef.zero
    have hj := h k X hX j
    have heq : matrixBlock D (X.map Phi) j =
        ((component D Phi j i).kron (LinearMap.id : MatrixMap (Fin k) (Fin k) ℂ)) M := by
      ext p q
      simp only [matrixBlock, Matrix.map_apply, kron_id_entry]
      rfl
    rwa [heq] at hj
  · intro h k X hX j
    rw [amplification_components]
    exact Matrix.posSemidef_sum _ (fun i _ => h j i k (hX i))

/-- The canonical C-star algebra of the same finite matrix direct sum. -/
abbrev CStarBlocks := ∀ i, CStarMatrix (D i) (D i) ℂ

/-- Coordinate transport of the original map, without any positivity assumption. -/
def canonicalLinear (Phi : BlockAlgebra D →ₗ[ℂ] BlockAlgebra D) :
    CStarBlocks D →ₗ[ℂ] CStarBlocks D where
  toFun X i := CStarMatrix.ofMatrix (Phi (fun j => CStarMatrix.ofMatrix.symm (X j)) i)
  map_add' _ _ := by ext i a b; simp
  map_smul' _ _ := by ext i a b; simp

/-- All auxiliary matrices over a finite direct sum, with all central components retained. -/
def flattenBlocks (k : ℕ) :
    CStarMatrix (Fin k) (Fin k) (CStarBlocks D) ≃⋆ₐ[ℂ]
      (∀ i, CStarMatrix (D i × Fin k) (D i × Fin k) ℂ) where
  toFun X i := CStarMatrix.ofMatrix fun p q => X p.2 q.2 i p.1 q.1
  invFun X := CStarMatrix.ofMatrix fun r s i =>
    CStarMatrix.ofMatrix fun a b => X i (a, r) (b, s)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl
  map_mul' X Y := by
    ext i p q
    change (∑ t : Fin k, (CStarMatrix.ofMatrix.symm (X p.2 t i) *
      CStarMatrix.ofMatrix.symm (Y t q.2 i))) p.1 q.1 =
      ∑ z : D i × Fin k, X p.2 z.2 i p.1 z.1 * Y z.2 q.2 i z.1 q.1
    simp only [Matrix.sum_apply, Matrix.mul_apply, CStarMatrix.ofMatrix_symm_apply,
      Fintype.sum_prod_type]
    exact Finset.sum_comm

private theorem amplification_iff_canonical
    (Phi : BlockAlgebra D →ₗ[ℂ] BlockAlgebra D) :
    AmplificationPositive D Phi ↔
      ∃ f : CompletelyPositiveMap (CStarBlocks D) (CStarBlocks D),
        f.toLinearMap = canonicalLinear D Phi := by
  have hcone (k : ℕ) (X : CStarMatrix (Fin k) (Fin k) (CStarBlocks D)) :
      0 ≤ X ↔ ∀ i, (matrixBlock D
        (fun r s i => CStarMatrix.ofMatrix.symm (X r s i)) i).PosSemidef := by
    constructor
    · intro h i
      have hf := map_nonneg (flattenBlocks D k) h
      exact Matrix.nonneg_iff_posSemidef.mp
        (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (hf i))
    · intro h
      have hf : 0 ≤ flattenBlocks D k X := by
        intro i
        exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (h i).nonneg
      exact map_nonneg (flattenBlocks D k).symm hf
  constructor
  · intro h
    refine ⟨{ toLinearMap := canonicalLinear D Phi,
      map_cstarMatrix_nonneg' := ?_ }, rfl⟩
    intro k X hX
    apply (hcone k _).mpr
    exact h k _ ((hcone k X).mp hX)
  · rintro ⟨f, hf⟩ k X hX
    let Y : CStarMatrix (Fin k) (Fin k) (CStarBlocks D) :=
      CStarMatrix.ofMatrix fun r s i => CStarMatrix.ofMatrix (X r s i)
    have hY : 0 ≤ Y := (hcone k Y).mpr hX
    have hout := (hcone k _).mp (f.map_cstarMatrix_nonneg Y hY)
    rw [hf] at hout
    exact hout


/-- Every ordered three-copy sector, with the full PSD cone in that sector. -/
abbrev TripleBlocks := ∀ i j k, Matrix (D i × (D j × D k)) (D i × (D j × D k)) ℂ

/-- The first leg sums all input-sector transitions of the original map. -/
def firstBlockLeg (Phi : BlockAlgebra D →ₗ[ℂ] BlockAlgebra D)
    (Z : TripleBlocks D) : TripleBlocks D := fun j k l =>
  ∑ i, ((component D Phi j i).kron
    (LinearMap.id : MatrixMap (D k × D l) (D k × D l) ℂ)) (Z i k l)

/-- Exchange the first and second factors, including their central labels. -/
def swapFirstSecond (Z : TripleBlocks D) : TripleBlocks D := fun i j k =>
  (Z j i k).submatrix (fun x => (x.2.1, x.1, x.2.2))
    (fun x => (x.2.1, x.1, x.2.2))

/-- Exchange the first and third factors, including their central labels. -/
def swapFirstThird (Z : TripleBlocks D) : TripleBlocks D := fun i j k =>
  (Z k j i).submatrix (fun x => (x.2.2, x.2.1, x.1))
    (fun x => (x.2.2, x.2.1, x.1))

/-- The identical original map acts in the selected position. -/
def blockLeg (l : Fin 3) (Phi : BlockAlgebra D →ₗ[ℂ] BlockAlgebra D)
    (Z : TripleBlocks D) : TripleBlocks D :=
  ![firstBlockLeg D Phi Z,
    swapFirstSecond D (firstBlockLeg D Phi (swapFirstSecond D Z)),
    swapFirstThird D (firstBlockLeg D Phi (swapFirstThird D Z))] l

/-- The original same-event weighted three-leg lift on every ordered block. -/
def blockAveraged (alpha : Fin 3 → ℝ)
    (Phi : BlockAlgebra D →ₗ[ℂ] BlockAlgebra D) (Z : TripleBlocks D) : TripleBlocks D :=
  ∑ l, (alpha l : ℂ) • blockLeg D l Phi Z

/-- The unweighted inclusion of the normalized GHZ projector in sector iii. -/
def seed (i : I) : TripleBlocks D := Pi.single i (Pi.single i (Pi.single i (ghz (d := D i))))

/-- Ordinary total matrix dimension, including all scalar summands. -/
def totalDimension : ℕ := ∑ i, Fintype.card (D i)

/-- The fixed source probe, independent of the event and the averaging weights. -/
def probe : TripleBlocks D :=
  ∑ i, ((Fintype.card (D i) : ℂ) / (totalDimension D : ℂ)) • seed D i

/-- The full ordered three-copy cone, with no separability restriction. -/
def TriplePositive (Z : TripleBlocks D) : Prop := ∀ i j k, (Z i j k).PosSemidef

private theorem seed_positive (i : I) : TriplePositive D (seed D i) := by
  intro j k l
  by_cases hji : j = i
  · subst j
    by_cases hki : k = i
    · subst k
      by_cases hli : l = i
      · subst l
        simpa [seed] using ghz_positive (d := D i)
      · simpa [seed, Pi.single_eq_of_ne hli] using
          (Matrix.PosSemidef.zero : (0 : Matrix (D i × (D i × D l)) _ ℂ).PosSemidef)
    · simpa [seed, Pi.single_eq_of_ne hki] using
        (Matrix.PosSemidef.zero : (0 : Matrix (D i × (D k × D l)) _ ℂ).PosSemidef)
  · simpa [seed, Pi.single_eq_of_ne hji] using
      (Matrix.PosSemidef.zero : (0 : Matrix (D j × (D k × D l)) _ ℂ).PosSemidef)

private theorem probe_positive : TriplePositive D (probe D) := by
  intro j k l
  change (∑ i, ((Fintype.card (D i) : ℂ) / (totalDimension D : ℂ)) •
    seed D i j k l).PosSemidef
  exact Matrix.posSemidef_sum _ (fun i _ => (seed_positive D i j k l).smul (by positivity))

private theorem totalDimension_positive [Nonempty I] [∀ i, Nonempty (D i)] :
    0 < totalDimension D := by
  exact Finset.sum_pos (fun i _ => Fintype.card_pos) Finset.univ_nonempty

private theorem firstBlockLeg_positive
    (Phi : BlockAlgebra D →ₗ[ℂ] BlockAlgebra D)
    (h : ∀ j i, (component D Phi j i).IsCompletelyPositive)
    (Z : TripleBlocks D) (hZ : TriplePositive D Z) :
    TriplePositive D (firstBlockLeg D Phi Z) := by
  intro j k l
  exact Matrix.posSemidef_sum _
    (fun i _ => (h j i).of_Fintype (D k × D l) (hZ i k l))

private theorem blockLeg_positive
    (Phi : BlockAlgebra D →ₗ[ℂ] BlockAlgebra D)
    (h : ∀ j i, (component D Phi j i).IsCompletelyPositive)
    (l : Fin 3) (Z : TripleBlocks D) (hZ : TriplePositive D Z) :
    TriplePositive D (blockLeg D l Phi Z) := by
  have h12 : TriplePositive D (swapFirstSecond D Z) :=
    fun i j k => (hZ j i k).submatrix _
  have h13 : TriplePositive D (swapFirstThird D Z) :=
    fun i j k => (hZ k j i).submatrix _
  fin_cases l
  · exact firstBlockLeg_positive D Phi h Z hZ
  · exact fun i j k => (firstBlockLeg_positive D Phi h _ h12 j i k).submatrix _
  · exact fun i j k => (firstBlockLeg_positive D Phi h _ h13 k j i).submatrix _

private theorem blockAveraged_positive
    (Phi : BlockAlgebra D →ₗ[ℂ] BlockAlgebra D)
    (h : ∀ j i, (component D Phi j i).IsCompletelyPositive)
    (alpha : Fin 3 → ℝ) (ha : ∀ l, 0 ≤ alpha l)
    (Z : TripleBlocks D) (hZ : TriplePositive D Z) :
    TriplePositive D (blockAveraged D alpha Phi Z) := by
  intro i j k
  change (∑ l, (alpha l : ℂ) • blockLeg D l Phi Z i j k).PosSemidef
  exact Matrix.posSemidef_sum _ (fun l _ =>
    (blockLeg_positive D Phi h l Z hZ i j k).smul (by exact_mod_cast ha l))


private theorem probe_diagonal (i : I) :
    probe D i i i = ((Fintype.card (D i) : ℂ) / (totalDimension D : ℂ)) • ghz := by
  simp [probe, seed, Finset.sum_apply, Pi.smul_apply]

private theorem probe_other (i j k : I) (h : ¬ (i = j ∧ j = k)) :
    probe D i j k = 0 := by
  change (∑ a, ((Fintype.card (D a) : ℂ) / (totalDimension D : ℂ)) •
    seed D a i j k) = 0
  apply Finset.sum_eq_zero
  intro a _
  by_cases hi : i = a
  · subst i
    by_cases hj : j = a
    · subst j
      have hk : k ≠ a := by aesop
      simp [seed, Pi.single_eq_of_ne hk]
    · simp [seed, Pi.single_eq_of_ne hj]
  · simp [seed, Pi.single_eq_of_ne hi]

private theorem probe_trace [Nonempty I] [∀ i, Nonempty (D i)] :
    (∑ i, ∑ j, ∑ k, Matrix.trace (probe D i j k)) = 1 := by
  have hsector (i : I) : (∑ j, ∑ k, Matrix.trace (probe D i j k)) =
      (Fintype.card (D i) : ℂ) / (totalDimension D : ℂ) := by
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single i]
      · rw [probe_diagonal, Matrix.trace_smul, ghz_trace, smul_eq_mul, mul_one]
      · intro k _ hki
        rw [probe_other D i i k (by aesop), Matrix.trace_zero]
      · simp
    · intro j _ hji
      apply Finset.sum_eq_zero
      intro k _
      rw [probe_other D i j k (by aesop), Matrix.trace_zero]
    · simp
  simp_rw [hsector]
  have hn : (totalDimension D : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (totalDimension_positive D))
  rw [← Finset.sum_div, ← Nat.cast_sum]
  exact div_self hn

private theorem probe_swap12 : swapFirstSecond D (probe D) = probe D := by
  funext i j k
  by_cases h : i = j ∧ j = k
  · rcases h with ⟨rfl, rfl⟩
    simp only [swapFirstSecond, probe_diagonal, Matrix.submatrix_smul]
    congr 1
    exact ghz_exchange (d := D k) 1
  · have h' : ¬ (j = i ∧ i = k) := by aesop
    simp [swapFirstSecond, probe_other D i j k h, probe_other D j i k h']

private theorem probe_swap13 : swapFirstThird D (probe D) = probe D := by
  funext i j k
  by_cases h : i = j ∧ j = k
  · rcases h with ⟨rfl, rfl⟩
    simp only [swapFirstThird, probe_diagonal, Matrix.submatrix_smul]
    congr 1
    exact ghz_exchange (d := D k) 2
  · have h' : ¬ (k = j ∧ j = i) := by aesop
    simp [swapFirstThird, probe_other D i j k h, probe_other D k j i h']

private theorem first_probe_same (Phi : BlockAlgebra D →ₗ[ℂ] BlockAlgebra D)
    (j i : I) :
    firstBlockLeg D Phi (probe D) j i i =
      ((Fintype.card (D i) : ℂ) / (totalDimension D : ℂ)) •
        (((component D Phi j i).kron
          (LinearMap.id : MatrixMap (D i × D i) (D i × D i) ℂ)) ghz) := by
  rw [firstBlockLeg, Finset.sum_eq_single i]
  · rw [probe_diagonal, map_smul]
  · intro a _ hai
    rw [probe_other D a i i (by aesop), map_zero]
  · simp

private theorem first_probe_different (Phi : BlockAlgebra D →ₗ[ℂ] BlockAlgebra D)
    (j k l : I) (hkl : k ≠ l) : firstBlockLeg D Phi (probe D) j k l = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  rw [probe_other D i k l (by aesop), map_zero]

/-- The rectangular repeated-label isometry, in output-first/input-second order. -/
def rectangularEmbedding {a b : Type*} [DecidableEq a] [DecidableEq b] :
    Matrix (b × (a × a)) (b × a) ℂ :=
  fun x p => if x = (p.1, p.2, p.2) then 1 else 0

private theorem rectangularEmbedding_isometry {a b : Type*}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] :
    (rectangularEmbedding (a := a) (b := b))ᴴ * rectangularEmbedding = 1 := by
  ext p q
  change (∑ x : b × (a × a), star (if x = (p.1, p.2, p.2) then (1 : ℂ) else 0) *
    (if x = (q.1, q.2, q.2) then 1 else 0)) = _
  simp [apply_ite (starRingEnd ℂ), Matrix.one_apply, Prod.mk.injEq, ite_and]

private theorem rectangular_ghz {a b : Type*}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (Phi : MatrixMap a b ℂ) :
    (Phi.kron (LinearMap.id : MatrixMap (a × a) (a × a) ℂ)) ghz =
      (Fintype.card a : ℂ)⁻¹ •
        (rectangularEmbedding * Phi.choi_matrix * rectangularEmbeddingᴴ) := by
  ext ⟨c, d, e⟩ ⟨f, g, h⟩
  by_cases hde : d = e <;> by_cases hgh : g = h <;>
    simp [hde, hgh, eq_comm, apply_ite (starRingEnd ℂ), mul_comm,
      MatrixMap.kron_def, ghz, diagonalVector, Matrix.vecMulVec,
      Matrix.mul_apply, Matrix.conjTranspose_apply, rectangularEmbedding,
      MatrixMap.choi_matrix, Matrix.single, Fintype.sum_prod_type, ite_and]

private theorem probe_diagonal_output (Phi : BlockAlgebra D →ₗ[ℂ] BlockAlgebra D)
    (alpha : Fin 3 → ℝ) (i : I) :
    blockAveraged D alpha Phi (probe D) i i i =
      ((Fintype.card (D i) : ℂ) / (totalDimension D : ℂ)) •
        averaged alpha (component D Phi i i) ghz := by
  simp only [blockAveraged, averaged, Fin.sum_univ_succ, Finset.sum_apply, Pi.smul_apply,
    LinearMap.add_apply, LinearMap.smul_apply]
  simp only [blockLeg, leg, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, probe_swap12, probe_swap13, first_probe_same,
    swapFirstSecond, swapFirstThird, Matrix.submatrix_smul]
  change _ = _
  module

private theorem probe_offsector [∀ i, Nonempty (D i)] (Phi : BlockAlgebra D →ₗ[ℂ] BlockAlgebra D)
    (alpha : Fin 3 → ℝ) (j i : I) (hji : j ≠ i) :
    blockAveraged D alpha Phi (probe D) j i i =
      ((alpha 0 : ℂ) / (totalDimension D : ℂ)) •
        (rectangularEmbedding * (component D Phi j i).choi_matrix *
          rectangularEmbeddingᴴ) := by
  have hn : (Fintype.card (D i) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [blockAveraged, Fin.sum_univ_succ, Finset.sum_apply, Pi.smul_apply,
    blockLeg, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, probe_swap12, probe_swap13, swapFirstSecond, swapFirstThird,
    first_probe_different D Phi i j i hji,
    first_probe_different D Phi i i j hji.symm, Matrix.submatrix_zero,
    smul_zero, add_zero, zero_add, first_probe_same, rectangular_ghz, smul_smul]
  congr 1
  field_simp


/-- A chosen off-diagonal sector, permuted into output-first Choi coordinates. -/
def offsectorOutput (Z : TripleBlocks D) (l : Fin 3) (j i : I) :
    Matrix (D j × (D i × D i)) (D j × (D i × D i)) ℂ :=
  ![Z j i i,
    (Z i j i).submatrix (fun x => (x.2.1, x.1, x.2.2))
      (fun x => (x.2.1, x.1, x.2.2)),
    (Z i i j).submatrix (fun x => (x.2.2, x.2.1, x.1))
      (fun x => (x.2.2, x.2.1, x.1))] l

private theorem offsectorOutput_positive (Z : TripleBlocks D)
    (hZ : TriplePositive D Z) (l : Fin 3) (j i : I) :
    (offsectorOutput D Z l j i).PosSemidef := by
  fin_cases l
  · exact hZ j i i
  · exact (hZ i j i).submatrix _
  · exact (hZ i i j).submatrix _

private theorem probe_all_offsectors [∀ i, Nonempty (D i)]
    (Phi : BlockAlgebra D →ₗ[ℂ] BlockAlgebra D)
    (alpha : Fin 3 → ℝ) (l : Fin 3) (j i : I) (hji : j ≠ i) :
    offsectorOutput D (blockAveraged D alpha Phi (probe D)) l j i =
      ((alpha l : ℂ) / (totalDimension D : ℂ)) •
        (rectangularEmbedding * (component D Phi j i).choi_matrix *
          rectangularEmbeddingᴴ) := by
  have hn : (Fintype.card (D i) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  fin_cases l
  · exact probe_offsector D Phi alpha j i hji
  · simp only [offsectorOutput, blockAveraged, Fin.sum_univ_succ,
      Finset.sum_apply, Pi.smul_apply, blockLeg, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      probe_swap12, probe_swap13, swapFirstSecond, swapFirstThird,
      first_probe_different D Phi i j i hji,
      first_probe_different D Phi i i j hji.symm,
      Matrix.submatrix_zero, smul_zero, add_zero, zero_add,
      first_probe_same, Matrix.submatrix_smul, Matrix.submatrix_submatrix]
    change (alpha 1 : ℂ) • (((Fintype.card (D i) : ℂ) / (totalDimension D : ℂ)) •
      (((component D Phi j i).kron LinearMap.id) ghz)) = _
    rw [rectangular_ghz, smul_smul, smul_smul]
    congr 1
    field_simp
  · simp only [offsectorOutput, blockAveraged, Fin.sum_univ_succ,
      Finset.sum_apply, Pi.smul_apply, blockLeg, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      probe_swap12, probe_swap13, swapFirstSecond, swapFirstThird,
      first_probe_different D Phi i i j hji.symm,
      first_probe_different D Phi i j i hji,
      Matrix.submatrix_zero, smul_zero, add_zero, zero_add,
      first_probe_same, Matrix.submatrix_smul, Matrix.submatrix_submatrix]
    change (alpha 2 : ℂ) • (((Fintype.card (D i) : ℂ) / (totalDimension D : ℂ)) •
      (((component D Phi j i).kron LinearMap.id) ghz)) = _
    rw [rectangular_ghz, smul_smul, smul_smul]
    congr 1
    field_simp

private theorem probe_detects_components [Nonempty I] [∀ i, Nonempty (D i)]
    (Phi : BlockAlgebra D →ₗ[ℂ] BlockAlgebra D)
    (alpha : Fin 3 → ℝ) (ha : ∀ l, 0 ≤ alpha l) (hsum : ∑ l, alpha l = 1)
    (hprobe : TriplePositive D (blockAveraged D alpha Phi (probe D))) :
    ∀ j i, (component D Phi j i).IsCompletelyPositive := by
  have htotal : 0 < (totalDimension D : ℝ) := by
    exact_mod_cast totalDimension_positive D
  obtain ⟨l, hl⟩ : ∃ l, 0 < alpha l := by
    by_contra h
    have hz : ∀ l, alpha l = 0 := by
      intro l
      have := ha l
      have := not_exists.mp h l
      linarith
    simp [hz] at hsum
  intro j i
  by_cases hji : j = i
  · subst j
    have hd := hprobe i i i
    rw [probe_diagonal_output] at hd
    have hc := hd.conjTranspose_mul_mul_same (readout (d := D i))
    rw [Matrix.mul_smul, Matrix.smul_mul, three_leg_choi_compression _ alpha hsum] at hc
    have hdim : (Fintype.card (D i) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have heq : ((Fintype.card (D i) : ℂ) / (totalDimension D : ℂ)) *
        (Fintype.card (D i) : ℂ)⁻¹ = (totalDimension D : ℂ)⁻¹ := by field_simp
    rw [smul_smul, heq] at hc
    have hout := hc.smul (a := (totalDimension D : ℂ)) (by positivity)
    have hn : (totalDimension D : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt htotal)
    apply (MatrixMap.choi_PSD_iff_CP_map _).mpr
    simpa only [smul_smul, mul_inv_cancel₀ hn, one_smul] using hout
  · have ho := offsectorOutput_positive D _ hprobe l j i
    rw [probe_all_offsectors D Phi alpha l j i hji] at ho
    have hc := ho.conjTranspose_mul_mul_same rectangularEmbedding
    have heq : (rectangularEmbedding (a := D i) (b := D j))ᴴ *
        (((alpha l : ℂ) / (totalDimension D : ℂ)) •
          (rectangularEmbedding * (component D Phi j i).choi_matrix *
            rectangularEmbeddingᴴ)) * rectangularEmbedding =
        ((alpha l : ℂ) / (totalDimension D : ℂ)) • (component D Phi j i).choi_matrix := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      simp only [← Matrix.mul_assoc, rectangularEmbedding_isometry, Matrix.one_mul]
      rw [Matrix.mul_assoc, rectangularEmbedding_isometry, Matrix.mul_one]
    rw [heq] at hc
    have hscale : 0 < alpha l / (totalDimension D : ℝ) := div_pos hl htotal
    have hout := hc.smul (a := ((alpha l / (totalDimension D : ℝ))⁻¹ : ℂ)) (by positivity)
    have hn : ((alpha l : ℂ) / (totalDimension D : ℂ)) ≠ 0 := by
      exact_mod_cast ne_of_gt hscale
    apply (MatrixMap.choi_PSD_iff_CP_map _).mpr
    simpa only [Complex.ofReal_inv, Complex.ofReal_div, Complex.ofReal_natCast,
      smul_smul, inv_mul_cancel₀ hn, one_smul] using hout

/-- The fixed trace-one probe detects canonical CP of the original finite direct-sum map,
which is equivalent to positivity of the actual same-map lift on the entire three-copy cone.
All ordered sectors and all nonnegative normalized weight triples are included. -/
theorem direct_sum_three_leg_detector [Nonempty I] [∀ i, Nonempty (D i)]
    (Phi : BlockAlgebra D →ₗ[ℂ] BlockAlgebra D)
    (alpha : Fin 3 → ℝ) (ha : ∀ l, 0 ≤ alpha l) (hsum : ∑ l, alpha l = 1) :
    TriplePositive D (probe D) ∧
    (∑ i, ∑ j, ∑ k, Matrix.trace (probe D i j k)) = 1 ∧
    (TriplePositive D (blockAveraged D alpha Phi (probe D)) ↔
      ∃ f : CompletelyPositiveMap (CStarBlocks D) (CStarBlocks D),
        f.toLinearMap = canonicalLinear D Phi) ∧
    ((∃ f : CompletelyPositiveMap (CStarBlocks D) (CStarBlocks D),
        f.toLinearMap = canonicalLinear D Phi) ↔
      ∀ Z : TripleBlocks D, TriplePositive D Z →
        TriplePositive D (blockAveraged D alpha Phi Z)) := by
  have hpc : TriplePositive D (blockAveraged D alpha Phi (probe D)) →
      ∃ f : CompletelyPositiveMap (CStarBlocks D) (CStarBlocks D),
        f.toLinearMap = canonicalLinear D Phi := by
    intro h
    exact (amplification_iff_canonical D Phi).mp
      ((amplification_iff_components D Phi).mpr
        (probe_detects_components D Phi alpha ha hsum h))
  have hcp : (∃ f : CompletelyPositiveMap (CStarBlocks D) (CStarBlocks D),
        f.toLinearMap = canonicalLinear D Phi) →
      ∀ Z : TripleBlocks D, TriplePositive D Z →
        TriplePositive D (blockAveraged D alpha Phi Z) := by
    intro h Z hZ
    exact blockAveraged_positive D Phi
      ((amplification_iff_components D Phi).mp ((amplification_iff_canonical D Phi).mpr h))
      alpha ha Z hZ
  exact ⟨probe_positive D, probe_trace D,
    ⟨hpc, fun h => hcp h _ (probe_positive D)⟩,
    ⟨hcp, fun h => hpc (h _ (probe_positive D))⟩⟩

end DirectSum

end D5.S3.Quantum.Foundation.ThreeLegChoiCompression
