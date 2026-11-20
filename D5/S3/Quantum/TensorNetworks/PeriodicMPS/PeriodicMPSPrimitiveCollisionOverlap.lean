/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSPrimitiveCollisionOverlap
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSPrimitiveCollisionOverlap
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSPrimitiveCollision]
   utility: none
   digest: The exponential overlap rate in a primitive collision. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSPrimitiveCollision

/-! The exact mixed transfer and overlap of the primitive Ising collision.
The cores and stabilization certificates are supplied by PeriodicMPSPrimitiveCollisionTransfer. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSPrimitiveCollision

open Matrix Complex Polynomial
open scoped Matrix Kronecker ComplexConjugate
open PeriodicMPSParentIntersection (Bond Word wordMatrix wordMatrix_append)
open PeriodicMPSUniformAntisymmetricTransfer
  (TransferMatrix conjugateCore mixedTransfer mixedRaw)
open PeriodicMPSUniformHardCoreTransferRecurrence (binaryTransfer binaryInsertion)
open UniformMPSExpectedDimensionRefutation (traceWord)

noncomputable section

private abbrev Pair := Fin 2 × Fin 2

private def rowMajor {R : Type*} (M : Matrix (Fin 4) (Fin 4) R) : TransferMatrix R :=
  Matrix.reindex (finProdFinEquiv : Pair ≃ Fin 4).symm finProdFinEquiv.symm M

/-- Ket-first transfer: the ordered virtual pair has the ket index first. -/
def collisionMixedTransfer : TransferMatrix ℂ :=
  binaryTransfer (cores false) (conjugateCore (cores true))

private def collisionMixedTransferG : TransferMatrix GaussianInt :=
  binaryTransfer (coresG false) (braG true)

private theorem map_collisionMixedTransfer :
    GaussianInt.toComplex.mapMatrix collisionMixedTransferG = collisionMixedTransfer := by
  ext p q
  simp only [collisionMixedTransferG, collisionMixedTransfer, binaryTransfer, Matrix.add_apply,
    Matrix.kroneckerMap_apply, RingHom.mapMatrix_apply, Matrix.map_apply, map_add, map_mul,
    braG, conjugateCore, starRingEnd_apply, cores, GaussianInt.toComplex_star]

/-- Even columns e₀+e₃, e₁+e₂ and odd columns e₀-e₃, e₁-e₂. -/
private def reversalBasisG : TransferMatrix GaussianInt :=
  rowMajor !![1, 0, 1, 0; 0, 1, 0, 1; 0, 1, 0, -1; 1, 0, -1, 0]

private def reversalBlocksG : TransferMatrix GaussianInt :=
  rowMajor !![6, 10, 0, 0; ⟨0, 10⟩, ⟨0, 6⟩, 0, 0;
    0, 0, ⟨0, 8⟩, 0; 0, 0, 0, -8]

private theorem reversal_blocks_G :
    collisionMixedTransferG * reversalBasisG = reversalBasisG * reversalBlocksG := by
  funext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> decide +kernel

private def reversalBasis : TransferMatrix ℂ :=
  GaussianInt.toComplex.mapMatrix reversalBasisG

private def reversalBlocks : TransferMatrix ℂ :=
  rowMajor !![6, 10, 0, 0; 10 * I, 6 * I, 0, 0; 0, 0, 8 * I, 0; 0, 0, 0, -8]

private theorem reversal_blocks :
    collisionMixedTransfer * reversalBasis = reversalBasis * reversalBlocks := by
  have h := congrArg GaussianInt.toComplex.mapMatrix reversal_blocks_G
  simp only [map_mul, map_collisionMixedTransfer] at h
  have hb : GaussianInt.toComplex.mapMatrix reversalBlocksG = reversalBlocks := by
    ext ⟨i, j⟩ ⟨k, l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num [reversalBlocksG, reversalBlocks, rowMajor, Matrix.reindex_apply,
        Matrix.submatrix_apply, finProdFinEquiv, GaussianInt.toComplex_def', map_ofNat]
  rw [hb] at h
  exact h

private theorem reversalBasis_unit : IsUnit reversalBasis.det := by
  rw [reversalBasis, ← RingHom.map_det,
    show reversalBasisG.det = (-4 : GaussianInt) by decide +kernel]
  norm_num [isUnit_iff_ne_zero]

/-- The roots of the even block are obtained by substituting ±√41. -/
private def evenEigenvalue (s : ℂ) : ℂ := (1 + I) * (3 + s)

private def root41 : ℂ := (Real.sqrt 41 : ℝ)

private theorem root41_sq : root41 ^ 2 = 41 := by
  rw [root41, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 41)]
  norm_num

private theorem evenEigenvalue_quadratic (s : ℂ) (hs : s ^ 2 = 41) :
    evenEigenvalue s ^ 2 - 6 * (1 + I) * evenEigenvalue s - 64 * I = 0 := by
  unfold evenEigenvalue
  linear_combination (1 + I)^2 * hs + 32 * Complex.I_sq

/-- The four eigenvalues in the order even-plus, even-minus, first odd, second odd. -/
def collisionMixedEigenvalues : Pair → ℂ :=
  fun p => ![evenEigenvalue root41, evenEigenvalue (-root41), 8 * I, -8] (finProdFinEquiv p)

private def evenEigenbasis : TransferMatrix ℂ :=
  rowMajor !![10, 10, 0, 0;
    evenEigenvalue root41 - 6, evenEigenvalue (-root41) - 6, 0, 0;
    0, 0, 1, 0; 0, 0, 0, 1]

private theorem even_eigenbasis :
    reversalBlocks * evenEigenbasis = evenEigenbasis * diagonal collisionMixedEigenvalues := by
  have hp := evenEigenvalue_quadratic root41 root41_sq
  have hm := evenEigenvalue_quadratic (-root41) (by rw [neg_sq, root41_sq])
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [reversalBlocks, evenEigenbasis, collisionMixedEigenvalues,
      Matrix.mul_apply, Matrix.mul_diagonal, Fintype.sum_prod_type, Fin.sum_univ_two,
      rowMajor, Matrix.reindex_apply, Matrix.submatrix_apply, finProdFinEquiv] <;>
    try ring1
  · linear_combination -hp
  · linear_combination -hm

private theorem evenEigenbasis_unit : IsUnit evenEigenbasis.det := by
  rw [evenEigenbasis, rowMajor, Matrix.det_reindex_self, isUnit_iff_ne_zero]
  have hdet : (det !![(10 : ℂ), 10, 0, 0;
      evenEigenvalue root41 - 6, evenEigenvalue (-root41) - 6, 0, 0;
      0, 0, 1, 0; 0, 0, 0, 1]) = -20 * (1 + I) * root41 := by
    norm_num [Matrix.det_succ_row_zero, Matrix.det_fin_two, Matrix.submatrix_apply,
      Fin.sum_univ_succ, evenEigenvalue,
      show (1 : Fin 4).succAbove (2 : Fin 3) = 3 by decide]
    ring
  rw [hdet]
  have hroot : root41 ≠ 0 := by
    intro h
    have hsq := root41_sq
    rw [h] at hsq
    norm_num at hsq
  have hI : (1 + I : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  exact mul_ne_zero (mul_ne_zero (by norm_num) hI) hroot

private def collisionEigenbasis : TransferMatrix ℂ := reversalBasis * evenEigenbasis

private theorem collisionEigenbasis_unit : IsUnit collisionEigenbasis.det := by
  rw [collisionEigenbasis, Matrix.det_mul]
  exact reversalBasis_unit.mul evenEigenbasis_unit

private theorem collision_intertwine :
    collisionMixedTransfer * collisionEigenbasis =
      collisionEigenbasis * diagonal collisionMixedEigenvalues := by
  rw [collisionEigenbasis, ← mul_assoc, reversal_blocks, mul_assoc, even_eigenbasis, mul_assoc]

private theorem collision_transfer_pow (n : ℕ) :
    collisionMixedTransfer ^ n =
      collisionEigenbasis * diagonal (fun p => collisionMixedEigenvalues p ^ n) *
        collisionEigenbasis⁻¹ := by
  have h (k : ℕ) : collisionMixedTransfer ^ k * collisionEigenbasis =
      collisionEigenbasis * (diagonal collisionMixedEigenvalues) ^ k := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_succ, mul_assoc, collision_intertwine, ← mul_assoc, ih, mul_assoc]
  change _ = collisionEigenbasis * diagonal (collisionMixedEigenvalues ^ n) * collisionEigenbasis⁻¹
  rw [← Matrix.diagonal_pow, ← h, mul_assoc,
    Matrix.mul_nonsing_inv _ collisionEigenbasis_unit, mul_one]

private theorem collision_trace_pow_sum (n : ℕ) :
    (collisionMixedTransfer ^ n).trace = ∑ p, collisionMixedEigenvalues p ^ n := by
  rw [collision_transfer_pow, Matrix.trace_mul_comm, ← mul_assoc,
    Matrix.nonsing_inv_mul _ collisionEigenbasis_unit, one_mul, Matrix.trace_diagonal]

/-- Exact mixed contraction at every length, including the empty product. -/
theorem collision_mixed_trace_pow (n : ℕ) :
    (collisionMixedTransfer ^ n).trace =
      (-(8 : ℂ)) ^ n + (8 * I) ^ n +
        ((1 + I) * (3 + (Real.sqrt 41 : ℝ))) ^ n +
        ((1 + I) * (3 - (Real.sqrt 41 : ℝ))) ^ n := by
  rw [collision_trace_pow_sum]
  simp [collisionMixedEigenvalues, evenEigenvalue, root41, Fintype.sum_prod_type,
    Fin.sum_univ_two, finProdFinEquiv, sub_eq_add_neg, add_comm, add_assoc]

/-- Characteristic polynomial in the row-major virtual pair convention. -/
theorem collision_mixed_charpoly :
    collisionMixedTransfer.charpoly =
      (X + C 8) * (X - C (8 * I)) * (X ^ 2 - C (6 * (1 + I)) * X - C (64 * I)) := by
  have hquad : (X - C (evenEigenvalue root41)) * (X - C (evenEigenvalue (-root41))) =
      X ^ 2 - C (6 * (1 + I)) * X - C (64 * I) := by
    have hsum : evenEigenvalue root41 + evenEigenvalue (-root41) = 6 * (1 + I) := by
      unfold evenEigenvalue
      ring
    have hprod : evenEigenvalue root41 * evenEigenvalue (-root41) = -(64 * I) := by
      unfold evenEigenvalue
      linear_combination -(1 + I)^2 * root41_sq - 32 * Complex.I_sq
    calc
      _ = X ^ 2 - (C (evenEigenvalue root41) + C (evenEigenvalue (-root41))) * X +
          C (evenEigenvalue root41) * C (evenEigenvalue (-root41)) := by ring
      _ = _ := by
        rw [← map_add, hsum, ← map_mul, hprod, map_neg]
        ring
  have h := collision_transfer_pow 1
  simp only [pow_one] at h
  rw [h, Matrix.charpoly_mul_comm, ← mul_assoc,
    Matrix.nonsing_inv_mul _ collisionEigenbasis_unit, one_mul, Matrix.charpoly_diagonal]
  simp only [Fintype.prod_prod_type, Fin.prod_univ_two]
  change ((X - C (evenEigenvalue root41)) * (X - C (evenEigenvalue (-root41)))) *
    ((X - C (8 * I)) * (X - C (-8))) = _
  rw [hquad, map_neg, sub_neg_eq_add]
  ring

private theorem binaryTransfer_pow_words (A B : Fin 2 → Bond) (n : ℕ) :
    binaryTransfer A B ^ n = ∑ w : Word n, wordMatrix A w ⊗ₖ wordMatrix B w := by
  unfold wordMatrix
  induction n with
  | zero => simp [Finset.univ_unique]
  | succ n ih =>
    rw [pow_succ', ih, ← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 2)).sum_comp,
      Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ,
      List.prod_cons, Fin.sum_univ_two]
    unfold binaryTransfer
    simp_rw [Matrix.mul_kronecker_mul, ← Finset.mul_sum, ← add_mul]

private theorem conjugate_word (B : Fin 2 → Bond) {n : ℕ} (w : Word n) :
    wordMatrix (conjugateCore B) w = (wordMatrix B w).map (starRingEnd ℂ) := by
  change (List.ofFn fun i => (RingHom.mapMatrix (starRingEnd ℂ)) (B (w i))).prod =
    (RingHom.mapMatrix (starRingEnd ℂ)) (List.ofFn fun i => B (w i)).prod
  rw [map_list_prod, List.map_ofFn]
  rfl

private theorem trace_binaryTransfer_pow (A B : Fin 2 → Bond) (n : ℕ) :
    (binaryTransfer A (conjugateCore B) ^ n).trace =
      ∑ w : Word n, traceWord 2 2 n A w * star (traceWord 2 2 n B w) := by
  rw [binaryTransfer_pow_words, Matrix.trace_sum]
  simp only [Matrix.trace_kronecker, conjugate_word, ← AddMonoidHom.map_trace (starRingEnd ℂ),
    starRingEnd_apply]
  rfl

/-- The exact raw coordinate overlap uses the same ket/bra convention as the transfer. -/
theorem collision_word_overlap (n : ℕ) :
    (∑ w : Word n, traceWord 2 2 n (cores false) w * star (traceWord 2 2 n (cores true) w)) =
      (collisionMixedTransfer ^ n).trace :=
  (trace_binaryTransfer_pow _ _ _).symm

open PeriodicMPSProjectiveCoordinates (mass)

private theorem stabilized_trace_pow (b : Bool) (r : ℕ) :
    (stabilizedTransfer b ^ (r + 2)).trace = 1 := by
  have h (k : ℕ) : stabilizedTransfer b ^ (k + 2) = stabilizedTransfer b ^ 2 := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [show k + 1 + 2 = (k + 2) + 1 by omega, pow_succ, ih,
        ← pow_succ, stabilizedTransfer_cube]
  rw [h, stabilizedTransfer_square, Matrix.trace_vecMulVec]
  norm_num [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- Squared Euclidean mass of the actual periodic trace words for every length at least two. -/
theorem collision_word_mass (b : Bool) (n : ℕ) (hn : 2 ≤ n) :
    mass (traceWord 2 2 n (cores b)) = (collisionScale b : ℝ) ^ n := by
  let S := mixedTransfer (cores b) (conjugateCore (cores b))
  have hS : S = (collisionScale b : ℂ) • stabilizedTransfer b := by
    have hc : (collisionScale b : ℂ) ≠ 0 := by cases b <;> norm_num [collisionScale]
    rw [stabilizedTransfer, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have ht : (S ^ n).trace = (collisionScale b : ℂ) ^ n := by
    have hs := stabilized_trace_pow b (n - 2)
    rw [Nat.sub_add_cancel hn] at hs
    rw [hS, _root_.smul_pow, Matrix.trace_smul, hs, smul_eq_mul, mul_one]
  rw [show S = binaryTransfer (conjugateCore (cores b)) (cores b) from rfl,
    binaryTransfer_pow_words, Matrix.trace_sum] at ht
  simp only [Matrix.trace_kronecker, conjugate_word, ← AddMonoidHom.map_trace (starRingEnd ℂ),
    starRingEnd_apply] at ht
  have hr := congrArg Complex.re ht
  rw [Complex.re_sum, ← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.ofReal_re] at hr
  rw [← hr, mass]
  apply Finset.sum_congr rfl
  intro w _
  change _ = (conj (wordMatrix (cores b) w).trace * (wordMatrix (cores b) w).trace).re
  rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  rfl

/-- Overlap of the two unit vectors obtained by positive real normalization of the trace words. -/
def collisionNormalizedOverlap (n : ℕ) : ℂ :=
  (∑ w : Word n, traceWord 2 2 n (cores false) w * star (traceWord 2 2 n (cores true) w)) /
    ((Real.sqrt (mass (traceWord 2 2 n (cores false))) *
      Real.sqrt (mass (traceWord 2 2 n (cores true))) : ℝ) : ℂ)

private theorem sqrt_pow_nonneg (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    Real.sqrt (x ^ n) = Real.sqrt x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Real.sqrt_mul hx, ih, pow_succ']

private theorem collision_normalizing_factor (n : ℕ) (hn : 2 ≤ n) :
    Real.sqrt (mass (traceWord 2 2 n (cores false))) *
      Real.sqrt (mass (traceWord 2 2 n (cores true))) = Real.sqrt 200 ^ n := by
  rw [collision_word_mass false n hn, collision_word_mass true n hn]
  change Real.sqrt ((10 : ℝ) ^ n) * Real.sqrt ((20 : ℝ) ^ n) = Real.sqrt 200 ^ n
  rw [sqrt_pow_nonneg 10 (by norm_num), sqrt_pow_nonneg 20 (by norm_num), ← mul_pow,
    ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 10)]
  norm_num

/-- Exact normalized overlap as a sum of four geometric sequences. -/
theorem collision_normalized_overlap (n : ℕ) (hn : 2 ≤ n) :
    collisionNormalizedOverlap n =
      ∑ p, (collisionMixedEigenvalues p / (Real.sqrt 200 : ℂ)) ^ n := by
  rw [collisionNormalizedOverlap, collision_word_overlap, collision_trace_pow_sum,
    collision_normalizing_factor n hn, Complex.ofReal_pow, Finset.sum_div]
  simp only [div_pow]

private theorem collision_eigenvalue_bound (p : Pair) :
    ‖collisionMixedEigenvalues p‖ ≤ (19 / 20 : ℝ) * Real.sqrt 200 := by
  have h41 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 41)
  have h200 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 200)
  have hs : Real.sqrt 41 ≤ 13 / 2 :=
    (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp (by rw [h41]; norm_num)
  have hs0 := Real.sqrt_nonneg 41
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), Complex.sq_norm]
  rcases p with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [collisionMixedEigenvalues, evenEigenvalue, root41, finProdFinEquiv,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;>
    nlinarith

private theorem collision_normalized_eigenvalue_bound (p : Pair) :
    ‖collisionMixedEigenvalues p / (Real.sqrt 200 : ℂ)‖ ≤ (19 / 20 : ℝ) := by
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    div_le_iff₀ (Real.sqrt_pos.2 (by norm_num))]
  exact collision_eigenvalue_bound p

/-- Exponential decay of the unit-vector overlap in the exact two-site collision fibre. -/
theorem collision_normalized_overlap_bound (n : ℕ) (hn : 2 ≤ n) :
    ‖collisionNormalizedOverlap n‖ ≤ 4 * (19 / 20 : ℝ) ^ n := by
  rw [collision_normalized_overlap n hn]
  calc
    _ ≤ ∑ p, ‖(collisionMixedEigenvalues p / (Real.sqrt 200 : ℂ)) ^ n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _p : Pair, (19 / 20 : ℝ) ^ n := by
      apply Finset.sum_le_sum
      intro p _
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (collision_normalized_eigenvalue_bound p) _
    _ = _ := by simp [Fintype.card_prod]

private def swapVirtual : TransferMatrix ℂ ≃ₐ[ℂ] TransferMatrix ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (Equiv.prodComm (Fin 2) (Fin 2))

private theorem swapVirtual_kronecker (P Q : Bond) :
    swapVirtual (P ⊗ₖ Q) = Q ⊗ₖ P := by
  ext i j
  change P i.2 j.2 * Q i.1 j.1 = Q i.1 j.1 * P i.2 j.2
  exact mul_comm _ _

private theorem trace_swapVirtual (M : TransferMatrix ℂ) :
    (swapVirtual M).trace = M.trace :=
  Equiv.sum_comp (Equiv.prodComm (Fin 2) (Fin 2)) (fun i => M i i)

private theorem mixedRaw_eq_word_cross (A B : Fin 2 → Bond) (m : ℕ) (p q : Pair) :
    mixedRaw A (conjugateCore B) m p q =
      ∑ w : Word m, traceWord 2 2 (2 + m) A (Fin.append ![p.1, p.2] w) *
        star (traceWord 2 2 (2 + m) B (Fin.append ![q.1, q.2] w)) := by
  rw [mixedRaw, mixedTransfer, binaryTransfer_pow_words, Matrix.mul_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro w _
  change _ = (wordMatrix A (Fin.append ![p.1, p.2] w)).trace *
    star (wordMatrix B (Fin.append ![q.1, q.2] w)).trace
  rw [wordMatrix_append, wordMatrix_append, mul_comm]
  have hpair (D : Fin 2 → Bond) (s : Pair) : wordMatrix D ![s.1, s.2] = D s.1 * D s.2 := by
    simp [wordMatrix, List.ofFn_succ]
  rw [hpair, hpair]
  simp only [binaryInsertion, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker, conjugate_word]
  congr 1
  change ((RingHom.mapMatrix (starRingEnd ℂ)) (B q.1) *
    (RingHom.mapMatrix (starRingEnd ℂ)) (B q.2) *
    (RingHom.mapMatrix (starRingEnd ℂ)) (wordMatrix B w)).trace = _
  rw [← map_mul, ← map_mul]
  exact (AddMonoidHom.map_trace (starRingEnd ℂ) _).symm

private def collisionInsertion (p q : Pair) : TransferMatrix ℂ :=
  binaryInsertion (cores false) (conjugateCore (cores true)) p q

private theorem collision_raw_ketFirst (m : ℕ) (p q : Pair) :
    mixedRaw (cores false) (conjugateCore (cores true)) m p q =
      (collisionInsertion p q * collisionMixedTransfer ^ m).trace := by
  rw [mixedRaw, ← trace_swapVirtual]
  simp only [mixedTransfer, binaryInsertion, binaryTransfer, map_add, map_mul, map_pow,
    swapVirtual_kronecker, collisionInsertion, collisionMixedTransfer]

/-- Cross reduced operator on the first two sites, with both rays normalized. -/
def collisionNormalizedCross (m : ℕ) : TransferMatrix ℂ :=
  fun p q =>
    (∑ w : Word m, traceWord 2 2 (2 + m) (cores false) (Fin.append ![p.1, p.2] w) *
      star (traceWord 2 2 (2 + m) (cores true) (Fin.append ![q.1, q.2] w))) /
    ((Real.sqrt (mass (traceWord 2 2 (2 + m) (cores false))) *
      Real.sqrt (mass (traceWord 2 2 (2 + m) (cores true)))) : ℝ)

/-- The fixed spectral coefficients of the two-site insertion. -/
def collisionCrossWeight (p q k : Pair) : ℂ :=
  (collisionEigenbasis⁻¹ * collisionInsertion p q * collisionEigenbasis) k k

/-- Exact spectral formula for the normalized cross reduced operator. -/
theorem collision_cross_contraction (m : ℕ) (p q : Pair) :
    collisionNormalizedCross m p q =
      (∑ k, collisionCrossWeight p q k *
        (collisionMixedEigenvalues k / (Real.sqrt 200 : ℂ)) ^ m) / 200 := by
  have hsqrt : ((Real.sqrt 200 : ℝ) : ℂ) ^ 2 = 200 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 200)]
    norm_num
  rw [collisionNormalizedCross, ← mixedRaw_eq_word_cross, collision_raw_ketFirst,
    collision_normalizing_factor _ (by omega), Complex.ofReal_pow, pow_add, hsqrt,
    collision_transfer_pow, ← mul_assoc, Matrix.trace_mul_comm, ← mul_assoc, ← mul_assoc]
  change (∑ k, ((collisionEigenbasis⁻¹ * collisionInsertion p q * collisionEigenbasis) *
    Matrix.diagonal (fun i => collisionMixedEigenvalues i ^ m)) k k) / _ = _
  simp only [Matrix.mul_diagonal, div_pow, collisionCrossWeight]
  rw [mul_comm (200 : ℂ), ← div_div, Finset.sum_div]
  simp only [mul_div_assoc]

/-- Entrywise decay with an explicit length-independent coefficient. -/
theorem collision_cross_entry_bound (m : ℕ) (p q : Pair) :
    ‖collisionNormalizedCross m p q‖ ≤
      ((∑ k, ‖collisionCrossWeight p q k‖) / 200) * (19 / 20 : ℝ) ^ m := by
  rw [collision_cross_contraction, norm_div]
  rw [show ‖(200 : ℂ)‖ = (200 : ℝ) by
    rw [← Complex.ofReal_ofNat, Complex.norm_real]
    norm_num]
  have h := norm_sum_le Finset.univ
    (fun k => collisionCrossWeight p q k * (collisionMixedEigenvalues k / (Real.sqrt 200 : ℂ)) ^ m)
  calc
    _ ≤ (∑ k, ‖collisionCrossWeight p q k‖ * (19 / 20 : ℝ) ^ m) / 200 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      refine h.trans (Finset.sum_le_sum fun k _ => ?_)
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (collision_normalized_eigenvalue_bound k) _) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

open Filter Topology

private def normalizedEigenvalue (p : Pair) : ℂ :=
  collisionMixedEigenvalues p / (Real.sqrt 200 : ℂ)

private theorem leading_eigenvalue_norm :
    ‖normalizedEigenvalue (0, 0)‖ = (3 + Real.sqrt 41) / 10 := by
  rw [normalizedEigenvalue, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    div_eq_iff (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 200)).ne']
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [Complex.sq_norm, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 200)]
  norm_num [collisionMixedEigenvalues, evenEigenvalue, root41, finProdFinEquiv,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  ring

private theorem other_eigenvalue_norm (p : Pair) (hp : p ≠ (0, 0)) :
    ‖collisionMixedEigenvalues p‖ ≤ 8 := by
  have hs₀ : 3 ≤ Real.sqrt 41 :=
    (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
      (by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 41)]; norm_num)
  have hs₁ : Real.sqrt 41 ≤ 7 :=
    (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
      (by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 41)]; norm_num)
  have h41 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 41)
  rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num), Complex.sq_norm]
  rcases p with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> try exact (hp rfl).elim
  all_goals
    norm_num [collisionMixedEigenvalues, evenEigenvalue, root41, finProdFinEquiv,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  nlinarith

private theorem other_normalized_eigenvalue_lt (p : Pair) (hp : p ≠ (0, 0)) :
    ‖normalizedEigenvalue p‖ < ‖normalizedEigenvalue (0, 0)‖ := by
  have hs : 6 ≤ Real.sqrt 41 :=
    (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
      (by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 41)]; norm_num)
  have hd : 10 < Real.sqrt 200 :=
    (sq_lt_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
      (by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 200)]; norm_num)
  rw [leading_eigenvalue_norm, normalizedEigenvalue, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), div_lt_iff₀ (Real.sqrt_pos.2 (by norm_num))]
  refine (other_eigenvalue_norm p hp).trans_lt ?_
  have hmul := mul_lt_mul_of_pos_left hd (show 0 < (3 + Real.sqrt 41) / 10 by positivity)
  linarith

private theorem overlap_div_leading_tendsto :
    Tendsto (fun n : ℕ => collisionNormalizedOverlap n / normalizedEigenvalue (0, 0) ^ n)
      atTop (𝓝 1) := by
  have hpos : 0 < ‖normalizedEigenvalue (0, 0)‖ := by rw [leading_eigenvalue_norm]; positivity
  have hne : normalizedEigenvalue (0, 0) ≠ 0 := norm_pos_iff.mp hpos
  have hzero (p : Pair) (hp : p ≠ (0, 0)) :
      Tendsto (fun n : ℕ => (normalizedEigenvalue p / normalizedEigenvalue (0, 0)) ^ n)
        atTop (𝓝 0) := by
    apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    rw [norm_div, div_lt_one hpos]
    exact other_normalized_eigenvalue_lt p hp
  have h := ((tendsto_const_nhds (x := (1 : ℂ))).add (hzero (0, 1) (by decide))).add
    ((hzero (1, 0) (by decide)).add (hzero (1, 1) (by decide)))
  simp only [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  rw [collision_normalized_overlap n hn, Finset.sum_div]
  simp only [← div_pow, Fintype.sum_prod_type, Fin.sum_univ_two]
  change _ = (normalizedEigenvalue (0, 0) / normalizedEigenvalue (0, 0)) ^ n + _ + (_ + _)
  rw [div_self hne, one_pow]
  rfl

/-- The nth root of the overlap magnitude converges to the dominant normalized eigenvalue modulus. -/
theorem collision_overlap_sharp_rate :
    Tendsto (fun n : ℕ => ‖collisionNormalizedOverlap n‖ ^ (1 / (n : ℝ)))
      atTop (𝓝 ((3 + Real.sqrt 41) / 10)) := by
  have hnorm : Tendsto (fun n : ℕ => ‖collisionNormalizedOverlap n / normalizedEigenvalue (0, 0) ^ n‖)
      atTop (𝓝 (1 : ℝ)) := by simpa only [norm_one] using overlap_div_leading_tendsto.norm
  have hpow :=
    hnorm.rpow (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)) (Or.inl one_ne_zero)
  rw [Real.one_rpow] at hpow
  have h := hpow.const_mul ‖normalizedEigenvalue (0, 0)‖
  rw [mul_one] at h
  rw [← leading_eigenvalue_norm]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpos : 0 < ‖normalizedEigenvalue (0, 0)‖ := by rw [leading_eigenvalue_norm]; positivity
  rw [norm_div, norm_pow, Real.div_rpow (norm_nonneg _) (pow_nonneg (norm_nonneg _) _),
    ← Real.rpow_natCast_mul (norm_nonneg _),
    show (n : ℝ) * (1 / (n : ℝ)) = 1 by field_simp, Real.rpow_one]
  field_simp

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSPrimitiveCollision

#print axioms D5.S3.Quantum.TensorNetworks.PeriodicMPSPrimitiveCollision.collision_mixed_charpoly
#print axioms D5.S3.Quantum.TensorNetworks.PeriodicMPSPrimitiveCollision.collision_mixed_trace_pow
#print axioms D5.S3.Quantum.TensorNetworks.PeriodicMPSPrimitiveCollision.collision_word_mass
#print axioms D5.S3.Quantum.TensorNetworks.PeriodicMPSPrimitiveCollision.collision_normalized_overlap
#print axioms D5.S3.Quantum.TensorNetworks.PeriodicMPSPrimitiveCollision.collision_normalized_overlap_bound
#print axioms D5.S3.Quantum.TensorNetworks.PeriodicMPSPrimitiveCollision.collision_cross_contraction
#print axioms D5.S3.Quantum.TensorNetworks.PeriodicMPSPrimitiveCollision.collision_cross_entry_bound
#print axioms D5.S3.Quantum.TensorNetworks.PeriodicMPSPrimitiveCollision.collision_overlap_sharp_rate
