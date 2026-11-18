/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original corrected and transported inverse source blocks. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalResolvent
import Mathlib.LinearAlgebra.Matrix.Kronecker

noncomputable section
open scoped BigOperators Matrix Kronecker Matrix.Norms.L2Operator Topology ENNReal
open Filter

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks

open LatticeGeneratingFieldLocality LatticeHalfFock OriginalCurrentMetric
open OriginalNormalRowSource OriginalCorrectedRowRecompositionSource
open OriginalSourceInverseCoefficient NativeAffineTransport
open OriginalGaussianMatrix OriginalGaussianResolvent OriginalGaussianExternalResolvent
open OriginalGaussianAllIndexResolvent OriginalGaussianUniformCutoff

abbrev Internal (D : LatticeData) (N : ℕ) := Fin D.rank × Fin N
abbrev External (D : LatticeData) := Bool × Index D

private def externalIndex (D : LatticeData) (x : External D) :
    Index D ⊕ (Index D ⊕ Index D) :=
  if x.1 then .inr (.inr x.2) else .inr (.inl x.2)

private def rowIndex (D : LatticeData) (N : ℕ) {X : Type*}
    (e : X → External D) : Internal D N ⊕ X → Index D ⊕ (Index D ⊕ Index D)
  | .inl i => .inl (boxLabel D N i)
  | .inr x => externalIndex D (e x)

/-- Restriction of the literal corrected source row to a frequency box and
any finite external family. External modes need not lie in the source box. -/
def originalRow (D : LatticeData) (N : ℕ) {X : Type*} (e : X → External D) :
    Matrix (Internal D N ⊕ X) (Internal D N ⊕ X) ℂ :=
  (correctedMatrix D (Function.Embedding.refl (Index D))).submatrix
    (rowIndex D N e) (rowIndex D N e)

/-- The original inverse-right substitution, fixing external coordinates. -/
def inverseSubstitution (D : LatticeData) (N : ℕ) :
    Matrix (Internal D N) (Internal D N) ℂ :=
  boxMatrix D N (fun k => (((-((k : ℂ) + 1))⁻¹ • (gramComplex D)⁻¹))ᵀ)

def damp (D : LatticeData) (N : ℕ) {X : Type*} (z : ℂ) : Internal D N ⊕ X → ℂ
  | .inl i => z ^ (i.2.val + 1)
  | .inr _ => 1

def leftRow (D : LatticeData) (N : ℕ) {X : Type*} (e : X → External D) (z : ℂ) :
    Matrix (Internal D N ⊕ X) (Internal D N ⊕ X) ℂ :=
  fun i j => damp D N z i * originalRow D N e i j * damp D N z j

def rightRow (D : LatticeData) (N : ℕ) {X : Type*} [Fintype X] [DecidableEq X]
    (e : X → External D) (z : ℂ) :
    Matrix (Internal D N ⊕ X) (Internal D N ⊕ X) ℂ :=
  fun i j => damp D N z i *
    transportCovariance (sourceBlock (J := X) (inverseSubstitution D N))
      (originalRow D N e) i j * damp D N z j

def frequencyRoot (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (fun s => (Real.sqrt (s.val + 1 : ℝ) : ℂ))

def inverseFrequencyRoot (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (fun s => (Real.sqrt (s.val + 1 : ℝ) : ℂ)⁻¹)

private lemma root_ne (s : ℕ) : (Real.sqrt (s + 1 : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < s + 1)).ne'

private lemma root_sq (s : ℕ) : (Real.sqrt (s + 1 : ℝ) : ℂ) ^ 2 = (s + 1 : ℂ) := by
  exact_mod_cast Real.sq_sqrt (by positivity : (0 : ℝ) ≤ s + 1)

lemma root_units (N : ℕ) :
    frequencyRoot N * inverseFrequencyRoot N = 1 ∧
      inverseFrequencyRoot N * frequencyRoot N = 1 := by
  have hb (i : Fin N) : (Real.sqrt ((i.val : ℝ) + 1) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < (i.val : ℝ) + 1)).ne'
  constructor <;> ext i j <;>
    by_cases h : i = j <;>
    simp [frequencyRoot, inverseFrequencyRoot, Matrix.diagonal_mul_diagonal,
      hb, Matrix.one_apply, Matrix.diagonal_apply, h, Nat.cast_add, Nat.cast_one]

private lemma gram_symm (D : LatticeData) : (gramComplex D).transpose = gramComplex D := by
  ext i j
  change (D.G j i : ℂ) = (D.G i j : ℂ)
  exact_mod_cast D.symmetric j i

private lemma inverse_gram_symm (D : LatticeData) :
    ((gramComplex D)⁻¹).transpose = (gramComplex D)⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, gram_symm]

lemma original_source (D : LatticeData) (N : ℕ) {X : Type*}
    (e : X → External D) (z : ℂ) :
    (leftRow D N e z).submatrix Sum.inl Sum.inl =
      (gramComplex D) ⊗ₖ (frequencyRoot N * finiteSection N z * frequencyRoot N) := by
  ext ⟨i,s⟩ ⟨j,t⟩
  change z ^ (s.val + 1) *
      (LatticeHalfFockFiniteCorrection.pairScalar (s.val + 1) (t.val + 1) *
        (D.G i j : ℂ)) * z ^ (t.val + 1) = _
  simp only [leftRow, damp, originalRow, Matrix.submatrix_apply, rowIndex,
    correctedMatrix, sourceCovariance, Function.Embedding.refl_apply, boxLabel,
    Matrix.kronecker_apply, frequencyRoot, Matrix.diagonal_mul, Matrix.mul_diagonal,
    finiteSection, matrixEntry, gramComplex, Matrix.map_apply, pow_add]
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp [root_ne]
  <;> ring

private lemma inverseSubstitution_entry (D : LatticeData) (N : ℕ)
    (i j : Internal D N) :
    inverseSubstitution D N i j =
      if i.2 = j.2 then -(j.2.val + 1 : ℂ)⁻¹ * (gramComplex D)⁻¹ i.1 j.1 else 0 := by
  simp only [inverseSubstitution, boxMatrix, Matrix.transpose_apply, Matrix.smul_apply,
    smul_eq_mul, inv_neg]
  rw [show (gramComplex D)⁻¹ j.1 i.1 = (gramComplex D)⁻¹ i.1 j.1 from
    congrArg (fun A => A i.1 j.1) (inverse_gram_symm D)]

private lemma inverseSubstitution_formula (D : LatticeData) (N : ℕ) :
    inverseSubstitution D N = -((gramComplex D)⁻¹ ⊗ₖ
      (inverseFrequencyRoot N * inverseFrequencyRoot N)) := by
  ext ⟨i,s⟩ ⟨j,t⟩
  rw [inverseSubstitution_entry]
  simp only [Matrix.neg_apply, Matrix.kronecker_apply, inverseFrequencyRoot,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, Pi.mul_apply]
  by_cases h : s = t
  · simp only [h, ↓reduceIte]
    rw [← pow_two, inv_pow, root_sq]
    ring
  · simp [h]

private lemma right_source_transport (D : LatticeData) (N : ℕ)
    {X : Type*} [Fintype X] [DecidableEq X] (e : X → External D) (z : ℂ) :
    (rightRow D N e z).submatrix Sum.inl Sum.inl =
      inverseSubstitution D N * (leftRow D N e z).submatrix Sum.inl Sum.inl *
        (inverseSubstitution D N).transpose := by
  ext i j
  simp only [Matrix.submatrix_apply, rightRow, leftRow, damp, transportCovariance,
    Fintype.sum_sum_type, sourceBlock, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul, mul_zero,
    Finset.sum_const_zero, add_zero, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [inverseSubstitution_entry, inverseSubstitution_entry]
  split_ifs with ha hb
  · rw [ha, hb]
    ring
  · ring
  · ring
  · ring

lemma original_inverse_source (D : LatticeData) (hu : IsUnit D.G.det) (N : ℕ)
    {X : Type*} [Fintype X] [DecidableEq X] (e : X → External D) (z : ℂ) :
    (rightRow D N e z).submatrix Sum.inl Sum.inl =
      (gramComplex D)⁻¹ ⊗ₖ
        (inverseFrequencyRoot N * finiteSection N z * inverseFrequencyRoot N) := by
  rw [right_source_transport, original_source, inverseSubstitution_formula,
    Matrix.transpose_neg, ← Matrix.kroneckerMap_transpose]
  have hi : (inverseFrequencyRoot N).transpose = inverseFrequencyRoot N := by
    simp [inverseFrequencyRoot]
  rw [Matrix.transpose_mul, hi, inverse_gram_symm]
  simp only [neg_mul, mul_neg, neg_neg, ← Matrix.mul_kronecker_mul]
  rw [Matrix.nonsing_inv_mul _ (SignedOscillatorWick.complex_det_unit D hu), one_mul]
  congr 1
  calc
    _ = (inverseFrequencyRoot N * (inverseFrequencyRoot N * frequencyRoot N)) *
      finiteSection N z * ((frequencyRoot N * inverseFrequencyRoot N) *
        inverseFrequencyRoot N) := by noncomm_ring
    _ = _ := by rw [(root_units N).1, (root_units N).2, mul_one, one_mul]

def finiteSquare (N : ℕ) (z : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Ring.inverse (1 - finiteSection N z ^ 2)

private lemma finiteSquare_unit (N : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    IsUnit (1 - finiteSection N z ^ 2) := by
  apply isUnit_one_sub_of_norm_lt_one
  have hk : ‖finiteSection N z‖ < 1 := (finiteSection_opNorm_le N z hz).trans_lt
    (pow_lt_one₀ (norm_nonneg z) hz (by norm_num))
  rw [pow_two]
  exact (norm_mul_le _ _).trans_lt
    (by simpa only [pow_two] using pow_lt_one₀ (norm_nonneg _) hk (by norm_num : (2 : ℕ) ≠ 0))

private lemma inverse_products (D : LatticeData) (hu : IsUnit D.G.det) (N : ℕ)
    {X : Type*} [Fintype X] [DecidableEq X] (e : X → External D) (z : ℂ) :
    let A := (leftRow D N e z).submatrix Sum.inl Sum.inl
    let B := (rightRow D N e z).submatrix Sum.inl Sum.inl
    B * A = (1 : Matrix (Fin D.rank) (Fin D.rank) ℂ) ⊗ₖ
      (inverseFrequencyRoot N * finiteSection N z ^ 2 * frequencyRoot N) ∧
    A * B = (1 : Matrix (Fin D.rank) (Fin D.rank) ℂ) ⊗ₖ
      (frequencyRoot N * finiteSection N z ^ 2 * inverseFrequencyRoot N) := by
  dsimp only
  rw [original_source, original_inverse_source D hu]
  constructor
  · rw [← Matrix.mul_kronecker_mul,
      Matrix.nonsing_inv_mul _ (SignedOscillatorWick.complex_det_unit D hu)]
    congr 1
    calc
      _ = inverseFrequencyRoot N * finiteSection N z *
        (inverseFrequencyRoot N * frequencyRoot N) * finiteSection N z *
          frequencyRoot N := by noncomm_ring
      _ = _ := by rw [(root_units N).2, mul_one]; noncomm_ring
  · rw [← Matrix.mul_kronecker_mul,
      Matrix.mul_nonsing_inv _ (SignedOscillatorWick.complex_det_unit D hu)]
    congr 1
    calc
      _ = frequencyRoot N * finiteSection N z *
        (frequencyRoot N * inverseFrequencyRoot N) * finiteSection N z *
          inverseFrequencyRoot N := by noncomm_ring
      _ = _ := by rw [(root_units N).1, mul_one]; noncomm_ring

private lemma finite_inverse_similarity (D : LatticeData) (N : ℕ)
    {z : ℂ} (hz : ‖z‖ < 1)
    (P Q : Matrix (Fin N) (Fin N) ℂ) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    Ring.inverse (1 - (1 : Matrix (Fin D.rank) (Fin D.rank) ℂ) ⊗ₖ
      (P * finiteSection N z ^ 2 * Q)) =
        (1 : Matrix (Fin D.rank) (Fin D.rank) ℂ) ⊗ₖ (P * finiteSquare N z * Q) := by
  let C := (1 : Matrix (Fin D.rank) (Fin D.rank) ℂ) ⊗ₖ (P * finiteSection N z ^ 2 * Q)
  let Y := (1 : Matrix (Fin D.rank) (Fin D.rank) ℂ) ⊗ₖ (P * finiteSquare N z * Q)
  have hT : (1 - finiteSection N z ^ 2) * finiteSquare N z = 1 :=
    Ring.mul_inverse_cancel _ (finiteSquare_unit N hz)
  have hY : (1 - C) * Y = 1 := by
    dsimp only [C, Y]
    rw [sub_mul, one_mul, ← Matrix.mul_kronecker_mul, one_mul]
    have hs : (P * finiteSquare N z * Q) -
        ((P * finiteSection N z ^ 2 * Q) * (P * finiteSquare N z * Q)) = 1 := by
      calc
        _ = P * ((1 - finiteSection N z ^ 2) * finiteSquare N z) * Q := by
          rw [sub_mul, one_mul]
          have hh : (P * finiteSection N z ^ 2 * Q) *
              (P * finiteSquare N z * Q) = P * finiteSection N z ^ 2 *
                (Q * P) * finiteSquare N z * Q := by noncomm_ring
          rw [hh, hQP, mul_one]
          noncomm_ring
        _ = _ := by rw [hT, mul_one, hPQ]
    calc
      _ = (1 : Matrix (Fin D.rank) (Fin D.rank) ℂ) ⊗ₖ
          ((P * finiteSquare N z * Q) -
            ((P * finiteSection N z ^ 2 * Q) * (P * finiteSquare N z * Q))) := by
        ext ⟨i,s⟩ ⟨j,t⟩
        simp only [Matrix.sub_apply, Matrix.kronecker_apply, mul_sub]
      _ = 1 := by rw [hs, Matrix.one_kronecker_one]
  have hU : IsUnit (1 - C) := IsUnit.of_mul_eq_one Y hY
  change Ring.inverse (1 - C) = Y
  calc
    _ = Ring.inverse (1 - C) * ((1 - C) * Y) := by rw [hY, mul_one]
    _ = Y := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hU, one_mul]

/-- Both ordered inverses of the literal raw source blocks exist throughout
the complex unit disk and are finite similarities of the square resolvent. -/
theorem original_internal_inverse_similarities (D : LatticeData) (hu : IsUnit D.G.det)
    (N : ℕ) {X : Type*} [Fintype X] [DecidableEq X] (e : X → External D)
    {z : ℂ} (hz : ‖z‖ < 1) :
    let A := (leftRow D N e z).submatrix Sum.inl Sum.inl
    let B := (rightRow D N e z).submatrix Sum.inl Sum.inl
    Ring.inverse (1 - B * A) =
      (1 : Matrix (Fin D.rank) (Fin D.rank) ℂ) ⊗ₖ
        (inverseFrequencyRoot N * finiteSquare N z * frequencyRoot N) ∧
    Ring.inverse (1 - A * B) =
      (1 : Matrix (Fin D.rank) (Fin D.rank) ℂ) ⊗ₖ
        (frequencyRoot N * finiteSquare N z * inverseFrequencyRoot N) := by
  dsimp only
  rw [(inverse_products D hu N e z).1, (inverse_products D hu N e z).2]
  exact ⟨finite_inverse_similarity D N hz _ _ (root_units N).2 (root_units N).1,
    finite_inverse_similarity D N hz _ _ (root_units N).1 (root_units N).2⟩

lemma original_mixed (D : LatticeData) (N : ℕ) {X : Type*}
    (e : X → External D) (z : ℂ) (i : Internal D N) (x : X) :
    leftRow D N e z (.inl i) (.inr x) =
      (Real.sqrt (i.2.val + 1 : ℝ) : ℂ) *
        externalColumn (e x).1 (e x).2.2 z i.2.val * (gramComplex D) i.1 (e x).2.1 := by
  have h := OriginalGaussianExternalResolvent.actual_left_mixed D z
    (boxLabel D N i) (e x).1 (e x).2
  rw [show boxLabel D N i = (i.1, i.2.val) from rfl] at h
  change z ^ (i.2.val + 1) * correctedMatrix D (Function.Embedding.refl (Index D))
    (.inl (boxLabel D N i)) (externalIndex D (e x)) =
      (Real.sqrt (i.2.val + 1 : ℝ) : ℂ) *
        externalColumn (e x).1 (e x).2.2 z i.2.val * (D.G i.1 (e x).2.1 : ℂ) at h
  change z ^ (i.2.val + 1) * correctedMatrix D (Function.Embedding.refl (Index D))
    (.inl (boxLabel D N i)) (externalIndex D (e x)) * 1 = _
  simpa only [mul_one, gramComplex, Matrix.map_apply] using h

private lemma right_mixed_transport (D : LatticeData) (N : ℕ)
    {X : Type*} [Fintype X] [DecidableEq X] (e : X → External D) (z : ℂ) :
    (rightRow D N e z).submatrix Sum.inl Sum.inr =
      inverseSubstitution D N * (leftRow D N e z).submatrix Sum.inl Sum.inr := by
  ext i x
  simp only [Matrix.submatrix_apply, rightRow, leftRow, damp, transportCovariance,
    Fintype.sum_sum_type, sourceBlock, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, Matrix.one_apply, zero_mul, mul_zero,
    Finset.sum_const_zero, add_zero, zero_add, mul_one, Matrix.mul_apply, Finset.mul_sum,
    mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  apply Finset.sum_congr rfl
  intro a _
  rw [inverseSubstitution_entry]
  by_cases h : i.2 = a.2
  · simp only [h, ↓reduceIte]
    ring
  · simp [h]

lemma original_inverse_mixed (D : LatticeData) (hu : IsUnit D.G.det) (N : ℕ)
    {X : Type*} [Fintype X] [DecidableEq X] (e : X → External D) (z : ℂ)
    (i : Internal D N) (x : X) :
    rightRow D N e z (.inl i) (.inr x) =
      -(Real.sqrt (i.2.val + 1 : ℝ) : ℂ)⁻¹ *
        externalColumn (e x).1 (e x).2.2 z i.2.val *
          (if i.1 = (e x).2.1 then 1 else 0) := by
  have h := congrArg (fun M => M i x) (right_mixed_transport D N e z)
  change rightRow D N e z (.inl i) (.inr x) = _ at h
  rw [h]
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, original_mixed,
    inverseSubstitution_entry, Fintype.sum_prod_type]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  have hg := congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℂ => M i.1 (e x).2.1)
    (Matrix.nonsing_inv_mul (gramComplex D) (SignedOscillatorWick.complex_det_unit D hu))
  simp only [Matrix.mul_apply, Matrix.one_apply] at hg
  have hfactor : (∑ j : Fin D.rank, -(i.2.val + 1 : ℂ)⁻¹ *
      (gramComplex D)⁻¹ i.1 j *
        ((Real.sqrt (i.2.val + 1 : ℝ) : ℂ) *
          externalColumn (e x).1 (e x).2.2 z i.2.val * (gramComplex D) j (e x).2.1)) =
      (-(i.2.val + 1 : ℂ)⁻¹ * (Real.sqrt (i.2.val + 1 : ℝ) : ℂ) *
        externalColumn (e x).1 (e x).2.2 z i.2.val) *
          (∑ j, (gramComplex D)⁻¹ i.1 j * (gramComplex D) j (e x).2.1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hfactor, hg, ← root_sq i.2.val]
  field_simp [root_ne]
  <;> ring

/-- The algebraic effective covariance of the literal damped source rows. -/
def originalEffectiveKernel (D : LatticeData) (N : ℕ) {X : Type*}
    [Fintype X] [DecidableEq X] (e : X → External D) (z : ℂ) : Matrix (X ⊕ X) (X ⊕ X) ℂ :=
  FiniteGaussianSewing.effectiveKernel
    ((leftRow D N e z).submatrix Sum.inr Sum.inr)
    ((rightRow D N e z).submatrix Sum.inr Sum.inr)
    ((leftRow D N e z).submatrix Sum.inl Sum.inl)
    ((rightRow D N e z).submatrix Sum.inl Sum.inl)
    ((leftRow D N e z).submatrix Sum.inr Sum.inl)
    ((rightRow D N e z).submatrix Sum.inl Sum.inr)

lemma original_mixed_transpose (D : LatticeData) (N : ℕ) {X : Type*}
    (e : X → External D) (z : ℂ) (i : Internal D N) (x : X) :
    leftRow D N e z (.inr x) (.inl i) = leftRow D N e z (.inl i) (.inr x) := by
  cases hx : (e x).1 <;>
    simp only [leftRow, damp, originalRow, Matrix.submatrix_apply, rowIndex,
      externalIndex, hx, Bool.false_eq_true, ↓reduceIte, correctedMatrix, normalMatrix,
      mul_one, one_mul] <;> ring

def finitePair (D : LatticeData) (N : ℕ) {X : Type*} (e : X → External D)
    (z : ℂ) (M : Matrix (Fin N) (Fin N) ℂ) (x y : X) : ℂ :=
  ∑ t : Fin N, ∑ s : Fin N, externalColumn (e x).1 (e x).2.2 z s.val *
    M s t * externalColumn (e y).1 (e y).2.2 z t.val

private lemma original_cross_block (D : LatticeData) (hu : IsUnit D.G.det) (N : ℕ)
    {X : Type*} [Fintype X] [DecidableEq X] (e : X → External D)
    {z : ℂ} (hz : ‖z‖ < 1) (x y : X) :
    originalEffectiveKernel D N e z (.inl x) (.inr y) =
      -(gramComplex D) (e x).2.1 (e y).2.1 * finitePair D N e z (finiteSquare N z) x y := by
  classical
  unfold originalEffectiveKernel FiniteGaussianSewing.effectiveKernel
  rw [Matrix.fromBlocks_apply₁₂, (original_internal_inverse_similarities D hu N e hz).1]
  have hQ (i j : Internal D N) :
      ((1 : Matrix (Fin D.rank) (Fin D.rank) ℂ) ⊗ₖ
        (inverseFrequencyRoot N * finiteSquare N z * frequencyRoot N)) i j =
      (if i.1 = j.1 then 1 else 0) *
        ((Real.sqrt (i.2.val + 1 : ℝ) : ℂ)⁻¹ * finiteSquare N z i.2 j.2 *
          (Real.sqrt (j.2.val + 1 : ℝ) : ℂ)) := by
    rw [Matrix.kroneckerMap_apply]
    simp only [Matrix.one_apply, frequencyRoot, inverseFrequencyRoot,
      Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, original_mixed_transpose,
    original_mixed, original_inverse_mixed D hu, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum, hQ]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.sum_ite_irrel, Finset.mem_univ, ↓reduceIte,
    Finset.sum_const_zero, mul_one, one_mul]
  rw [finitePair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [show (gramComplex D) (e y).2.1 (e x).2.1 =
      (gramComplex D) (e x).2.1 (e y).2.1 from
    congrArg (fun M => M (e x).2.1 (e y).2.1) (gram_symm D)]
  field_simp [root_ne]
  <;> ring

def finiteOdd (N : ℕ) (z : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  finiteSection N z * finiteSquare N z

private lemma finiteSquare_commutes (N : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    finiteSquare N z * finiteSection N z = finiteOdd N z := by
  let K := finiteSection N z
  let T := finiteSquare N z
  have ht : T * (1 - K ^ 2) = 1 :=
    Ring.inverse_mul_cancel _ (finiteSquare_unit N hz)
  have th : (1 - K ^ 2) * T = 1 :=
    Ring.mul_inverse_cancel _ (finiteSquare_unit N hz)
  calc
    T * K = T * K * ((1 - K ^ 2) * T) := by rw [th, mul_one]
    _ = (T * (1 - K ^ 2)) * K * T := by noncomm_ring
    _ = K * T := by rw [ht, one_mul]

private lemma internal_inverse_times_source (D : LatticeData) (hu : IsUnit D.G.det)
    (N : ℕ) {X : Type*} [Fintype X] [DecidableEq X] (e : X → External D)
    {z : ℂ} (hz : ‖z‖ < 1) :
    let A := (leftRow D N e z).submatrix Sum.inl Sum.inl
    let B := (rightRow D N e z).submatrix Sum.inl Sum.inl
    Ring.inverse (1 - B * A) * B = (gramComplex D)⁻¹ ⊗ₖ
      (inverseFrequencyRoot N * finiteOdd N z * inverseFrequencyRoot N) ∧
    Ring.inverse (1 - A * B) * A = (gramComplex D) ⊗ₖ
      (frequencyRoot N * finiteOdd N z * frequencyRoot N) := by
  dsimp only
  rw [(original_internal_inverse_similarities D hu N e hz).1,
    (original_internal_inverse_similarities D hu N e hz).2,
    original_source, original_inverse_source D hu]
  constructor
  · rw [← Matrix.mul_kronecker_mul, one_mul]
    congr 1
    calc
      _ = inverseFrequencyRoot N * (finiteSquare N z * finiteSection N z) *
        inverseFrequencyRoot N := by
          have h := (root_units N).1
          calc
            _ = inverseFrequencyRoot N * finiteSquare N z *
              (frequencyRoot N * inverseFrequencyRoot N) * finiteSection N z *
                inverseFrequencyRoot N := by noncomm_ring
            _ = _ := by rw [h, mul_one]; noncomm_ring
      _ = _ := by rw [finiteSquare_commutes N hz]
  · rw [← Matrix.mul_kronecker_mul, one_mul]
    congr 1
    calc
      _ = frequencyRoot N * (finiteSquare N z * finiteSection N z) * frequencyRoot N := by
        calc
          _ = frequencyRoot N * finiteSquare N z *
            (inverseFrequencyRoot N * frequencyRoot N) * finiteSection N z *
              frequencyRoot N := by noncomm_ring
          _ = _ := by rw [(root_units N).2, mul_one]; noncomm_ring
      _ = _ := by rw [finiteSquare_commutes N hz]

private lemma right_external_block (D : LatticeData) (N : ℕ)
    {X : Type*} [Fintype X] [DecidableEq X] (e : X → External D) (z : ℂ) :
    (rightRow D N e z).submatrix Sum.inr Sum.inr =
      (leftRow D N e z).submatrix Sum.inr Sum.inr := by
  ext x y
  simp [rightRow, leftRow, damp, transportCovariance, sourceBlock,
    Fintype.sum_sum_type, Matrix.one_apply, mul_ite, ite_mul, eq_comm]

private lemma original_right_block (D : LatticeData) (hu : IsUnit D.G.det) (N : ℕ)
    {X : Type*} [Fintype X] [DecidableEq X] (e : X → External D)
    {z : ℂ} (hz : ‖z‖ < 1) (x y : X) :
    originalEffectiveKernel D N e z (.inr x) (.inr y) =
      leftRow D N e z (.inr x) (.inr y) +
        (gramComplex D) (e x).2.1 (e y).2.1 * finitePair D N e z (finiteOdd N z) x y := by
  classical
  unfold originalEffectiveKernel FiniteGaussianSewing.effectiveKernel
  rw [Matrix.fromBlocks_apply₂₂, Matrix.add_apply,
    show ((rightRow D N e z).submatrix Sum.inr Sum.inr) x y =
        leftRow D N e z (.inr x) (.inr y) from
      congrArg (fun M => M x y) (right_external_block D N e z)]
  congr 1
  rw [Matrix.mul_assoc
    (((rightRow D N e z).submatrix Sum.inl Sum.inr).transpose)
    (Ring.inverse (1 - (leftRow D N e z).submatrix Sum.inl Sum.inl *
      (rightRow D N e z).submatrix Sum.inl Sum.inl))
    ((leftRow D N e z).submatrix Sum.inl Sum.inl),
    (internal_inverse_times_source D hu N e hz).2]
  have hQ (i j : Internal D N) :
      ((gramComplex D) ⊗ₖ (frequencyRoot N * finiteOdd N z * frequencyRoot N)) i j =
      (gramComplex D) i.1 j.1 *
        ((Real.sqrt (i.2.val + 1 : ℝ) : ℂ) * finiteOdd N z i.2 j.2 *
          (Real.sqrt (j.2.val + 1 : ℝ) : ℂ)) := by
    rw [Matrix.kroneckerMap_apply]
    simp only [frequencyRoot, Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
    original_inverse_mixed D hu, Fintype.sum_prod_type, Finset.sum_mul,
    Finset.mul_sum, hQ]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.sum_ite_irrel, Finset.mem_univ, ↓reduceIte,
    Finset.sum_const_zero, mul_one, one_mul]
  rw [finitePair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  field_simp [root_ne]
  <;> ring

private lemma sum_colour_frequency (D : LatticeData) (N : ℕ)
    (f : Fin D.rank → Fin N → Fin D.rank → Fin N → ℂ) :
    (∑ j, ∑ t, ∑ i, ∑ s, f i s j t) = ∑ t, ∑ s, ∑ j, ∑ i, f i s j t := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  calc
    _ = ∑ j, ∑ s, ∑ i, f i s j t := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

private lemma colour_contraction (D : LatticeData) (hu : IsUnit D.G.det)
    (a b : Fin D.rank) :
    (∑ j, ∑ i, (gramComplex D) i a * (gramComplex D)⁻¹ i j * (gramComplex D) j b) =
      (gramComplex D) a b := by
  have h : gramComplex D * (gramComplex D)⁻¹ * gramComplex D = gramComplex D := by
    rw [Matrix.mul_nonsing_inv _ (SignedOscillatorWick.complex_det_unit D hu), one_mul]
  have hc := congrArg (fun M => M a b) h
  simp only [Matrix.mul_apply, Finset.sum_mul] at hc
  convert hc using 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [show gramComplex D i a = gramComplex D a i from
    congrArg (fun M => M a i) (gram_symm D)]

private lemma original_left_block (D : LatticeData) (hu : IsUnit D.G.det) (N : ℕ)
    {X : Type*} [Fintype X] [DecidableEq X] (e : X → External D)
    {z : ℂ} (hz : ‖z‖ < 1) (x y : X) :
    originalEffectiveKernel D N e z (.inl x) (.inl y) =
      leftRow D N e z (.inr x) (.inr y) +
        (gramComplex D) (e x).2.1 (e y).2.1 * finitePair D N e z (finiteOdd N z) x y := by
  classical
  unfold originalEffectiveKernel FiniteGaussianSewing.effectiveKernel
  rw [Matrix.fromBlocks_apply₁₁]
  simp only [Matrix.add_apply, Matrix.submatrix_apply]
  congr 1
  rw [Matrix.mul_assoc ((leftRow D N e z).submatrix Sum.inr Sum.inl)
    (Ring.inverse (1 - (rightRow D N e z).submatrix Sum.inl Sum.inl *
      (leftRow D N e z).submatrix Sum.inl Sum.inl))
    ((rightRow D N e z).submatrix Sum.inl Sum.inl),
    (internal_inverse_times_source D hu N e hz).1]
  have hQ (i j : Internal D N) :
      ((gramComplex D)⁻¹ ⊗ₖ
        (inverseFrequencyRoot N * finiteOdd N z * inverseFrequencyRoot N)) i j =
      (gramComplex D)⁻¹ i.1 j.1 *
        ((Real.sqrt (i.2.val + 1 : ℝ) : ℂ)⁻¹ * finiteOdd N z i.2 j.2 *
          (Real.sqrt (j.2.val + 1 : ℝ) : ℂ)⁻¹) := by
    rw [Matrix.kroneckerMap_apply]
    simp only [inverseFrequencyRoot, Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
    original_mixed_transpose, original_mixed, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum, hQ]
  rw [sum_colour_frequency D N]
  rw [finitePair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  have hterm (i j : Fin D.rank) :
      ((Real.sqrt (s.val + 1 : ℝ) : ℂ) *
        externalColumn (e x).1 (e x).2.2 z s.val * gramComplex D i (e x).2.1 *
        ((gramComplex D)⁻¹ i j *
          ((Real.sqrt (s.val + 1 : ℝ) : ℂ)⁻¹ * finiteOdd N z s t *
            (Real.sqrt (t.val + 1 : ℝ) : ℂ)⁻¹))) *
          ((Real.sqrt (t.val + 1 : ℝ) : ℂ) *
            externalColumn (e y).1 (e y).2.2 z t.val * gramComplex D j (e y).2.1) =
      (externalColumn (e x).1 (e x).2.2 z s.val * finiteOdd N z s t *
        externalColumn (e y).1 (e y).2.2 z t.val) *
        (gramComplex D i (e x).2.1 * (gramComplex D)⁻¹ i j * gramComplex D j (e y).2.1) := by
    field_simp [root_ne]
    <;> ring
  simp_rw [hterm]
  simp_rw [← Finset.mul_sum]
  rw [colour_contraction D hu]
  ring

lemma cutoff_zeroExtend (N : ℕ) (out : Bool) (p : ℕ) (z : ℂ) :
    zeroExtend N (WithLp.toLp 2 (fun s : Fin N => externalColumn out p z s.val)) =
      externalCutoff N out p z := by
  classical
  ext n
  simp only [zeroExtend_apply, externalCutoff, lp.coeFn_sum, Finset.sum_apply,
    lp.single_apply, Pi.single_apply, PiLp.toLp_apply]
  by_cases hn : n < N <;> simp [Finset.mem_range, hn, eq_comm]

private lemma cutoff_pair (D : LatticeData) (N : ℕ) {X : Type*}
    (e : X → External D) (z : ℂ) (M : Matrix (Fin N) (Fin N) ℂ) (x y : X) :
    innerSL ℂ (star (externalCutoff N (e x).1 (e x).2.2 z))
      (zeroExtend N (WithLp.toLp 2 (M.mulVec
        (fun s : Fin N => externalColumn (e y).1 (e y).2.2 z s.val)))) =
      finitePair D N e z M x y := by
  have hcut : externalCutoff N (e x).1 (e x).2.2 z =
      ∑ s : Fin N, (lp.single 2 s.val (externalColumn (e x).1 (e x).2.2 z s.val) : H) :=
    Finset.sum_range _
  have hstar (s : Fin N) :
      star (lp.single 2 s.val (externalColumn (e x).1 (e x).2.2 z s.val) : H) =
        lp.single 2 s.val (star (externalColumn (e x).1 (e x).2.2 z s.val)) := by
    ext k
    simp only [lp.star_apply, lp.single_apply, Pi.single_apply]
    split_ifs <;> simp
  rw [hcut, innerSL_apply_apply, star_sum, sum_inner]
  simp_rw [hstar, lp.inner_single_left, RCLike.inner_apply', ← RCLike.star_def, star_star]
  simp only [zeroExtend_apply, dif_pos (Fin.isLt _), PiLp.toLp_apply,
    Matrix.mulVec, dotProduct]
  rw [finitePair, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

private lemma finitePair_square (D : LatticeData) (N : ℕ) {X : Type*}
    (e : X → External D) {z : ℂ} (hz : ‖z‖ < 1) (x y : X) :
    finitePair D N e z (finiteSquare N z) x y =
      innerSL ℂ (star (externalCutoff N (e x).1 (e x).2.2 z))
        ((∑' k : ℕ, (sectionOp N z ^ 2) ^ k)
          (externalCutoff N (e y).1 (e y).2.2 z)) := by
  rw [← cutoff_zeroExtend N (e y).1 (e y).2.2 z,
    OriginalGaussianDisplacement.zeroExtend_square_inverse N hz]
  exact (cutoff_pair D N e z (finiteSquare N z) x y).symm

private lemma finitePair_odd (D : LatticeData) (N : ℕ) {X : Type*}
    (e : X → External D) {z : ℂ} (hz : ‖z‖ < 1) (x y : X) :
    finitePair D N e z (finiteOdd N z) x y =
      innerSL ℂ (star (externalCutoff N (e x).1 (e x).2.2 z))
        ((sectionOp N z * (∑' k : ℕ, (sectionOp N z ^ 2) ^ k))
          (externalCutoff N (e y).1 (e y).2.2 z)) := by
  change _ = innerSL ℂ (star (externalCutoff N (e x).1 (e x).2.2 z))
    (sectionOp N z ((∑' k : ℕ, (sectionOp N z ^ 2) ^ k)
      (externalCutoff N (e y).1 (e y).2.2 z)))
  rw [← cutoff_zeroExtend N (e y).1 (e y).2.2 z,
    OriginalGaussianDisplacement.zeroExtend_square_inverse N hz,
    OriginalGaussianDisplacement.section_zeroExtend]
  simpa only [finiteOdd, finiteSquare, Matrix.mulVec_mulVec] using
    (cutoff_pair D N e z (finiteOdd N z) x y).symm

def externalFreeEntry (D : LatticeData) (a b : External D) : ℂ :=
  if a.1 = b.1 then 0 else
    if a.2.2 = b.2.2 then -((a.2.2 : ℂ) + 1 / 2) else 0

private lemma original_free_entry (D : LatticeData) (a b : External D) :
    correctedMatrix D (Function.Embedding.refl (Index D))
      (externalIndex D a) (externalIndex D b) =
      (gramComplex D) a.2.1 b.2.1 * externalFreeEntry D a b := by
  cases ha : a.1 <;> cases hb : b.1 <;>
    by_cases h : a.2.2 = b.2.2 <;>
    simp [externalIndex, ha, hb, externalFreeEntry, correctedMatrix, normalMatrix,
      OriginalNormalRowSource.IO, LatticeHalfFock.frequency, h, eq_comm, D.symmetric] <;> ring

private lemma finiteSquare_symm (N : ℕ) (z : ℂ) :
    (finiteSquare N z).transpose = finiteSquare N z := by
  simp only [finiteSquare, ← Matrix.nonsing_inv_eq_ringInverse, Matrix.transpose_nonsing_inv,
    Matrix.transpose_sub, Matrix.transpose_one, pow_two, Matrix.transpose_mul,
    OriginalGaussianDisplacement.section_symm]

private lemma finitePair_square_symm (D : LatticeData) (N : ℕ) {X : Type*}
    (e : X → External D) (z : ℂ) (x y : X) :
    finitePair D N e z (finiteSquare N z) x y =
      finitePair D N e z (finiteSquare N z) y x := by
  unfold finitePair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  have h : finiteSquare N z s t = finiteSquare N z t s :=
    congrArg (fun M => M t s) (finiteSquare_symm N z)
  rw [h]
  ring

private lemma original_lower_cross_block (D : LatticeData) (hu : IsUnit D.G.det)
    (N : ℕ) {X : Type*} [Fintype X] [DecidableEq X] (e : X → External D)
    {z : ℂ} (hz : ‖z‖ < 1) (x y : X) :
    originalEffectiveKernel D N e z (.inr x) (.inl y) =
      -(gramComplex D) (e y).2.1 (e x).2.1 * finitePair D N e z (finiteSquare N z) y x := by
  classical
  unfold originalEffectiveKernel FiniteGaussianSewing.effectiveKernel
  rw [Matrix.fromBlocks_apply₂₁, (original_internal_inverse_similarities D hu N e hz).2]
  have hQ (i j : Internal D N) :
      ((1 : Matrix (Fin D.rank) (Fin D.rank) ℂ) ⊗ₖ
        (frequencyRoot N * finiteSquare N z * inverseFrequencyRoot N)) i j =
      (if i.1 = j.1 then 1 else 0) *
        ((Real.sqrt (i.2.val + 1 : ℝ) : ℂ) * finiteSquare N z i.2 j.2 *
          (Real.sqrt (j.2.val + 1 : ℝ) : ℂ)⁻¹) := by
    rw [Matrix.kroneckerMap_apply]
    simp only [Matrix.one_apply, frequencyRoot, inverseFrequencyRoot,
      Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
    original_mixed_transpose, original_mixed, original_inverse_mixed D hu,
    Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum, hQ]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.sum_ite_irrel, Finset.mem_univ, ↓reduceIte,
    Finset.sum_const_zero, mul_one, one_mul]
  rw [← finitePair_square_symm D N e z x y, finitePair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [show gramComplex D (e x).2.1 (e y).2.1 = gramComplex D (e y).2.1 (e x).2.1 from
    congrArg (fun M => M (e y).2.1 (e x).2.1) (gram_symm D)]
  field_simp [root_ne]
  <;> ring

private def finiteEffectiveEntry (D : LatticeData) (N : ℕ) {X : Type*}
    (e : X → External D) (z : ℂ) : Matrix (X ⊕ X) (X ⊕ X) ℂ :=
  Matrix.fromBlocks
    (fun x y => gramComplex D (e x).2.1 (e y).2.1 *
      (externalFreeEntry D (e x) (e y) + finitePair D N e z (finiteOdd N z) x y))
    (fun x y => -gramComplex D (e x).2.1 (e y).2.1 *
      finitePair D N e z (finiteSquare N z) x y)
    (fun x y => -gramComplex D (e y).2.1 (e x).2.1 *
      finitePair D N e z (finiteSquare N z) y x)
    (fun x y => gramComplex D (e x).2.1 (e y).2.1 *
      (externalFreeEntry D (e x) (e y) + finitePair D N e z (finiteOdd N z) x y))

private lemma original_effectiveKernel_finite_blocks (D : LatticeData)
    (hu : IsUnit D.G.det) (N : ℕ) {X : Type*} [Fintype X] [DecidableEq X]
    (e : X → External D) {z : ℂ} (hz : ‖z‖ < 1) :
    originalEffectiveKernel D N e z = finiteEffectiveEntry D N e z := by
  ext (x | x) (y | y)
  · change originalEffectiveKernel D N e z (.inl x) (.inl y) =
      gramComplex D (e x).2.1 (e y).2.1 *
        (externalFreeEntry D (e x) (e y) + finitePair D N e z (finiteOdd N z) x y)
    rw [original_left_block D hu N e hz]
    change leftRow D N e z (.inr x) (.inr y) + _ = _
    simp only [leftRow, damp, originalRow, Matrix.submatrix_apply, rowIndex,
      original_free_entry, mul_one, one_mul, finiteEffectiveEntry, Matrix.fromBlocks_apply₁₁]
    ring
  · exact original_cross_block D hu N e hz x y
  · exact original_lower_cross_block D hu N e hz x y
  · change originalEffectiveKernel D N e z (.inr x) (.inr y) =
      gramComplex D (e x).2.1 (e y).2.1 *
        (externalFreeEntry D (e x) (e y) + finitePair D N e z (finiteOdd N z) x y)
    rw [original_right_block D hu N e hz]
    simp only [leftRow, damp, originalRow, Matrix.submatrix_apply, rowIndex,
      original_free_entry, mul_one, one_mul, finiteEffectiveEntry, Matrix.fromBlocks_apply₂₂]
    ring

lemma external_pair_error (u v x y : H) (A B : H →L[ℂ] H)
    {C : ℝ} (hC : 0 ≤ C) (hu : ‖u‖ ≤ C) (hy : ‖y‖ ≤ C)
    (hA : ‖A‖ ≤ C) (hB : ‖B‖ ≤ C) :
    ‖innerSL ℂ (star v) (B y) - innerSL ℂ (star u) (A x)‖ ≤
      C ^ 2 * (‖v - u‖ + ‖B - A‖ + ‖y - x‖) := by
  let b (s t : H) : ℂ := innerSL ℂ (star s) t
  have hb (s t : H) : ‖b s t‖ ≤ ‖s‖ * ‖t‖ := by
    simpa only [b, innerSL_apply_apply, norm_star] using
      norm_inner_le_norm (𝕜 := ℂ) (star s) t
  have he : b v (B y) - b u (A x) =
      b (v - u) (B y) + b u ((B - A) y) + b u (A (y - x)) := by
    simp only [b, innerSL_apply_apply, star_sub, inner_sub_left, inner_sub_right,
      ContinuousLinearMap.sub_apply, map_sub]
    ring
  change ‖b v (B y) - b u (A x)‖ ≤ _
  rw [he]
  calc
    _ ≤ (‖b (v - u) (B y)‖ + ‖b u ((B - A) y)‖) + ‖b u (A (y - x))‖ :=
      (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ ≤ ‖v - u‖ * (‖B‖ * ‖y‖) + ‖u‖ * (‖B - A‖ * ‖y‖) +
        ‖u‖ * (‖A‖ * ‖y - x‖) := by
      gcongr
      · exact (hb _ _).trans (mul_le_mul_of_nonneg_left (B.le_opNorm _) (norm_nonneg _))
      · exact (hb _ _).trans (mul_le_mul_of_nonneg_left ((B - A).le_opNorm _) (norm_nonneg _))
      · exact (hb _ _).trans (mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _))
    _ ≤ ‖v - u‖ * (C * C) + C * (‖B - A‖ * C) + C * (C * ‖y - x‖) := by gcongr
    _ = _ := by ring

private lemma external_pair_uniform {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (out : Bool) (p : ℕ) (out' : Bool) (q : ℕ)
    (F : ℕ → ℂ → H →L[ℂ] H) (A : ℂ → H →L[ℂ] H) (M : ℝ)
    (hbound : ∀ N z, ‖z‖ ≤ ρ → ‖F N z‖ ≤ M ∧ ‖A z‖ ≤ M)
    (hF : TendstoUniformlyOn F A atTop {z : ℂ | ‖z‖ ≤ ρ}) :
    TendstoUniformlyOn
      (fun N z => innerSL ℂ (star (externalCutoff N out p z))
        (F N z (externalCutoff N out' q z)))
      (fun z => innerSL ℂ (star (externalVector out p z)) (A z (externalVector out' q z)))
      atTop {z : ℂ | ‖z‖ ≤ ρ} := by
  let C := max 1 (max (externalMass p ρ) (max (externalMass q ρ) M))
  have hC : 1 ≤ C := le_max_left _ _
  have hpC : externalMass p ρ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hqC : externalMass q ρ ≤ C := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hMC : M ≤ C := (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hpu := externalCutoff_control hρ hρ1 out p
  have hqu := externalCutoff_control hρ hρ1 out' q
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let δ := ε / (3 * C ^ 2 + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  filter_upwards [Metric.tendstoUniformly_iff.mp hpu.2 δ hδ,
    Metric.tendstoUniformly_iff.mp hqu.2 δ hδ,
    Metric.tendstoUniformlyOn_iff.mp hF δ hδ] with N hN hN' hNF
  intro z hz
  have hu := hpu.1 z hz
  have hw := hqu.1 z hz
  have hb := hbound N z hz
  have he := external_pair_error (externalVector out p z) (externalCutoff N out p z)
    (externalVector out' q z) (externalCutoff N out' q z) (A z) (F N z)
    (zero_le_one.trans hC) (hu.1.trans hpC) ((hw.2 N).trans hqC)
    (hb.2.trans hMC) (hb.1.trans hMC)
  have h1 := hN ⟨z, hz⟩
  have h2 := hN' ⟨z, hz⟩
  have h3 := hNF z hz
  rw [dist_comm, dist_eq_norm] at h1 h2 h3 ⊢
  apply he.trans_lt
  have hCp : 0 < C ^ 2 := sq_pos_of_pos (zero_lt_one.trans_le hC)
  calc
    _ < C ^ 2 * (3 * δ) := mul_lt_mul_of_pos_left (by linarith) hCp
    _ < ε := by
      dsimp [δ]
      rw [show C ^ 2 * (3 * (ε / (3 * C ^ 2 + 1))) =
        (3 * C ^ 2 * ε) / (3 * C ^ 2 + 1) by ring]
      exact (div_lt_iff₀ (by positivity : 0 < 3 * C ^ 2 + 1)).mpr (by nlinarith)

private lemma square_control {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    {z : ℂ} (hz : ‖z‖ ≤ ρ) (N : ℕ) :
    ‖(∑' k : ℕ, (sectionOp N z ^ 2) ^ k)‖ ≤ (1 - ρ ^ 4)⁻¹ ∧
      ‖squareResolvent z‖ ≤ (1 - ρ ^ 4)⁻¹ := by
  have hq := pow_lt_one₀ hρ hρ1 (by norm_num : (4 : ℕ) ≠ 0)
  have hb (A : H →L[ℂ] H) (hA : ‖A‖ ≤ ρ ^ 2) : ‖A ^ 2‖ ≤ ρ ^ 4 := by
    calc
      _ ≤ ‖A‖ ^ 2 := norm_pow_le _ _
      _ ≤ (ρ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hA 2
      _ = _ := by ring
  exact ⟨traceNeumann_norm_le (by positivity) hq
      (hb _ ((sectionOp_norm_le N (hz.trans_lt hρ1)).trans
        (pow_le_pow_left₀ (norm_nonneg _) hz 2))),
    traceNeumann_norm_le (by positivity) hq
      (hb _ ((operator_norm_le (hz.trans_lt hρ1)).trans
        (pow_le_pow_left₀ (norm_nonneg _) hz 2)))⟩

private lemma odd_control {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    (∀ N z, ‖z‖ ≤ ρ →
      ‖sectionOp N z * (∑' k : ℕ, (sectionOp N z ^ 2) ^ k)‖ ≤ (1 - ρ ^ 4)⁻¹ ∧
        ‖oddResolvent z‖ ≤ (1 - ρ ^ 4)⁻¹) ∧
    TendstoUniformlyOn
      (fun N z => sectionOp N z * (∑' k : ℕ, (sectionOp N z ^ 2) ^ k))
      oddResolvent atTop {z : ℂ | ‖z‖ ≤ ρ} := by
  have hq : ρ ^ 2 ≤ 1 := pow_le_one₀ hρ hρ1.le
  have hM : 0 ≤ (1 - ρ ^ 4)⁻¹ := inv_nonneg.mpr
    (sub_nonneg.mpr (pow_le_one₀ hρ hρ1.le))
  have hb N z (hz : ‖z‖ ≤ ρ) : ‖sectionOp N z‖ ≤ ρ ^ 2 ∧ ‖operator z‖ ≤ ρ ^ 2 :=
    ⟨(sectionOp_norm_le N (hz.trans_lt hρ1)).trans (pow_le_pow_left₀ (norm_nonneg _) hz 2),
      (operator_norm_le (hz.trans_lt hρ1)).trans (pow_le_pow_left₀ (norm_nonneg _) hz 2)⟩
  constructor
  · intro N z hz
    have ht := square_control hρ hρ1 hz N
    exact ⟨(norm_mul_le _ _).trans ((mul_le_mul (hb N z hz).1 ht.1 (norm_nonneg _) (by positivity)).trans
      (mul_le_of_le_one_left hM hq)),
      (norm_mul_le _ _).trans ((mul_le_mul (hb N z hz).2 ht.2 (norm_nonneg _) (by positivity)).trans
        (mul_le_of_le_one_left hM hq))⟩
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    let δ := ε / ((1 - ρ ^ 4)⁻¹ + 2)
    have hδ : 0 < δ := div_pos hε (by positivity)
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (sectionOp_tendstoUniformlyOn hρ hρ1) δ hδ,
      Metric.tendstoUniformlyOn_iff.mp (sectionSquareResolvent_tendstoUniformlyOn hρ hρ1) δ hδ]
      with N hK hT
    intro z hz
    have hk := hK z hz
    have ht := hT z hz
    rw [dist_comm, dist_eq_norm] at hk ht ⊢
    have he : sectionOp N z * (∑' k : ℕ, (sectionOp N z ^ 2) ^ k) - oddResolvent z =
        (sectionOp N z - operator z) * (∑' k : ℕ, (sectionOp N z ^ 2) ^ k) +
          operator z * ((∑' k : ℕ, (sectionOp N z ^ 2) ^ k) - squareResolvent z) := by
      unfold oddResolvent
      noncomm_ring
    rw [he]
    calc
      _ ≤ ‖sectionOp N z - operator z‖ * (1 - ρ ^ 4)⁻¹ +
          ‖(∑' k : ℕ, (sectionOp N z ^ 2) ^ k) - squareResolvent z‖ := by
        apply (norm_add_le _ _).trans
        apply add_le_add
        · exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_left (square_control hρ hρ1 hz N).1 (norm_nonneg _))
        · exact (norm_mul_le _ _).trans
            (mul_le_of_le_one_left (norm_nonneg _) ((hb N z hz).2.trans hq))
      _ < δ * (1 - ρ ^ 4)⁻¹ + δ := add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_right hk.le hM) ht
      _ < ε := by
        dsimp [δ]
        rw [show ε / ((1 - ρ ^ 4)⁻¹ + 2) * (1 - ρ ^ 4)⁻¹ +
            ε / ((1 - ρ ^ 4)⁻¹ + 2) =
            (ε * ((1 - ρ ^ 4)⁻¹ + 1)) / ((1 - ρ ^ 4)⁻¹ + 2) by ring]
        exact (div_lt_iff₀ (by positivity : 0 < (1 - ρ ^ 4)⁻¹ + 2)).mpr (by nlinarith)

/-- Explicit original external covariance, with the full identity contribution
in the cross block and ordinary bilinear transposes. -/
def explicitEffectiveKernel (D : LatticeData) {X : Type*} (e : X → External D)
    (z : ℂ) : Matrix (X ⊕ X) (X ⊕ X) ℂ :=
  Matrix.fromBlocks
    (fun x y => gramComplex D (e x).2.1 (e y).2.1 *
      (externalFreeEntry D (e x) (e y) + externalJ (e x).1 (e x).2.2 (e y).1 (e y).2.2 z))
    (fun x y => -gramComplex D (e x).2.1 (e y).2.1 *
      externalT (e x).1 (e x).2.2 (e y).1 (e y).2.2 z)
    (fun x y => -gramComplex D (e y).2.1 (e x).2.1 *
      externalT (e y).1 (e y).2.2 (e x).1 (e x).2.2 z)
    (fun x y => gramComplex D (e x).2.1 (e y).2.1 *
      (externalFreeEntry D (e x) (e y) + externalJ (e x).1 (e x).2.2 (e y).1 (e y).2.2 z))

/-- All entries of the actual finite external effective covariance converge
locally uniformly to explicit absolutely summable scalar series. -/
theorem original_effectiveKernel_blocks_tendsto_explicit (D : LatticeData)
    (hu : IsUnit D.G.det) {X : Type*} [Fintype X] [DecidableEq X]
    (e : X → External D) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (a b : X ⊕ X) :
    TendstoUniformlyOn (fun N z => originalEffectiveKernel D N e z a b)
      (fun z => explicitEffectiveKernel D e z a b) atTop {z : ℂ | ‖z‖ ≤ ρ} := by
  have hJ (x y : X) := external_pair_uniform hρ hρ1 (e x).1 (e x).2.2 (e y).1 (e y).2.2
    _ _ _ (odd_control hρ hρ1).1 (odd_control hρ hρ1).2
  have hT (x y : X) := external_pair_uniform hρ hρ1 (e x).1 (e x).2.2 (e y).1 (e y).2.2
    _ _ _ (fun N z hz => square_control hρ hρ1 hz N) (sectionSquareResolvent_tendstoUniformlyOn hρ hρ1)
  have hj (x y : X) : TendstoUniformlyOn (fun N z => finitePair D N e z (finiteOdd N z) x y)
      (fun z => externalJ (e x).1 (e x).2.2 (e y).1 (e y).2.2 z) atTop {z : ℂ | ‖z‖ ≤ ρ} := by
    exact ((hJ x y).congr (Eventually.of_forall (fun N z hz =>
      (finitePair_odd D N e (hz.trans_lt hρ1) x y).symm))).congr_right
      (fun z hz => (external_contractions_explicit _ _ _ _ (hz.trans_lt hρ1)).2.2.1)
  have ht (x y : X) : TendstoUniformlyOn (fun N z => finitePair D N e z (finiteSquare N z) x y)
      (fun z => externalT (e x).1 (e x).2.2 (e y).1 (e y).2.2 z) atTop {z : ℂ | ‖z‖ ≤ ρ} := by
    exact ((hT x y).congr (Eventually.of_forall (fun N z hz =>
      (finitePair_square D N e (hz.trans_lt hρ1) x y).symm))).congr_right
      (fun z hz => (external_contractions_explicit _ _ _ _ (hz.trans_lt hρ1)).2.2.2.1)
  have hfinite : TendstoUniformlyOn (fun N z => finiteEffectiveEntry D N e z a b)
      (fun z => explicitEffectiveKernel D e z a b) atTop {z : ℂ | ‖z‖ ≤ ρ} := by
    rcases a with x | x <;> rcases b with y | y
    · exact (uniformContinuous_const_smul (gramComplex D (e x).2.1 (e y).2.1)).comp_tendstoUniformlyOn
        ((uniformContinuous_const.add uniformContinuous_id).comp_tendstoUniformlyOn (hj x y))
    · exact (uniformContinuous_const_smul (-gramComplex D (e x).2.1 (e y).2.1)).comp_tendstoUniformlyOn (ht x y)
    · exact (uniformContinuous_const_smul (-gramComplex D (e y).2.1 (e x).2.1)).comp_tendstoUniformlyOn (ht y x)
    · exact (uniformContinuous_const_smul (gramComplex D (e x).2.1 (e y).2.1)).comp_tendstoUniformlyOn
        ((uniformContinuous_const.add uniformContinuous_id).comp_tendstoUniformlyOn (hj x y))
  exact hfinite.congr (Eventually.of_forall (fun N z hz => congrArg (fun M => M a b)
    (original_effectiveKernel_finite_blocks D hu N e (hz.trans_lt hρ1)).symm))

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks
