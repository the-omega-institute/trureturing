/- GID: D5/S3/Quantum/Entanglement/Witness/LiPoonSzeP2
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/LiPoonSzeP2
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Strict elementary-symmetric realignment separation in unequal local dimensions. -/

import D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound
import D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormCovariance
import D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Analysis.Matrix.Order
import D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks

/-! The rectangular comparison problem for elementary symmetric realignment spectra.

admission_basis: open-problem-resolution (#30506; Proved).
The terminal conclusion combines the sharp separable tail bound with three
explicit density-matrix spectra and retains the actual complex matrix predicates. -/

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.style.longLine false
noncomputable section

open Matrix
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open scoped BigOperators
open D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
open D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence (IsSeparable)

open scoped MatrixOrder ComplexOrder

namespace D5.S3.Quantum.Entanglement.Witness.LiPoonSzeP2

/-- Bob's occupied tensor-product block and its unused orthogonal complement. -/
private abbrev BobBlock (m q r : ℕ) := (Fin m × Fin q) ⊕ Fin r
/-- A factor whose columns are the unnormalized maximally entangled vectors
in the `q` orthogonal multiplicity sectors. -/
private def entangledFactor (m q r : ℕ) :
    Matrix (Fin m × BobBlock m q r) (Fin q) ℂ :=
  fun ⟨i, a⟩ h => match a with
    | .inl ⟨j, p⟩ => if i = j ∧ p = h then 1 else 0
    | .inr _ => 0
/-- The positive entangled block in the LPS construction. -/
private def entangledBlock (m q r : ℕ) :
    Matrix (Fin m × BobBlock m q r) (Fin m × BobBlock m q r) ℂ :=
  entangledFactor m q r * (entangledFactor m q r)ᴴ
/-- Independent scalar weights on the occupied and unused Bob subspaces. -/
private def blockDiagonal (m q r : ℕ) (u v : ℝ) :
    Matrix (Fin m × BobBlock m q r) (Fin m × BobBlock m q r) ℂ :=
  Matrix.diagonal fun ⟨_, a⟩ => match a with
    | .inl _ => (u : ℂ)
    | .inr _ => (v : ℂ)
/-- The LPS block family, before identifying Bob's coordinates with `Fin n`. -/
private def blockState (m q r : ℕ) (t u v : ℝ) :
    Matrix (Fin m × BobBlock m q r) (Fin m × BobBlock m q r) ℂ :=
  t • entangledBlock m q r + blockDiagonal m q r u v
private lemma entangledBlock_posSemidef (m q r : ℕ) :
    (entangledBlock m q r).PosSemidef := by
  exact Matrix.posSemidef_self_mul_conjTranspose _
private lemma blockDiagonal_posSemidef (m q r : ℕ) {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (blockDiagonal m q r u v).PosSemidef := by
  rw [blockDiagonal, Matrix.posSemidef_diagonal_iff]
  rintro ⟨i, a | a⟩
  · change (0 : ℂ) ≤ (u : ℂ)
    exact RCLike.ofReal_nonneg.mpr hu
  · change (0 : ℂ) ≤ (v : ℂ)
    exact RCLike.ofReal_nonneg.mpr hv
private lemma blockState_posSemidef (m q r : ℕ) {t u v : ℝ}
    (ht : 0 ≤ t) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (blockState m q r t u v).PosSemidef := by
  exact ((entangledBlock_posSemidef m q r).smul ht).add
    (blockDiagonal_posSemidef m q r hu hv)
private lemma entangledBlock_inl (m q r : ℕ) (i j a b : Fin m) (p s : Fin q) :
    entangledBlock m q r (i, .inl (a,p)) (j, .inl (b,s)) =
      if i = a ∧ j = b ∧ p = s then 1 else 0 := by
  classical
  by_cases hi : i = a <;> by_cases hj : j = b
  · subst a; subst b
    simp [entangledBlock, entangledFactor, Matrix.mul_apply, Matrix.conjTranspose_apply,
      ite_mul, mul_ite, eq_comm]
  · simp [entangledBlock, entangledFactor, Matrix.mul_apply, Matrix.conjTranspose_apply, hj]
  · simp [entangledBlock, entangledFactor, Matrix.mul_apply, Matrix.conjTranspose_apply, hi]
  · simp [entangledBlock, entangledFactor, Matrix.mul_apply, Matrix.conjTranspose_apply, hi]
@[simp] private lemma entangledBlock_inr_left (m q r : ℕ) (i j : Fin m)
    (a : Fin r) (b : BobBlock m q r) :
    entangledBlock m q r (i, .inr a) (j,b) = 0 := by
  simp [entangledBlock, entangledFactor, Matrix.mul_apply]
@[simp] private lemma entangledBlock_inr_right (m q r : ℕ) (i j : Fin m)
    (a : BobBlock m q r) (b : Fin r) :
    entangledBlock m q r (i,a) (j, .inr b) = 0 := by
  simp [entangledBlock, entangledFactor, Matrix.mul_apply, Matrix.conjTranspose_apply]
private lemma entangledBlock_trace (m q r : ℕ) :
    Matrix.trace (entangledBlock m q r) = (m * q : ℕ) := by
  classical
  simp [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fintype.sum_sum_type,
    entangledBlock_inl, Finset.sum_ite_eq, eq_comm]
private lemma blockDiagonal_trace (m q r : ℕ) (u v : ℝ) :
    Matrix.trace (blockDiagonal m q r u v) =
      ((m ^ 2 * q : ℕ) : ℂ) * u + ((m * r : ℕ) : ℂ) * v := by
  simp [blockDiagonal, Matrix.trace, Matrix.diag, Fintype.sum_prod_type,
    Fintype.sum_sum_type, pow_two]
  ring
private lemma blockState_trace (m q r : ℕ) (t u v : ℝ) :
    Matrix.trace (blockState m q r t u v) =
      (((t * m * q + u * m ^ 2 * q + v * m * r : ℝ)) : ℂ) := by
  rw [blockState, Matrix.trace_add, Matrix.trace_smul,
    entangledBlock_trace, blockDiagonal_trace]
  simp only [Complex.real_smul, Nat.cast_mul, Nat.cast_pow, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_pow]
  ring
/-- A nonnegative normalized LPS block family is a genuine density matrix. -/
private theorem blockState_isDensity (m q r : ℕ) {t u v : ℝ}
    (ht : 0 ≤ t) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (htrace : t * m * q + u * m ^ 2 * q + v * m * r = 1) :
    IsDensity (blockState m q r t u v) := by
  exact ⟨blockState_posSemidef m q r ht hu hv, by rw [blockState_trace, htrace]; rfl⟩
private lemma realign_blockState_inl (m q r : ℕ) (t u v : ℝ)
    (i j a b : Fin m) (p s : Fin q) :
    realign (blockState m q r t u v) (i,j) (.inl (a,p), .inl (b,s)) =
      if p = s then
        (t : ℂ) * (if i = a ∧ j = b then 1 else 0) +
          (u : ℂ) * (if i = j ∧ a = b then 1 else 0)
      else 0 := by
  classical
  by_cases hp : p = s <;> by_cases hi : i = a <;> by_cases hj : j = b <;>
    by_cases hij : i = j <;> by_cases hab : a = b <;>
    simp [realign, blockState, blockDiagonal, entangledBlock_inl,
      Matrix.diagonal_apply, Matrix.smul_apply, Complex.real_smul,
      hp, hi, hj, hij, hab]
@[simp] private lemma realign_blockState_inl_inr (m q r : ℕ) (t u v : ℝ)
    (i j a : Fin m) (p : Fin q) (b : Fin r) :
    realign (blockState m q r t u v) (i,j) (.inl (a,p), .inr b) = 0 := by
  simp [realign, blockState, blockDiagonal, Matrix.diagonal_apply]
@[simp] private lemma realign_blockState_inr_inl (m q r : ℕ) (t u v : ℝ)
    (i j b : Fin m) (p : Fin q) (a : Fin r) :
    realign (blockState m q r t u v) (i,j) (.inr a, .inl (b,p)) = 0 := by
  simp [realign, blockState, blockDiagonal, Matrix.diagonal_apply]
private lemma realign_blockState_inr (m q r : ℕ) (t u v : ℝ)
    (i j : Fin m) (a b : Fin r) :
    realign (blockState m q r t u v) (i,j) (.inr a, .inr b) =
      (v : ℂ) * (if i = j ∧ a = b then 1 else 0) := by
  classical
  by_cases hi : i = j <;> by_cases ha : a = b <;>
    simp [realign, blockState, blockDiagonal, Matrix.diagonal_apply, hi, ha]
private lemma active_row_inner (m : ℕ) (t u : ℝ) (i j k l : Fin m) :
    (∑ a : Fin m, ∑ b : Fin m,
      ((t : ℂ) * (if i = a ∧ j = b then 1 else 0) +
        (u : ℂ) * (if i = j ∧ a = b then 1 else 0)) *
      ((t : ℂ) * (if k = a ∧ l = b then 1 else 0) +
        (u : ℂ) * (if k = l ∧ a = b then 1 else 0))) =
      (t : ℂ)^2 * (if i = k ∧ j = l then 1 else 0) +
      (2 * (t : ℂ) * u + m * (u : ℂ)^2) *
        (if i = j ∧ k = l then 1 else 0) := by
  classical
  by_cases hij : i = j <;> by_cases hkl : k = l <;>
    by_cases hik : i = k <;> by_cases hjl : j = l <;>
    simp_all [ite_and, mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
      Finset.sum_mul, ite_mul, mul_ite, eq_comm] <;> ring
private lemma active_row_product (m q r : ℕ) (t u v : ℝ)
    (i j k l a b : Fin m) (p s : Fin q) :
    realign (blockState m q r t u v) (i,j) (.inl (a,p), .inl (b,s)) *
      star (realign (blockState m q r t u v) (k,l) (.inl (a,p), .inl (b,s))) =
      if p = s then
        ((t : ℂ) * (if i = a ∧ j = b then 1 else 0) +
          (u : ℂ) * (if i = j ∧ a = b then 1 else 0)) *
        ((t : ℂ) * (if k = a ∧ l = b then 1 else 0) +
          (u : ℂ) * (if k = l ∧ a = b then 1 else 0)) else 0 := by
  classical
  have hs : star ((t : ℂ) * (if k = a ∧ l = b then 1 else 0) +
      (u : ℂ) * (if k = l ∧ a = b then 1 else 0)) =
      ((t : ℂ) * (if k = a ∧ l = b then 1 else 0) +
      (u : ℂ) * (if k = l ∧ a = b then 1 else 0)) := by
    split_ifs <;> simp [Complex.star_def]
  by_cases h : p = s
  · simp only [realign_blockState_inl, h, ite_true, hs]
  · simp [realign_blockState_inl, h]
private lemma inactive_row_product (m q r : ℕ) (t u v : ℝ)
    (i j k l : Fin m) (a b : Fin r) :
    realign (blockState m q r t u v) (i,j) (.inr a, .inr b) *
      star (realign (blockState m q r t u v) (k,l) (.inr a, .inr b)) =
      if i = j ∧ k = l then (if a = b then (v : ℂ)^2 else 0) else 0 := by
  classical
  by_cases hij : i = j <;> by_cases hkl : k = l <;> by_cases hab : a = b <;>
    simp [realign_blockState_inr, hij, hkl, hab, Complex.star_def, pow_two]
/-- The row Gram matrix of the realignment is scalar plus a rank-one
identity-direction term, including every remainder coordinate. -/
private theorem blockState_realign_gram (m q r : ℕ) (t u v : ℝ) :
    let A := realign (blockState m q r t u v)
    A * Aᴴ = ((q : ℝ) * t ^ 2) • (1 : Matrix (Fin m × Fin m) (Fin m × Fin m) ℂ) +
      ((q : ℝ) * (2 * t * u + m * u ^ 2) + r * v ^ 2) •
        Matrix.vecMulVec
          (fun p : Fin m × Fin m => if p.1 = p.2 then (1 : ℂ) else 0)
          (fun p : Fin m × Fin m => if p.1 = p.2 then (1 : ℂ) else 0) := by
  classical
  dsimp only
  ext ⟨i,j⟩ ⟨k,l⟩
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.vecMulVec_apply, Complex.real_smul]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Fintype.sum_sum_type]
  simp only [realign_blockState_inl_inr, realign_blockState_inr_inl,
    zero_mul, mul_zero, map_zero, Finset.sum_const_zero, add_zero, zero_add]
  simp only [active_row_product, inactive_row_product, Finset.sum_ite_irrel,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul, Fintype.card_fin]
  rw [← Finset.mul_sum]
  rw [active_row_inner]
  by_cases hij : i = j <;> by_cases hkl : k = l <;>
    by_cases hik : i = k <;> by_cases hjl : j = l <;>
    simp_all [Matrix.one_apply, Matrix.vecMulVec, Matrix.smul_apply,
      Complex.real_smul, Nat.cast_mul, Nat.cast_add, Complex.ofReal_mul,
      Complex.ofReal_add, Complex.ofReal_pow] <;> ring
/-- Reindexing Bob's orthonormal coordinates to the prescribed finite type. -/
private def blockStateOnFin (m q r n : ℕ) (h : m * q + r = n) (t u v : ℝ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  let e : BobBlock m q r ≃ Fin n := Fintype.equivOfCardEq (by simp [BobBlock, h])
  let f := (Equiv.refl (Fin m)).prodCongr e
  (blockState m q r t u v).submatrix f.symm f.symm
private theorem blockStateOnFin_isDensity (m q r n : ℕ) (h : m * q + r = n)
    {t u v : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (htrace : t * m * q + u * m ^ 2 * q + v * m * r = 1) :
    IsDensity (blockStateOnFin m q r n h t u v) := by
  let e : BobBlock m q r ≃ Fin n := Fintype.equivOfCardEq (by simp [BobBlock, h])
  let f := (Equiv.refl (Fin m)).prodCongr e
  obtain ⟨hp, ht⟩ := blockState_isDensity m q r ht hu hv htrace
  refine ⟨hp.submatrix f.symm, ?_⟩
  change (∑ i, blockState m q r t u v (f.symm i) (f.symm i)) = 1
  exact (Equiv.sum_comp f.symm (fun i => blockState m q r t u v i i)).trans ht
private theorem blockStateOnFin_realign_gram (m q r n : ℕ) (h : m * q + r = n)
    (t u v : ℝ) :
    let A := realign (blockStateOnFin m q r n h t u v)
    A * Aᴴ = ((q : ℝ) * t ^ 2) • (1 : Matrix (Fin m × Fin m) (Fin m × Fin m) ℂ) +
      ((q : ℝ) * (2 * t * u + m * u ^ 2) + r * v ^ 2) •
        Matrix.vecMulVec
          (fun p : Fin m × Fin m => if p.1 = p.2 then (1 : ℂ) else 0)
          (fun p : Fin m × Fin m => if p.1 = p.2 then (1 : ℂ) else 0) := by
  let e : BobBlock m q r ≃ Fin n := Fintype.equivOfCardEq (by simp [BobBlock, h])
  let g := e.symm.prodCongr e.symm
  let R := realign (blockState m q r t u v)
  change R.submatrix id g * Rᴴ.submatrix g id = _
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  exact blockState_realign_gram m q r t u v
/-- The main LPS family with specified first and repeated singular values. -/
private def lpsState (m q r n : ℕ) (h : m * q + r = n) (a b : ℝ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  blockStateOnFin m q r n h (b / Real.sqrt q)
    (a ^ 2 - b / (m * Real.sqrt q)) (a ^ 2)
private lemma lps_t_add_mu (m q : ℕ) (hm : 0 < m) (hq : 0 < q) (a b : ℝ) :
    b / Real.sqrt q + m * (a ^ 2 - b / (m * Real.sqrt q)) = m * a ^ 2 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hq0 : Real.sqrt (q : ℝ) ≠ 0 := by positivity
  field_simp [hm0, hq0]
  <;> ring
private lemma lps_trace_normalization (m q r n : ℕ) (hm : 0 < m) (hq : 0 < q)
    (h : m * q + r = n) (a b : ℝ) (ha : a ^ 2 * m * n = 1) :
    (b / Real.sqrt q) * m * q +
      (a ^ 2 - b / (m * Real.sqrt q)) * m ^ 2 * q + a ^ 2 * m * r = 1 := by
  have hn : (m : ℝ) * q + r = n := by exact_mod_cast h
  calc
    _ = (m : ℝ) * q * (b / Real.sqrt q + m *
        (a ^ 2 - b / (m * Real.sqrt q))) + a ^ 2 * m * r := by ring
    _ = a ^ 2 * m * n := by rw [lps_t_add_mu m q hm hq, ← hn]; ring
    _ = 1 := ha
private theorem lpsState_isDensity (m q r n : ℕ) (hm : 0 < m) (hq : 0 < q)
    (h : m * q + r = n) (a b : ℝ) (hb : 0 ≤ b)
    (hu : 0 ≤ a ^ 2 - b / (m * Real.sqrt q)) (ha : a ^ 2 * m * n = 1) :
    IsDensity (lpsState m q r n h a b) := by
  apply blockStateOnFin_isDensity
  · exact div_nonneg hb (Real.sqrt_nonneg _)
  · exact hu
  · exact sq_nonneg _
  · exact lps_trace_normalization m q r n hm hq h a b ha
private lemma lps_repeated_gram_value (q : ℕ) (hq : 0 < q) (b : ℝ) :
    (q : ℝ) * (b / Real.sqrt q) ^ 2 = b ^ 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ q by positivity)
  have hq0 : Real.sqrt (q : ℝ) ≠ 0 := by positivity
  field_simp [hq0]
  nlinarith
private lemma lps_distinguished_gram_value (m q r n : ℕ) (hm : 0 < m) (hq : 0 < q)
    (h : m * q + r = n) (a b : ℝ) (ha : a ^ 2 * m * n = 1) :
    (q : ℝ) * (b / Real.sqrt q) ^ 2 +
      m * (q * (2 * (b / Real.sqrt q) * (a ^ 2 - b / (m * Real.sqrt q)) +
          m * (a ^ 2 - b / (m * Real.sqrt q)) ^ 2) + r * (a ^ 2) ^ 2) = a ^ 2 := by
  have hn : (m : ℝ) * q + r = n := by exact_mod_cast h
  calc
    _ = (q : ℝ) * (b / Real.sqrt q + m *
        (a ^ 2 - b / (m * Real.sqrt q))) ^ 2 + m * r * (a ^ 2) ^ 2 := by ring
    _ = a ^ 2 * (a ^ 2 * m * n) := by rw [lps_t_add_mu m q hm hq, ← hn]; ring
    _ = a ^ 2 := by rw [ha, mul_one]
/-- The supported LPS family assigns zero weight to the unused Bob space. -/
private def supportedState (m q r n : ℕ) (h : m * q + r = n) (a b : ℝ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  blockStateOnFin m q r n h (b / Real.sqrt q)
    (a ^ 2 - b / (m * Real.sqrt q)) 0
private theorem supportedState_isDensity (m q r n : ℕ) (hm : 0 < m) (hq : 0 < q)
    (h : m * q + r = n) (a b : ℝ) (hb : 0 ≤ b)
    (hu : 0 ≤ a ^ 2 - b / (m * Real.sqrt q)) (ha : a ^ 2 * m ^ 2 * q = 1) :
    IsDensity (supportedState m q r n h a b) := by
  apply blockStateOnFin_isDensity
  · exact div_nonneg hb (Real.sqrt_nonneg _)
  · exact hu
  · exact le_rfl
  · calc
      _ = (m : ℝ) * q * (b / Real.sqrt q + m *
          (a ^ 2 - b / (m * Real.sqrt q))) := by ring
      _ = a ^ 2 * m ^ 2 * q := by rw [lps_t_add_mu m q hm hq]; ring
      _ = 1 := ha
private lemma supported_distinguished_gram_value (m q : ℕ) (hm : 0 < m) (hq : 0 < q)
    (a b : ℝ) (ha : a ^ 2 * m ^ 2 * q = 1) :
    (q : ℝ) * (b / Real.sqrt q) ^ 2 +
      m * (q * (2 * (b / Real.sqrt q) * (a ^ 2 - b / (m * Real.sqrt q)) +
          m * (a ^ 2 - b / (m * Real.sqrt q)) ^ 2)) = a ^ 2 := by
  calc
    _ = (q : ℝ) * (b / Real.sqrt q + m *
        (a ^ 2 - b / (m * Real.sqrt q))) ^ 2 := by ring
    _ = a ^ 2 * (a ^ 2 * m ^ 2 * q) := by rw [lps_t_add_mu m q hm hq]; ring
    _ = a ^ 2 := by rw [ha, mul_one]
/-- The uniform witness at every Bob dimension at least `m³`. -/
private def uniformState (m n : ℕ) (h : m ^ 3 ≤ n) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  blockStateOnFin m (m ^ 2) (n - m ^ 3) n
    (by nlinarith [Nat.sub_add_cancel h]) (1 / (m : ℝ) ^ 3) 0 0
private theorem uniformState_isDensity (m n : ℕ) (hm : 0 < m) (h : m ^ 3 ≤ n) :
    IsDensity (uniformState m n h) := by
  apply blockStateOnFin_isDensity
  · positivity
  · exact le_rfl
  · exact le_rfl
  · have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
    simp only [zero_mul, add_zero, Nat.cast_pow]
    field_simp [hm0]
    <;> ring
private theorem uniformState_realign_gram (m n : ℕ) (hm : 0 < m) (h : m ^ 3 ≤ n) :
    let A := realign (uniformState m n h)
    A * Aᴴ = (1 / (m : ℝ) ^ 4) •
      (1 : Matrix (Fin m × Fin m) (Fin m × Fin m) ℂ) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp only [uniformState, blockStateOnFin_realign_gram, mul_zero,
    zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero, zero_smul]
  congr 1
  push_cast
  field_simp [hm0]
  <;> ring
/-- A sufficient dimension inequality guarantees positivity of the identity
coefficient in the main prescribed-spectrum construction. -/
private theorem main_coefficient_nonneg {m n q : ℝ} (hm : 2 ≤ m) (hq : 0 < q)
    (hmq : m * q ≤ n) (hnq : n ≤ m ^ 2 * Real.sqrt q) :
    0 ≤ (1 / Real.sqrt (m * n)) ^ 2 -
      ((1 - 1 / Real.sqrt (m * n)) / (m ^ 2 - 1)) / (m * Real.sqrt q) := by
  have hm0 : 0 < m := by linarith
  have hn0 : 0 < n := (mul_pos hm0 hq).trans_le hmq
  have hmn0 : 0 < m * n := mul_pos hm0 hn0
  have hs0 : 0 < Real.sqrt (m * n) := Real.sqrt_pos.mpr hmn0
  have hq0 : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hd : 0 < m ^ 2 - 1 := by nlinarith
  have hαsq : (1 / Real.sqrt (m * n)) ^ 2 = 1 / (m * n) := by
    rw [div_pow, one_pow, Real.sq_sqrt hmn0.le]
  have hprod : Real.sqrt q * Real.sqrt (m * n) ≤ n := by
    rw [← Real.sqrt_mul hq.le]
    apply (Real.sqrt_le_iff).mpr
    refine ⟨hn0.le, ?_⟩
    nlinarith only [mul_le_mul_of_nonneg_right hmq hn0.le]
  have hαn : Real.sqrt q ≤ (1 / Real.sqrt (m * n)) * n := by
    apply (le_div_iff₀ hs0).mpr at hprod
    simpa only [one_div_mul_eq_div] using hprod
  have hβn : ((1 - 1 / Real.sqrt (m * n)) / (m ^ 2 - 1)) * n ≤ Real.sqrt q := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hd]
    nlinarith only [hnq, hαn]
  rw [hαsq]
  apply sub_nonneg.mpr
  apply (div_le_div_iff₀ (mul_pos hm0 hq0) hmn0).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hβn hm0.le]
/-- Below the last supported block, the integer remainder supplies enough
slack for the main construction's positive identity coefficient. -/
private theorem main_dimension_square_bound {m q n : ℕ} (hm : 2 ≤ m) (hq : 1 ≤ q)
    (hqm : q + 2 ≤ m ^ 2) (hn : n + 1 ≤ m * (q + 1)) :
    (n : ℝ) ^ 2 ≤ (m : ℝ) ^ 4 * q := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hnR : (n : ℝ) + 1 ≤ (m : ℝ) * ((q : ℝ) + 1) := by exact_mod_cast hn
  have hqmR : (q : ℝ) + 2 ≤ (m : ℝ) ^ 2 := by exact_mod_cast hqm
  by_cases hsmall : q + 3 ≤ m ^ 2
  · have hsmallR : (q : ℝ) + 3 ≤ (m : ℝ) ^ 2 := by exact_mod_cast hsmall
    have hp : (q : ℝ) * ((q : ℝ) + 2 - (m : ℝ)^2) ≤ -(q : ℝ) := by
      have := mul_le_mul_of_nonneg_left (show (q : ℝ) + 2 - (m : ℝ)^2 ≤ -1 by linarith)
        (show 0 ≤ (q : ℝ) by positivity)
      nlinarith only [this]
    have hqsq : ((q : ℝ) + 1)^2 ≤ (m : ℝ)^2 * q := by nlinarith only [hp, hqR]
    calc
      (n : ℝ)^2 ≤ ((m : ℝ) * ((q : ℝ) + 1))^2 := by
        apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
        linarith
      _ ≤ (m : ℝ)^4 * q := by
        have := mul_le_mul_of_nonneg_left hqsq (sq_nonneg (m : ℝ))
        nlinarith only [this]
  · have hqeq : q + 2 = m ^ 2 := by omega
    have hqeqR : (q : ℝ) + 2 = (m : ℝ)^2 := by exact_mod_cast hqeq
    have heq := congrArg (fun z : ℝ => (m : ℝ) * z) hqeqR
    have hnB : (n : ℝ) ≤ (m : ℝ)^3 - m - 1 := by nlinarith only [hnR, heq]
    have hB0 : 0 ≤ (m : ℝ)^3 - m - 1 := (Nat.cast_nonneg n).trans hnB
    have hpoly : 0 ≤ 2 * (m : ℝ)^3 - (m : ℝ)^2 - 2 * m - 1 := by
      have h0 : 0 ≤ (m : ℝ) - 2 := by linarith
      have hc := mul_nonneg h0 (sq_nonneg ((m : ℝ) - 2))
      nlinarith only [h0, hc, sq_nonneg ((m : ℝ) - 2)]
    calc
      (n : ℝ)^2 ≤ ((m : ℝ)^3 - m - 1)^2 := (sq_le_sq₀ (by positivity) hB0).mpr hnB
      _ ≤ (m : ℝ)^4 * q := by
        have hmul := congrArg (fun z : ℝ => (m : ℝ)^4 * z) hqeqR
        nlinarith only [hmul, hpoly]
attribute [local irreducible] blockStateOnFin
open D5.S3.Quantum.Foundation.FiniteTraceDistance
/-- The established rectangular trace norm agrees with the row-side singular
sum, including every zero and without a restriction on relative dimensions. -/
private theorem traceNorm_eq_row_singular_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ ℂ) :
    traceNorm A = ∑ i, singularVector A i := by
  let hG := A.posSemidef_self_mul_conjTranspose.isHermitian
  have ht : traceNorm A = ∑ i, Real.sqrt (hG.eigenvalues i) := by
    rw [← D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance.traceNorm_conjTranspose_rect A]
    unfold D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm
    rw [Matrix.conjTranspose_conjTranspose,
      CFC.sqrt_eq_real_sqrt (A * Aᴴ)
        (Matrix.nonneg_iff_posSemidef.mpr A.posSemidef_self_mul_conjTranspose),
      cfcₙ_eq_cfc, Matrix.IsHermitian.cfc_eq hG, Matrix.IsHermitian.cfc]
    simp [Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [ht]
  simp_rw [singularVector_eq_sqrt_rowGram]
  exact Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    (fun i => Real.sqrt (hG.eigenvalues₀ i))
private lemma scalar_rankOne_charpoly {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mu nu : ℂ) (d : ι → ℂ) (hk : 0 < Fintype.card ι) :
    (mu • (1 : Matrix ι ι ℂ) + nu • Matrix.vecMulVec d d).charpoly =
      (Polynomial.X - Polynomial.C mu) ^ (Fintype.card ι - 1) *
        (Polynomial.X - Polynomial.C (mu + nu * (d ⬝ᵥ d))) := by
  let k := Fintype.card ι
  have he : mu • (1 : Matrix ι ι ℂ) + nu • Matrix.vecMulVec d d =
      Matrix.vecMulVec (nu • d) d - Matrix.scalar ι (-mu) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.scalar_apply,
      Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> ring
  rw [he, Matrix.charpoly_sub_scalar, Matrix.charpoly_vecMulVec]
  simp only [Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp,
    Polynomial.smul_comp, Polynomial.C_comp, Polynomial.smul_eq_C_mul]
  have hd : (nu • d) ⬝ᵥ d = nu * (d ⬝ᵥ d) := by
    simp [dotProduct, Finset.mul_sum, mul_assoc]
  rw [hd]
  have heq : Fintype.card ι = (Fintype.card ι - 1) + 1 := by omega
  conv_lhs => lhs; rw [heq, pow_succ]
  simp only [map_add, map_mul, map_neg]
  ring
/-- The identity matrix, viewed as a vector in the realignment row space. -/
private def identityDirection (m : ℕ) : Fin m × Fin m → ℂ :=
  fun p => if p.1 = p.2 then 1 else 0
private lemma identityDirection_dot (m : ℕ) :
    identityDirection m ⬝ᵥ identityDirection m = (m : ℂ) := by
  classical
  simp [identityDirection, dotProduct, Fintype.sum_prod_type, ite_mul, mul_ite]
private lemma blockStateOnFin_realign_charpoly (m q r n : ℕ) (h : m * q + r = n)
    (hm : 0 < m) (t u v : ℝ) :
    let mu : ℝ := q * t ^ 2
    let nu : ℝ := q * (2 * t * u + m * u ^ 2) + r * v ^ 2
    let A := realign (blockStateOnFin m q r n h t u v)
    (A * Aᴴ).charpoly =
      (Polynomial.X - Polynomial.C (mu : ℂ)) ^ (m ^ 2 - 1) *
        (Polynomial.X - Polynomial.C ((mu + m * nu : ℝ) : ℂ)) := by
  dsimp only
  rw [blockStateOnFin_realign_gram]
  have hk : 0 < Fintype.card (Fin m × Fin m) := by simp; positivity
  convert scalar_rankOne_charpoly
    (((q : ℝ) * t ^ 2 : ℝ) : ℂ)
    ((((q : ℝ) * (2 * t * u + m * u ^ 2) + r * v ^ 2) : ℝ) : ℂ)
    (identityDirection m) hk using 1 <;>
    simp [identityDirection_dot, identityDirection, pow_two, Complex.real_smul,
      Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow, mul_comm] <;>
    congr 1 <;> ext i j <;>
    simp [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, identityDirection] <;>
    exact Or.inl rfl
/-- Reading real singular-value multiplicities directly from a split row-Gram
characteristic polynomial avoids introducing any unproved spectral assumption. -/
private theorem singularMultiset_of_rowGram_charpoly {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpoly : (A * Aᴴ).charpoly =
      (Polynomial.X - Polynomial.C ((b ^ 2 : ℝ) : ℂ)) ^ (Fintype.card ι - 1) *
        (Polynomial.X - Polynomial.C ((a ^ 2 : ℝ) : ℂ))) :
    Finset.univ.val.map (singularVector A) =
      Multiset.replicate (Fintype.card ι - 1) b + {a} := by
  let hG := A.posSemidef_self_mul_conjTranspose.isHermitian
  have heig : Finset.univ.val.map hG.eigenvalues₀ =
      Multiset.replicate (Fintype.card ι - 1) (b ^ 2) + {a ^ 2} := by
    apply Multiset.map_injective Complex.ofReal_injective
    rw [Multiset.map_map]
    have hroots := hG.roots_charpoly_eq_eigenvalues₀
    rw [RCLike.ofReal_eq_complex_ofReal] at hroots
    rw [← hroots, hpoly,
      Polynomial.roots_mul (mul_ne_zero
        (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)) (Polynomial.X_sub_C_ne_zero _)),
      Polynomial.roots_pow, Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]
    simp [Multiset.nsmul_singleton]
  calc
    Finset.univ.val.map (singularVector A) =
        (Finset.univ.val.map hG.eigenvalues₀).map Real.sqrt := by
      rw [Multiset.map_map]
      apply Multiset.map_congr rfl
      intro i hi
      exact singularVector_eq_sqrt_rowGram A i
    _ = Multiset.replicate (Fintype.card ι - 1) b + {a} := by
      rw [heig]
      simp [Real.sqrt_sq ha, Real.sqrt_sq hb]
private theorem lpsState_singularMultiset (m q r n : ℕ) (hm : 0 < m) (hq : 0 < q)
    (h : m * q + r = n) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hanorm : a ^ 2 * m * n = 1) :
    Finset.univ.val.map (singularVector (realign (lpsState m q r n h a b))) =
      Multiset.replicate (m ^ 2 - 1) b + {a} := by
  have hp := blockStateOnFin_realign_charpoly m q r n h hm
    (b / Real.sqrt q) (a ^ 2 - b / (m * Real.sqrt q)) (a ^ 2)
  dsimp only at hp
  rw [lps_distinguished_gram_value m q r n hm hq h a b hanorm,
    lps_repeated_gram_value q hq b] at hp
  change Finset.univ.val.map (singularVector (realign (blockStateOnFin m q r n h
    (b / Real.sqrt q) (a ^ 2 - b / (m * Real.sqrt q)) (a ^ 2)))) = _
  have hc : Fintype.card (Fin m × Fin m) = m ^ 2 := by simp [pow_two]
  have hp' := hp
  rw [← hc] at hp'
  have hs := singularMultiset_of_rowGram_charpoly
    (realign (blockStateOnFin m q r n h (b / Real.sqrt q)
      (a ^ 2 - b / (m * Real.sqrt q)) (a ^ 2))) a b ha hb hp'
  exact hs.trans (congrArg (fun d => Multiset.replicate (d - 1) b + {a}) hc)
private theorem lpsState_traceNorm (m q r n : ℕ) (hm : 0 < m) (hq : 0 < q)
    (h : m * q + r = n) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hanorm : a ^ 2 * m * n = 1) (hbnorm : ((m ^ 2 - 1 : ℕ) : ℝ) * b + a = 1) :
    traceNorm (realign (lpsState m q r n h a b)) = 1 := by
  rw [traceNorm_eq_row_singular_sum]
  change (Finset.univ.val.map (singularVector (realign (lpsState m q r n h a b)))).sum = 1
  rw [lpsState_singularMultiset m q r n hm hq h a b ha hb hanorm]
  simpa [nsmul_eq_mul] using hbnorm
private theorem supportedState_singularMultiset (m q r n : ℕ) (hm : 0 < m) (hq : 0 < q)
    (h : m * q + r = n) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hanorm : a ^ 2 * m ^ 2 * q = 1) :
    Finset.univ.val.map (singularVector (realign (supportedState m q r n h a b))) =
      Multiset.replicate (m ^ 2 - 1) b + {a} := by
  have hp := blockStateOnFin_realign_charpoly m q r n h hm
    (b / Real.sqrt q) (a ^ 2 - b / (m * Real.sqrt q)) 0
  dsimp only at hp
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, add_zero] at hp
  rw [supported_distinguished_gram_value m q hm hq a b hanorm,
    lps_repeated_gram_value q hq b] at hp
  change Finset.univ.val.map (singularVector (realign (blockStateOnFin m q r n h
    (b / Real.sqrt q) (a ^ 2 - b / (m * Real.sqrt q)) 0))) = _
  have hc : Fintype.card (Fin m × Fin m) = m ^ 2 := by simp [pow_two]
  have hp' := hp
  rw [← hc] at hp'
  have hs := singularMultiset_of_rowGram_charpoly
    (realign (blockStateOnFin m q r n h (b / Real.sqrt q)
      (a ^ 2 - b / (m * Real.sqrt q)) 0)) a b ha hb hp'
  exact hs.trans (congrArg (fun d => Multiset.replicate (d - 1) b + {a}) hc)

private theorem supportedState_traceNorm (m q r n : ℕ) (hm : 0 < m) (hq : 0 < q)
    (h : m * q + r = n) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hanorm : a ^ 2 * m ^ 2 * q = 1) (hbnorm : ((m ^ 2 - 1 : ℕ) : ℝ) * b + a = 1) :
    traceNorm (realign (supportedState m q r n h a b)) = 1 := by
  rw [traceNorm_eq_row_singular_sum]
  change (Finset.univ.val.map (singularVector (realign (supportedState m q r n h a b)))).sum = 1
  rw [supportedState_singularMultiset m q r n hm hq h a b ha hb hanorm]
  simpa [nsmul_eq_mul] using hbnorm

/-- A prescribed-spectrum density matrix on every Bob space containing the
supported tensor block. The input conditions concern dimensions only. -/
theorem supported_witness (m q n : ℕ) (hm : 2 ≤ m) (hq : 1 ≤ q)
    (hqm : q ≤ m ^ 2) (hmqn : m * q ≤ n) :
    let a : ℝ := 1 / ((m : ℝ) * Real.sqrt q)
    let b : ℝ := (1 - a) / ((m : ℝ) ^ 2 - 1)
    ∃ ρ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity ρ ∧
      traceNorm (realign ρ) = 1 ∧
      Finset.univ.val.map (singularVector (realign ρ)) =
        Multiset.replicate (m ^ 2 - 1) b + {a} := by
  let a : ℝ := 1 / ((m : ℝ) * Real.sqrt q)
  let b : ℝ := (1 - a) / ((m : ℝ)^2 - 1)
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hs0 : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hq0
  have hs1 : 1 ≤ Real.sqrt (q : ℝ) := Real.one_le_sqrt.mpr hqR
  have hsa : Real.sqrt (q : ℝ) ≤ m :=
    Real.sqrt_le_iff.mpr ⟨hm0.le, by exact_mod_cast hqm⟩
  have hsq := Real.sq_sqrt hq0.le
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    apply (div_le_iff₀ (mul_pos hm0 hs0)).mpr
    have hp := mul_le_mul_of_nonneg_left hs1 hm0.le
    nlinarith only [hp, hmR]
  have hd : 0 < (m : ℝ)^2 - 1 := by nlinarith
  have hb0 : 0 ≤ b := div_nonneg (sub_nonneg.mpr ha1) hd.le
  have hnq : (m : ℝ) * q ≤ (m : ℝ)^2 * Real.sqrt q := by
    calc
      (m : ℝ) * q = ((m : ℝ) * Real.sqrt q) * Real.sqrt q := by
        rw [mul_assoc, ← pow_two, hsq]
      _ ≤ ((m : ℝ) * Real.sqrt q) * m :=
        mul_le_mul_of_nonneg_left hsa (by positivity)
      _ = (m : ℝ)^2 * Real.sqrt q := by ring
  have hroot : Real.sqrt ((m : ℝ) * ((m : ℝ) * q)) = (m : ℝ) * Real.sqrt q := by
    rw [show (m : ℝ) * ((m : ℝ) * q) = (m : ℝ)^2 * q by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hm0.le]
  have hu : 0 ≤ a ^ 2 - b / ((m : ℝ) * Real.sqrt q) := by
    have hu := main_coefficient_nonneg
      hmR hq0 (le_refl ((m : ℝ) * q)) hnq
    rw [hroot] at hu
    exact hu
  have hanorm : a ^ 2 * (m : ℝ)^2 * q = 1 := by
    dsimp [a]
    rw [div_pow, one_pow, mul_pow, hsq]
    field_simp [ne_of_gt hm0, ne_of_gt hq0]
  have hcast : ((m ^ 2 - 1 : ℕ) : ℝ) = (m : ℝ)^2 - 1 := by
    rw [Nat.cast_sub (by nlinarith : 1 ≤ m ^ 2), Nat.cast_pow, Nat.cast_one]
  have hbnorm : ((m ^ 2 - 1 : ℕ) : ℝ) * b + a = 1 := by
    rw [hcast]
    dsimp [b]
    field_simp [ne_of_gt hd]
    <;> ring
  let h : m * q + (n - m * q) = n := Nat.add_sub_of_le hmqn
  refine ⟨supportedState m q (n - m * q) n h a b, ?_, ?_, ?_⟩
  · exact supportedState_isDensity m q (n - m * q) n (by omega) (by omega)
      h a b hb0 hu hanorm
  · exact supportedState_traceNorm m q (n - m * q) n (by omega) (by omega)
      h a b ha0 hb0 hanorm hbnorm
  · exact supportedState_singularMultiset m q (n - m * q) n (by omega) (by omega)
      h a b ha0 hb0 hanorm

/-- The main witness at every dimension below the last supported tensor block.
All positivity and spectral obligations are discharged from natural dimensions. -/
theorem main_witness (m n : ℕ) (hm : 2 ≤ m) (hmn : m < n)
    (hn : n < m ^ 3 - m) :
    let a : ℝ := 1 / Real.sqrt ((m : ℝ) * n)
    let b : ℝ := (1 - a) / ((m : ℝ) ^ 2 - 1)
    ∃ ρ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity ρ ∧
      traceNorm (realign ρ) = 1 ∧
      Finset.univ.val.map (singularVector (realign ρ)) =
        Multiset.replicate (m ^ 2 - 1) b + {a} := by
  let q := n / m
  let r := n % m
  let a : ℝ := 1 / Real.sqrt ((m : ℝ) * n)
  let b : ℝ := (1 - a) / ((m : ℝ)^2 - 1)
  have hm0 : 0 < m := by omega
  have hq : 1 ≤ q := (Nat.le_div_iff_mul_le hm0).mpr (by simpa using hmn.le)
  have hsplit : m * q + r = n := Nat.div_add_mod n m
  have hr : r < m := Nat.mod_lt n hm0
  have hqLt : q < m ^ 2 - 1 := by
    apply (Nat.div_lt_iff_lt_mul hm0).mpr
    have hpow : m ^ 2 * m = m ^ 3 := by ring
    simpa only [Nat.sub_mul, hpow, one_mul] using hn
  have hqm : q + 2 ≤ m ^ 2 := by omega
  have hnup : n + 1 ≤ m * (q + 1) := by nlinarith
  have hdim := main_dimension_square_bound
    hm hq hqm hnup
  have hsqq := Real.sq_sqrt (show (0 : ℝ) ≤ q by positivity)
  have hnq : (n : ℝ) ≤ (m : ℝ)^2 * Real.sqrt q := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, hsqq]
    convert hdim using 1 <;> ring
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmR0 : (0 : ℝ) < m := by linarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hmnR0 : (0 : ℝ) < (m : ℝ) * n := mul_pos hmR0 hnR
  have hs0 : 0 < Real.sqrt ((m : ℝ) * n) := Real.sqrt_pos.mpr hmnR0
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    apply (div_le_iff₀ hs0).mpr
    rw [one_mul]
    apply Real.one_le_sqrt.mpr
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hp := mul_le_mul_of_nonneg_left hn1 hmR0.le
    nlinarith only [hp, hmR]
  have hd : 0 < (m : ℝ)^2 - 1 := by nlinarith
  have hb0 : 0 ≤ b := div_nonneg (sub_nonneg.mpr ha1) hd.le
  have hmqR : (m : ℝ) * q ≤ n := by exact_mod_cast Nat.mul_div_le n m
  have hu : 0 ≤ a ^ 2 - b / ((m : ℝ) * Real.sqrt q) :=
    main_coefficient_nonneg
      hmR hqR hmqR hnq
  have hanorm : a ^ 2 * m * n = 1 := by
    dsimp [a]
    rw [div_pow, one_pow, Real.sq_sqrt hmnR0.le]
    field_simp [ne_of_gt hmR0, ne_of_gt hnR]
  have hcast : ((m ^ 2 - 1 : ℕ) : ℝ) = (m : ℝ)^2 - 1 := by
    rw [Nat.cast_sub (by nlinarith : 1 ≤ m ^ 2), Nat.cast_pow, Nat.cast_one]
  have hbnorm : ((m ^ 2 - 1 : ℕ) : ℝ) * b + a = 1 := by
    rw [hcast]
    dsimp [b]
    field_simp [ne_of_gt hd]
    <;> ring
  refine ⟨lpsState m q r n hsplit a b, ?_, ?_, ?_⟩
  · exact lpsState_isDensity m q r n hm0 (by omega) hsplit a b hb0 hu hanorm
  · exact lpsState_traceNorm m q r n hm0 (by omega) hsplit a b ha0 hb0 hanorm hbnorm
  · exact lpsState_singularMultiset m q r n hm0 (by omega) hsplit a b ha0 hb0 hanorm

private lemma singularVector_of_scalar_rowGram {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (b : ℝ) (hb : 0 ≤ b)
    (hGram : A * Aᴴ = b ^ 2 • (1 : Matrix ι ι ℂ))
    (i : Fin (Fintype.card ι)) : singularVector A i = b := by
  let hG := A.posSemidef_self_mul_conjTranspose.isHermitian
  have hpoly : (A * Aᴴ).charpoly =
      (Polynomial.X - Polynomial.C ((b ^ 2 : ℝ) : ℂ)) ^ Fintype.card ι := by
    rw [hGram]
    have he : b ^ 2 • (1 : Matrix ι ι ℂ) =
        Matrix.diagonal (fun _ => ((b ^ 2 : ℝ) : ℂ)) := by
      ext j k
      by_cases h : j = k <;> simp [Matrix.one_apply, Matrix.diagonal_apply, h]
    rw [he, Matrix.charpoly_diagonal]
    simp
  have heig : Finset.univ.val.map hG.eigenvalues₀ =
      Multiset.replicate (Fintype.card ι) (b ^ 2) := by
    apply Multiset.map_injective Complex.ofReal_injective
    have hroots := hG.roots_charpoly_eq_eigenvalues₀
    rw [RCLike.ofReal_eq_complex_ofReal] at hroots
    rw [Multiset.map_map, ← hroots, hpoly,
      Polynomial.roots_pow, Polynomial.roots_X_sub_C]
    simp [Multiset.nsmul_singleton]
  have hi : hG.eigenvalues₀ i = b ^ 2 := by
    have hi' : hG.eigenvalues₀ i ∈ Finset.univ.val.map hG.eigenvalues₀ :=
      Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
    rw [heig, Multiset.mem_replicate] at hi'
    exact hi'.2
  rw [singularVector_eq_sqrt_rowGram, hi, Real.sqrt_sq hb]

/-- All `m²` native singular values of the actual large-dimension witness
are `1/m²`. -/
private theorem uniformState_singularVector (m n : ℕ) (hm : 0 < m) (h : m ^ 3 ≤ n)
    (i : Fin (Fintype.card (Fin m × Fin m))) :
    singularVector (realign (uniformState m n h)) i = 1 / (m : ℝ) ^ 2 := by
  apply singularVector_of_scalar_rowGram _ _ (by positivity)
  rw [uniformState_realign_gram m n hm h]
  congr 1
  ring

/-- The uniform witness saturates CCNR in the repository's actual trace norm. -/
private theorem uniformState_traceNorm (m n : ℕ) (hm : 0 < m) (h : m ^ 3 ≤ n) :
    traceNorm (realign (uniformState m n h)) = 1 := by
  rw [traceNorm_eq_row_singular_sum]
  simp_rw [uniformState_singularVector m n hm h]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp [Fintype.card_prod, pow_two]
  field_simp [hm0]

/-- The uniform prescribed spectrum is realized at every dimension at least
`m³` by a density matrix saturating the actual CCNR norm. -/
theorem uniform_witness (m n : ℕ) (hm : 2 ≤ m) (h : m ^ 3 ≤ n) :
    let a : ℝ := 1 / ((m : ℝ)^2)
    let b : ℝ := (1 - a) / ((m : ℝ)^2 - 1)
    ∃ ρ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity ρ ∧
      traceNorm (realign ρ) = 1 ∧
      Finset.univ.val.map (singularVector (realign ρ)) =
        Multiset.replicate (m ^ 2 - 1) b + {a} := by
  let a : ℝ := 1 / ((m : ℝ)^2)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hd : (m : ℝ)^2 - 1 ≠ 0 := by
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hb : (1 - a) / ((m : ℝ)^2 - 1) = a := by
    dsimp [a]
    field_simp [hm0, hd]
  refine ⟨uniformState m n h, uniformState_isDensity m n (by omega) h,
    uniformState_traceNorm m n (by omega) h, ?_⟩
  rw [hb]
  have hs : Finset.univ.val.map (singularVector (realign (uniformState m n h))) =
      Multiset.replicate (m ^ 2) a := by
    simp_rw [uniformState_singularVector m n (by omega) h]
    simp [a, pow_two]
  rw [hs]
  have hk : m ^ 2 - 1 + 1 = m ^ 2 := Nat.sub_add_cancel (by nlinarith)
  conv_lhs => rw [← hk, Multiset.replicate_add]
  simp only [Multiset.replicate_one]; rfl


private theorem esymmSV_of_profile {m n ℓ : ℕ} (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ)
    (A : Matrix (Fin m × Fin m) (Fin n × Fin n) ℂ) (a : ℝ)
    (hsp : Finset.univ.val.map (singularVector A) =
      Multiset.replicate (m ^ 2 - 1) ((1 - a) / ((m : ℝ)^2 - 1)) + {a}) :
    esymmSV ℓ A = schurProfile (m ^ 2) ℓ a := by
  have hk : 1 ≤ m ^ 2 := by nlinarith
  have hb : (1 - a) / ((m : ℝ)^2 - 1) = tailMean (m ^ 2) a := by
    simp only [tailMean, Nat.cast_sub hk, Nat.cast_pow, Nat.cast_one]
  rw [hb] at hsp
  have he := esymm_cons_replicate (m ^ 2 - 1) (ℓ - 1) a (tailMean (m ^ 2) a)
  have hℓeq : ℓ - 1 + 1 = ℓ := by omega
  rw [hℓeq] at he
  unfold esymmSV
  rw [hsp, Multiset.add_comm, Multiset.singleton_add]
  simpa only [schurProfile] using he

/-- Every nontrivial rectangular elementary-symmetric realignment order has a
strict gap between separability and the CCNR-admissible density matrices. -/
theorem result (m n ℓ : ℕ) (hm : 2 ≤ m) (hmn : m < n) (hℓ : 2 ≤ ℓ)
    (hℓk : ℓ ≤ m ^ 2) :
    ∃ ρ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      IsDensity ρ ∧ traceNorm (realign ρ) ≤ 1 ∧
      ∃ c' : ℝ, (∀ σ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
        IsSeparable σ → esymmSV ℓ (realign σ) ≤ c') ∧
        c' < esymmSV ℓ (realign ρ) := by
  let c' := schurProfile (m ^ 2) ℓ (separableThreshold m n)
  have hsep : ∀ σ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      IsSeparable σ → esymmSV ℓ (realign σ) ≤ c' :=
    fun σ hσ => separable_esymm_bound hm hmn hℓ hℓk σ hσ
  by_cases hlarge : m ^ 3 ≤ n
  · obtain ⟨ρ, hρ, hnorm, hsp⟩ := uniform_witness m n hm hlarge
    refine ⟨ρ, hρ, hnorm.le, c', hsep, ?_⟩
    rw [esymmSV_of_profile hm hℓ _ _ hsp]
    exact uniform_profile_gap hm (by omega) hℓ hℓk
  · by_cases hmain : n < m ^ 3 - m
    · obtain ⟨ρ, hρ, hnorm, hsp⟩ := main_witness m n hm hmn hmain
      refine ⟨ρ, hρ, hnorm.le, c', hsep, ?_⟩
      rw [esymmSV_of_profile hm hℓ _ _ hsp]
      exact main_profile_gap hm hmn (by omega) hℓ hℓk
    · have hq : 1 ≤ m ^ 2 - 1 := by
        have : 2 ≤ m ^ 2 := by nlinarith
        omega
      have hsupport : m * (m ^ 2 - 1) ≤ n := by
        have hpow : m * (m ^ 2 - 1) = m ^ 3 - m := by
          rw [Nat.mul_sub_left_distrib]
          congr 1 <;> ring
        rw [hpow]
        omega
      obtain ⟨ρ, hρ, hnorm, hsp⟩ := supported_witness m (m ^ 2 - 1) n hm hq (by omega) hsupport
      refine ⟨ρ, hρ, hnorm.le, c', hsep, ?_⟩
      rw [esymmSV_of_profile hm hℓ _ _ hsp]
      have hcast : ((m ^ 2 - 1 : ℕ) : ℝ) = (m : ℝ)^2 - 1 := by
        rw [Nat.cast_sub (by nlinarith : 1 ≤ m ^ 2), Nat.cast_pow, Nat.cast_one]
      rw [hcast]
      exact exceptional_profile_gap hm (by omega) hℓ hℓk

end D5.S3.Quantum.Entanglement.Witness.LiPoonSzeP2
