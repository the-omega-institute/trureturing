/- GID: D5/S3/Quantum/Foundation/EffectDensityStability
   generality: I
   mirror-B: D5/B/S3/Quantum/Foundation/EffectDensityStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform approximate effect additivity yields one density with an explicit all-effect error bound. -/

/-
The finite positive-coordinate construction uses diagonal, real-pair and
imaginary-pair effects. Their exact coordinate expansion and trace pairing give
a Hermitian candidate with uniform error. Spectral repair then gives one positive
complex-trace-one density for all effects, with error
4 * (2*d - 1)^2 * (6*d^2 + 1) * epsilon.

The quantitative argument is the bounded-interval, signed-family and spectral
repair construction. Busch supplies the exact all-effect representation
background. The implication requires its global effect hypotheses; finite
observations alone do not establish them, and no physical realization or
optimality is asserted.
-/

import D5.S3.Quantum.Foundation.EffectAdditivityStability
import D5.S3.Quantum.Foundation.EffectDensityRepair
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped Matrix BigOperators ComplexOrder MatrixOrder CStarAlgebra
open D5.S3.Quantum.Foundation.EffectAdditivityStability
namespace D5.S3.Quantum.Foundation.EffectDensityStability

def diagonalProbe {d : ℕ} (i : Fin d) : Mat d := Matrix.single i i 1

def realProbe {d : ℕ} (i j : Fin d) : Mat d :=
  (2 : ℂ)⁻¹ • Matrix.vecMulVec (Pi.single i 1 + Pi.single j 1)
    (star (Pi.single i 1 + Pi.single j 1))

def imaginaryProbe {d : ℕ} (i j : Fin d) : Mat d :=
  (2 : ℂ)⁻¹ • Matrix.vecMulVec (Pi.single i 1 + Pi.single j Complex.I)
    (star (Pi.single i 1 + Pi.single j Complex.I))

def upperEntry {d : ℕ} (p : Mat d → ℝ) (i j : Fin d) : ℂ :=
  ⟨p (realProbe i j) - (p (diagonalProbe i) + p (diagonalProbe j))/2,
    (p (diagonalProbe i) + p (diagonalProbe j))/2 - p (imaginaryProbe i j)⟩

def candidate {d : ℕ} (p : Mat d → ℝ) : Mat d := fun i j =>
  if i = j then (p (diagonalProbe i) : ℂ)
  else if i < j then upperEntry p i j else star (upperEntry p j i)

theorem candidate_hermitian {d : ℕ} (p : Mat d → ℝ) : (candidate p).IsHermitian := by
  ext i j
  by_cases hij : i = j
  · subst j; simp [candidate, Matrix.conjTranspose_apply]
  · by_cases hlt : i < j
    · simp [candidate, Matrix.conjTranspose_apply, hij, Ne.symm hij, hlt,
        not_lt.mpr (le_of_lt hlt)]
    · have hgt : j < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)
      simp [candidate, Matrix.conjTranspose_apply, hij, Ne.symm hij, hlt, hgt]

def realMinus {d : ℕ} (i j : Fin d) : Mat d :=
  (2 : ℂ)⁻¹ • Matrix.vecMulVec (Pi.single i 1 - Pi.single j 1)
    (star (Pi.single i 1 - Pi.single j 1))

def imaginaryMinus {d : ℕ} (i j : Fin d) : Mat d :=
  (2 : ℂ)⁻¹ • Matrix.vecMulVec (Pi.single i 1 - Pi.single j Complex.I)
    (star (Pi.single i 1 - Pi.single j Complex.I))

theorem diagonal_eq {d : ℕ} (i : Fin d) :
    diagonalProbe i = Matrix.diagonal (fun k => if k = i then (1 : ℂ) else 0) := by
  ext a b
  by_cases ha : a = i <;> by_cases hb : b = i <;> by_cases hab : a = b <;>
    simp_all [diagonalProbe, Matrix.single, Matrix.diagonal, eq_comm]

theorem diagonal_effect {d : ℕ} (i : Fin d) : IsEffect (diagonalProbe i) := by
  rw [diagonal_eq]
  constructor
  · exact Matrix.PosSemidef.diagonal (fun k => by split_ifs <;> simp)
  · have heq : (1 : Mat d) - Matrix.diagonal (fun k => if k = i then (1 : ℂ) else 0) =
        Matrix.diagonal (fun k => if k = i then (0 : ℂ) else 1) := by
      ext a b
      by_cases hab : a = b <;> by_cases ha : a = i <;>
        simp_all [Matrix.diagonal]
    rw [heq]
    exact Matrix.PosSemidef.diagonal (fun k => by split_ifs <;> simp)

theorem pair_diagonal_le {d : ℕ} (i j : Fin d) (hij : i ≠ j) :
    diagonalProbe i + diagonalProbe j ≤ (1 : Mat d) := by
  rw [Matrix.le_iff]
  have heq : (1 : Mat d) - (diagonalProbe i + diagonalProbe j) =
      Matrix.diagonal (fun k => if k = i ∨ k = j then (0 : ℂ) else 1) := by
    rw [diagonal_eq, diagonal_eq]
    ext a b
    by_cases hab : a = b <;> by_cases ha : a = i <;> by_cases hj : a = j <;>
      simp_all [Matrix.diagonal]
  rw [heq]
  exact Matrix.PosSemidef.diagonal (fun k => by split_ifs <;> simp)

theorem real_complement {d : ℕ} (i j : Fin d) (hij : i ≠ j) :
    diagonalProbe i + diagonalProbe j - realProbe i j = realMinus i j := by
  ext a b
  by_cases hai : a = i <;> by_cases haj : a = j <;>
    by_cases hbi : b = i <;> by_cases hbj : b = j <;>
    simp_all [diagonalProbe, realProbe, realMinus, Matrix.vecMulVec,
      Matrix.single, Pi.single_apply, Pi.star_apply, smul_eq_mul, eq_comm]
  all_goals norm_num

theorem imaginary_complement {d : ℕ} (i j : Fin d) (hij : i ≠ j) :
    diagonalProbe i + diagonalProbe j - imaginaryProbe i j = imaginaryMinus i j := by
  ext a b
  by_cases hai : a = i <;> by_cases haj : a = j <;>
    by_cases hbi : b = i <;> by_cases hbj : b = j <;>
    simp_all [diagonalProbe, imaginaryProbe, imaginaryMinus, Matrix.vecMulVec,
      Matrix.single, Pi.single_apply, Pi.star_apply, smul_eq_mul, eq_comm]
  all_goals norm_num [Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im]

theorem real_le_pair {d : ℕ} (i j : Fin d) (hij : i ≠ j) :
    realProbe i j ≤ diagonalProbe i + diagonalProbe j := by
  rw [Matrix.le_iff, real_complement i j hij]
  exact (Matrix.posSemidef_vecMulVec_self_star _).smul
    (by norm_num [Complex.nonneg_iff, Complex.inv_re, Complex.inv_im])

theorem imaginary_le_pair {d : ℕ} (i j : Fin d) (hij : i ≠ j) :
    imaginaryProbe i j ≤ diagonalProbe i + diagonalProbe j := by
  rw [Matrix.le_iff, imaginary_complement i j hij]
  exact (Matrix.posSemidef_vecMulVec_self_star _).smul
    (by norm_num [Complex.nonneg_iff, Complex.inv_re, Complex.inv_im])

theorem real_effect {d : ℕ} (i j : Fin d) (hij : i ≠ j) : IsEffect (realProbe i j) := by
  apply (effect_iff_order _).mpr
  refine ⟨?_, (real_le_pair i j hij).trans (pair_diagonal_le i j hij)⟩
  exact ((Matrix.posSemidef_vecMulVec_self_star _).smul
    (show (0 : ℂ) ≤ 2⁻¹ by norm_num [Complex.nonneg_iff, Complex.inv_re, Complex.inv_im])).nonneg

theorem imaginary_effect {d : ℕ} (i j : Fin d) (hij : i ≠ j) : IsEffect (imaginaryProbe i j) := by
  apply (effect_iff_order _).mpr
  refine ⟨?_, (imaginary_le_pair i j hij).trans (pair_diagonal_le i j hij)⟩
  exact ((Matrix.posSemidef_vecMulVec_self_star _).smul
    (show (0 : ℂ) ≤ 2⁻¹ by norm_num [Complex.nonneg_iff, Complex.inv_re, Complex.inv_im])).nonneg

theorem entry_norm_bound {d : ℕ} (E : Mat d) (hE : IsEffect E) (i j : Fin d) :
    ‖E i j‖ ≤ 1 := by
  have hb := (cstar_effect_bridge (CStarMatrix.ofMatrix E)).mp hE
  exact (CStarMatrix.norm_entry_le_norm (M := CStarMatrix.ofMatrix E)).trans
    ((CStarAlgebra.norm_le_one_iff_of_nonneg _ hb.1).mpr hb.2)

def probe {d : ℕ} (a : Fin d × Fin d) : Mat d :=
  if a.1 = a.2 then diagonalProbe a.1
  else if a.1 < a.2 then realProbe a.1 a.2 else imaginaryProbe a.2 a.1

theorem probe_effect {d : ℕ} (a : Fin d × Fin d) : IsEffect (probe a) := by
  rcases a with ⟨i,j⟩
  by_cases hij : i = j
  · simp [probe, hij, diagonal_effect]
  · by_cases hlt : i < j
    · simpa [probe, hij, hlt] using real_effect i j hij
    · simpa [probe, hij, hlt] using imaginary_effect j i (Ne.symm hij)

theorem probe_card (d : ℕ) : Fintype.card (Fin d × Fin d) = d^2 := by
  simp [pow_two]

def majorant {d : ℕ} (a : Fin d × Fin d) : Mat d :=
  diagonalProbe a.1 + diagonalProbe a.2 - if a.1 = a.2 then diagonalProbe a.1 else 0

theorem probe_le_majorant {d : ℕ} (a : Fin d × Fin d) : probe a ≤ majorant a := by
  rcases a with ⟨i,j⟩
  by_cases hij : i = j
  · subst j
    simp [probe, majorant]
  · by_cases hlt : i < j
    · simpa [probe, majorant, hij, hlt] using real_le_pair i j hij
    · simpa [probe, majorant, hij, hlt, add_comm] using imaginary_le_pair j i (Ne.symm hij)

theorem diagonal_sum (d : ℕ) : (∑ i : Fin d, diagonalProbe i) = (1 : Mat d) := by
  exact Matrix.sum_single_one

theorem triangular_sum {ι A : Type*} [Fintype ι] [LinearOrder ι]
    [AddCommMonoid A] (f : ι → ι → A) :
    (∑ i, ∑ j, f i j) = (∑ i, f i i) +
      ∑ i, ∑ j, if i < j then f i j + f j i else 0 := by
  classical
  have hp (i j : ι) : f i j =
      (if i = j then f i i else 0) + (if i < j then f i j else 0) +
        (if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [ne_of_lt h, h, not_lt_of_ge h.le]
    · subst j; simp
    · simp [ne_of_gt h, h, not_lt_of_ge h.le]
  have hs : (∑ i, ∑ j, f i j) =
      (∑ i, f i i) + (∑ i, ∑ j, if i < j then f i j else 0) +
        (∑ i, ∑ j, if j < i then f i j else 0) := by
    calc
      _ = ∑ i, ∑ j, ((if i = j then f i i else 0) +
          (if i < j then f i j else 0) + (if j < i then f i j else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_congr rfl (fun j _ => hp i j)
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_ite_eq,
          Finset.mem_univ, ite_true]
  rw [hs, Finset.sum_comm (f := fun i j => if j < i then f i j else 0)]
  have hjoin : (∑ i, ∑ j, if i < j then f i j + f j i else 0) =
      (∑ i, ∑ j, if i < j then f i j else 0) +
        (∑ i, ∑ j, if i < j then f j i else 0) := by
    calc
      _ = ∑ i, ∑ j, ((if i < j then f i j else 0) +
          (if i < j then f j i else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> simp
      _ = _ := by simp only [Finset.sum_add_distrib]
  rw [hjoin, add_assoc]

theorem incident_sum {ι A : Type*} [Fintype ι] [AddCommMonoid A]
    [Module ℝ A] (q : ι → ι → ℝ) (D : ι → A) :
    (∑ i, (∑ j, (q i j + q j i)) • D i) =
      ∑ i, ∑ j, q i j • (D i + D j) := by
  simp only [Finset.sum_smul, add_smul, smul_add, Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm

def coordinate {d : ℕ} (E : Mat d) (a : Fin d × Fin d) : ℝ :=
  if a.1 = a.2 then (E a.1 a.1).re -
    ∑ k : Fin d, (if a.1 < k then (E a.1 k).re - (E a.1 k).im else
      if k < a.1 then (E k a.1).re - (E k a.1).im else 0)
  else if a.1 < a.2 then 2 * (E a.1 a.2).re else -2 * (E a.2 a.1).im

def offdiagTerm {d : ℕ} (E : Mat d) (i j : Fin d) : Mat d :=
  (2 * (E i j).re) • realProbe i j + (-2 * (E i j).im) • imaginaryProbe i j -
    ((E i j).re - (E i j).im) • (diagonalProbe i + diagonalProbe j)

theorem offdiag_identity {d : ℕ} (E : Mat d) (i j : Fin d) (hij : i ≠ j) :
    offdiagTerm E i j = Matrix.single i j (E i j) + Matrix.single j i (star (E i j)) := by
  ext a b
  by_cases hai : a = i <;> by_cases haj : a = j <;>
    by_cases hbi : b = i <;> by_cases hbj : b = j <;>
    simp_all [offdiagTerm, diagonalProbe, realProbe, imaginaryProbe, Matrix.vecMulVec,
      Matrix.single, Pi.single_apply, Pi.star_apply, smul_eq_mul, eq_comm,
      Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im]
  all_goals norm_num
  all_goals try (constructor <;> ring)
  all_goals ring

def upperCorrection {d : ℕ} (E : Mat d) (i j : Fin d) : ℝ :=
  if i < j then (E i j).re - (E i j).im else 0

theorem coordinate_diagonal {d : ℕ} (E : Mat d) (i : Fin d) :
    coordinate E (i,i) = (E i i).re -
      ∑ j : Fin d, (upperCorrection E i j + upperCorrection E j i) := by
  simp only [coordinate, ite_true]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i < j
  · simp [upperCorrection, h, not_lt_of_ge h.le]
  · simp [upperCorrection, h]

theorem coordinate_pair {d : ℕ} (E : Mat d) (i j : Fin d) :
    (if i < j then coordinate E (i,j) • probe (i,j) +
      coordinate E (j,i) • probe (j,i) else 0) =
    (if i < j then offdiagTerm E i j else 0) +
      upperCorrection E i j • (diagonalProbe i + diagonalProbe j) := by
  by_cases h : i < j
  · simp only [ite_eq_left h, coordinate, probe, ite_eq_right (ne_of_lt h),
      ite_eq_right (ne_of_gt h), ite_eq_right (not_lt_of_ge h.le), upperCorrection,
      offdiagTerm]
    module
  · simp [h, upperCorrection]

theorem coordinate_split {d : ℕ} (E : Mat d) :
    (∑ a : Fin d × Fin d, coordinate E a • probe a) =
      (∑ i : Fin d, (E i i).re • diagonalProbe i) +
        ∑ i : Fin d, ∑ j : Fin d, if i < j then offdiagTerm E i j else 0 := by
  rw [Fintype.sum_prod_type, triangular_sum]
  have hd : (∑ i : Fin d, coordinate E (i,i) • probe (i,i)) =
      (∑ i : Fin d, (E i i).re • diagonalProbe i) -
        ∑ i : Fin d, ∑ j : Fin d,
          upperCorrection E i j • (diagonalProbe i + diagonalProbe j) := by
    simp only [probe, ite_true, coordinate_diagonal, sub_smul, Finset.sum_sub_distrib]
    rw [incident_sum]
  rw [hd]
  simp_rw [coordinate_pair]
  simp only [Finset.sum_add_distrib]
  abel

theorem coordinate_expansion {d : ℕ} (E : Mat d) (hE : E.IsHermitian) :
    (∑ a : Fin d × Fin d, coordinate E a • probe a) = E := by
  rw [coordinate_split]
  have hd (i : Fin d) : (E i i).re • diagonalProbe i = Matrix.single i i (E i i) := by
    rw [diagonalProbe, Matrix.smul_single]
    congr 1
    simpa using hE.coe_re_apply_self i
  have ho (i j : Fin d) : (if i < j then offdiagTerm E i j else 0) =
      (if i < j then Matrix.single i j (E i j) + Matrix.single j i (E j i) else 0) := by
    by_cases h : i < j
    · rw [ite_eq_left h, ite_eq_left h, offdiag_identity E i j (ne_of_lt h)]
      rw [hE.apply]
    · rw [ite_eq_right h, ite_eq_right h]
  simp_rw [hd, ho]
  exact (triangular_sum (fun i j : Fin d => Matrix.single i j (E i j))).symm.trans
    (Matrix.sum_sum_single E)

lemma real_probe_decomp {d : ℕ} (i j : Fin d) (hij : i ≠ j) :
    realProbe i j = (2 : ℂ)⁻¹ •
      (Matrix.single i i 1 + Matrix.single i j 1 + Matrix.single j i 1 + Matrix.single j j 1) := by
  ext a b
  by_cases hai : a = i <;> by_cases haj : a = j <;>
    by_cases hbi : b = i <;> by_cases hbj : b = j <;>
    simp_all [realProbe, Matrix.vecMulVec, Matrix.single, Pi.single_apply, Pi.star_apply,
      smul_eq_mul, eq_comm]

lemma imaginary_probe_decomp {d : ℕ} (i j : Fin d) (hij : i ≠ j) :
    imaginaryProbe i j = (2 : ℂ)⁻¹ •
      (Matrix.single i i 1 + Matrix.single i j (-Complex.I) +
        Matrix.single j i Complex.I + Matrix.single j j 1) := by
  ext a b
  by_cases hai : a = i <;> by_cases haj : a = j <;>
    by_cases hbi : b = i <;> by_cases hbj : b = j <;>
    simp_all [imaginaryProbe, Matrix.vecMulVec, Matrix.single, Pi.single_apply, Pi.star_apply,
      smul_eq_mul, eq_comm]

lemma trace_single_sum {d : ℕ} (C : Mat d) (i j : Fin d) (a : ℂ) :
    Matrix.trace (C * Matrix.single i j a) = a * C j i := by
  simpa [mul_comm] using Matrix.trace_mul_single C i j a

lemma trace_real_formula {d : ℕ} (C : Mat d) (i j : Fin d) (hij : i ≠ j) :
    (Matrix.trace (C * realProbe i j)).re =
      ((C i i).re + (C j j).re + (C i j).re + (C j i).re) / 2 := by
  rw [real_probe_decomp i j hij, Matrix.mul_smul, Matrix.mul_add,
    Matrix.mul_add, Matrix.mul_add]
  simp only [Matrix.trace_smul, Matrix.trace_add, trace_single_sum]
  norm_num [Complex.ext_iff, Complex.mul_re, Complex.inv_re, Complex.inv_im]
  ring

lemma trace_imaginary_formula {d : ℕ} (C : Mat d) (i j : Fin d) (hij : i ≠ j) :
    (Matrix.trace (C * imaginaryProbe i j)).re =
      ((C i i).re + (C j j).re + (C j i).im - (C i j).im) / 2 := by
  rw [imaginary_probe_decomp i j hij, Matrix.mul_smul, Matrix.mul_add,
    Matrix.mul_add, Matrix.mul_add]
  simp only [Matrix.trace_smul, Matrix.trace_add, trace_single_sum]
  norm_num [Complex.ext_iff, Complex.mul_re, Complex.mul_im,
    Complex.inv_re, Complex.inv_im]
  ring

theorem probe_trace {d : ℕ} (p : Mat d → ℝ) (a : Fin d × Fin d) :
    (Matrix.trace (candidate p * probe a)).re = p (probe a) := by
  rcases a with ⟨i,j⟩
  by_cases hij : i = j
  · subst j
    simp [probe, diagonalProbe, candidate, Matrix.trace_mul_single]
  · by_cases hlt : i < j
    · have hformula := trace_real_formula (candidate p) i j hij
      simp only [probe, ite_eq_right hij, ite_eq_left hlt]
      calc
        (Matrix.trace (candidate p * realProbe i j)).re =
            ((candidate p i i).re + (candidate p j j).re +
              (candidate p i j).re + (candidate p j i).re) / 2 := hformula
        _ = p (realProbe i j) := by
          simp [candidate, upperEntry, hij, Ne.symm hij, hlt,
            not_lt_of_ge hlt.le]
          ring
    · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)
      have hformula := trace_imaginary_formula (candidate p) j i (Ne.symm hij)
      simp only [probe, ite_eq_right hij, ite_eq_right hlt]
      calc
        (Matrix.trace (candidate p * imaginaryProbe j i)).re =
            ((candidate p j j).re + (candidate p i i).re +
              (candidate p i j).im - (candidate p j i).im) / 2 := hformula
        _ = p (imaginaryProbe j i) := by
          simp [candidate, upperEntry, hij, Ne.symm hij, hlt, hji]
          ring

theorem coordinate_trace {d : ℕ} (p : Mat d → ℝ) (H : Mat d)
    (hH : H.IsHermitian) :
    (Matrix.trace (candidate p * H)).re =
      ∑ a : Fin d × Fin d, coordinate H a * p (probe a) := by
  have hexp := coordinate_expansion H hH
  have hcomplex :
      Matrix.trace (candidate p * (∑ a : Fin d × Fin d, coordinate H a • probe a)) =
        ∑ a : Fin d × Fin d,
          (coordinate H a : ℂ) * Matrix.trace (candidate p * probe a) := by
    rw [Matrix.mul_sum]
    simp_rw [Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul, Complex.real_smul]
  conv_lhs => rw [← hexp]
  rw [hcomplex]
  simp_rw [Complex.re_sum, Complex.re_ofReal_mul, probe_trace]

theorem majorant_sum (d : ℕ) :
    (∑ a : Fin d × Fin d, majorant a) =
      (2 * (d : ℝ) - 1) • (1 : Mat d) := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [majorant, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.sum_nsmul, diagonal_sum]
  simp only [← Nat.cast_smul_eq_nsmul ℝ]
  module

theorem probe_sum_bound (d : ℕ) :
    (∑ a : Fin d × Fin d, probe a) ≤
      (2 * (d : ℝ) - 1) • (1 : Mat d) := by
  rw [← majorant_sum]
  exact Finset.sum_le_sum (fun a _ => probe_le_majorant a)

theorem coordinate_bound {d : ℕ} (hd : 1 ≤ d)
    (E : Mat d) (hE : IsEffect E) (a : Fin d × Fin d) :
    |coordinate E a| ≤ 2 * (d : ℝ) - 1 := by
  classical
  have hre (i j : Fin d) : |(E i j).re| ≤ 1 :=
    (Complex.abs_re_le_norm _).trans (entry_norm_bound E hE i j)
  have him (i j : Fin d) : |(E i j).im| ≤ 1 :=
    (Complex.abs_im_le_norm _).trans (entry_norm_bound E hE i j)
  have hdiff (i j : Fin d) : |(E i j).re - (E i j).im| ≤ 2 := by
    have ht : |(E i j).re - (E i j).im| ≤ |(E i j).re| + |(E i j).im| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (E i j).re (-(E i j).im)
    linarith [hre i j, him i j]
  rcases a with ⟨i,j⟩
  by_cases hij : i = j
  · subst j
    let t : Fin d → ℝ := fun k =>
      if i < k then (E i k).re - (E i k).im else
        if k < i then (E k i).re - (E k i).im else 0
    have ht (k : Fin d) : |t k| ≤ if k = i then 0 else 2 := by
      by_cases hik : i < k
      · simpa only [t, ite_eq_left hik, ite_eq_right (ne_of_gt hik)] using hdiff i k
      · by_cases hki : k < i
        · simpa only [t, ite_eq_right hik, ite_eq_left hki, ite_eq_right (ne_of_lt hki)] using hdiff k i
        · have hki' : k = i := le_antisymm (le_of_not_gt hik) (le_of_not_gt hki)
          subst k
          simp [t]
    have hcount : (∑ k : Fin d, if k = i then (0 : ℝ) else 2) =
        2 * (d : ℝ) - 2 := by
      have hx (k : Fin d) : (if k = i then (0 : ℝ) else 2) =
          2 - (if k = i then 2 else 0) := by split_ifs <;> norm_num
      simp_rw [hx]
      simp [Finset.sum_sub_distrib]
      ring
    have hs : |∑ k : Fin d, t k| ≤ 2 * (d : ℝ) - 2 := by
      calc
        _ ≤ ∑ k : Fin d, |t k| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k : Fin d, if k = i then (0 : ℝ) else 2 :=
          Finset.sum_le_sum (fun k _ => ht k)
        _ = _ := hcount
    simp only [coordinate]
    change |(E i i).re - ∑ k : Fin d, t k| ≤ _
    have htri : |(E i i).re - ∑ k : Fin d, t k| ≤
        |(E i i).re| + |∑ k : Fin d, t k| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (E i i).re (-(∑ k : Fin d, t k))
    linarith [hre i i]
  · have hd2 : 2 ≤ d := by
      by_contra h
      have hd1 : d = 1 := by omega
      have heq : i = j := Fin.ext (by omega)
      exact hij heq
    have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
    by_cases hlt : i < j
    · have hc : |2 * (E i j).re| ≤ 2 := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        linarith [hre i j]
      simpa only [coordinate, ite_eq_right hij, ite_eq_left hlt] using
        hc.trans (by linarith : (2 : ℝ) ≤ 2 * (d : ℝ) - 1)
    · have hc : |-2 * (E j i).im| ≤ 2 := by
        have ha : |(-2 : ℝ)| = 2 := by norm_num
        rw [abs_mul, ha]
        linarith [him j i]
      simpa only [coordinate, ite_eq_right hij, ite_eq_right hlt] using
        hc.trans (by linarith : (2 : ℝ) ≤ 2 * (d : ℝ) - 1)

theorem candidate_error
    (d : ℕ) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 ≤ ε) (p : Mat d → ℝ)
    (hpos : ∀ E, IsEffect E → 0 ≤ p E)
    (hnorm : p 1 = 1)
    (hadd : ∀ E F, E.PosSemidef → F.PosSemidef → IsEffect (E + F) →
      |p (E + F) - p E - p F| ≤ ε)
    (E : Mat d) (hE : IsEffect E) :
    |p E - (Matrix.trace (candidate p * E)).re| ≤
      (2 * (d : ℝ) - 1)^2 * (6 * (d : ℝ)^2 + 1) * ε := by
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hK : (1 : ℝ) ≤ 2 * (d : ℝ) - 1 := by linarith
  have hf := finite_positive_family_error
    p ε (2 * (d : ℝ) - 1) hε hK hpos hadd hnorm
    (probe (d := d)) (coordinate E) probe_effect (probe_sum_bound d)
    (coordinate_bound hd E hE) E hE (coordinate_expansion E hE.1.isHermitian).symm
  rw [coordinate_trace p E hE.1.isHermitian]
  simpa only [probe_card, Nat.cast_pow] using hf

theorem approximate_effect_density
    (d : ℕ) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 ≤ ε)
    (p : Matrix (Fin d) (Fin d) ℂ → ℝ)
    (hpos : ∀ E : Matrix (Fin d) (Fin d) ℂ,
      E.PosSemidef → (1 - E).PosSemidef → 0 ≤ p E)
    (hnorm : p 1 = 1)
    (hadd : ∀ E F : Matrix (Fin d) (Fin d) ℂ,
      E.PosSemidef → F.PosSemidef →
      (E + F).PosSemidef ∧ (1 - (E + F)).PosSemidef →
      |p (E + F) - p E - p F| ≤ ε) :
    ∃ ρ : Matrix (Fin d) (Fin d) ℂ,
      ρ.PosSemidef ∧ Matrix.trace ρ = 1 ∧
      ∀ E : Matrix (Fin d) (Fin d) ℂ,
        E.PosSemidef → (1 - E).PosSemidef →
        |p E - (Matrix.trace (ρ * E)).re| ≤
          4 * (2 * (d : ℝ) - 1)^2 * (6 * (d : ℝ)^2 + 1) * ε := by
  let η : ℝ := (2 * (d : ℝ) - 1)^2 * (6 * (d : ℝ)^2 + 1) * ε
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hp : ∀ E : Mat d, IsEffect E → 0 ≤ p E :=
    fun E hE => hpos E hE.1 hE.2
  have hc (E : Mat d) (hE : IsEffect E) :
      |p E - (Matrix.trace (candidate p * E)).re| ≤ η :=
    candidate_error d hd ε hε p hp hnorm hadd E hE
  have hI : IsEffect (1 : Mat d) :=
    ⟨Matrix.PosSemidef.one, by simpa only [sub_self] using (Matrix.PosSemidef.zero (n := Fin d) (R := ℂ))⟩
  have htrace : |(Matrix.trace (candidate p)).re - 1| ≤ η := by
    simpa only [Matrix.mul_one, hnorm, abs_sub_comm] using hc 1 hI
  have hlower : ∀ E : Mat d, E.PosSemidef → (1 - E).PosSemidef →
      -η ≤ (Matrix.trace (candidate p * E)).re := by
    intro E hE hEc
    have he := (abs_le.mp (hc E ⟨hE,hEc⟩)).2
    have hpE := hpos E hE hEc
    linarith
  obtain ⟨ρ,hρ,htr,hr⟩ := D5.S3.Quantum.Foundation.EffectDensityRepair.uniform_density_repair
    d hd η hη (candidate p) (candidate_hermitian p) htrace hlower
  refine ⟨ρ,hρ,htr,?_⟩
  intro E hE hEc
  have he := hc E ⟨hE,hEc⟩
  have hrE := hr E hE hEc
  calc
    |p E - (Matrix.trace (ρ * E)).re| =
        |(p E - (Matrix.trace (candidate p * E)).re) +
          ((Matrix.trace (candidate p * E)).re - (Matrix.trace (ρ * E)).re)| := by
      congr 1
      ring
    _ ≤ |p E - (Matrix.trace (candidate p * E)).re| +
        |(Matrix.trace (candidate p * E)).re - (Matrix.trace (ρ * E)).re| := abs_add_le _ _
    _ = |p E - (Matrix.trace (candidate p * E)).re| +
        |(Matrix.trace (ρ * E)).re - (Matrix.trace (candidate p * E)).re| := by
      rw [abs_sub_comm (Matrix.trace (candidate p * E)).re (Matrix.trace (ρ * E)).re]
    _ ≤ η + 3 * η := add_le_add he hrE
    _ = 4 * (2 * (d : ℝ) - 1)^2 * (6 * (d : ℝ)^2 + 1) * ε := by
      dsimp [η]
      ring

end D5.S3.Quantum.Foundation.EffectDensityStability
