/- GID: D5/S3/Quantum/Tomography/ZaunerFlatnessDefectCertificate
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/ZaunerFlatnessDefectCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A structural zero gives an exact positive sum-of-squares flatness-defect margin, excluding mutually unbiased Zauner canonical completions. -/

import D5.S3.Quantum.Tomography.ComplexHadamardEntrywiseDefect
import D5.S3.Quantum.Tomography.ZaunerCompletionFibre

/- Library-search audit trail (2026-09-04):
   * Reuses the inline squared entrywise defect introduced by
     `ComplexHadamardEntrywiseDefect`; no competing frame-potential or
     collision definition is introduced.
   * Reuses the correct fixed-edge structural-zero theorem
     `zaunerLeftFactor_mul_conjTranspose_offMode_zero`.
   * Pinned Mathlib supplies `Finset.single_le_sum`, `Finset.sum_nonneg`,
     `sq_nonneg`, and `sq_pos_of_ne_zero`.
-/

open scoped BigOperators Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.ZaunerFlatnessDefectCertificate

open Matrix
open D5.S3.Quantum.Tomography.ZaunerCompletionFibre

/-- One exact zero entry contributes the full squared target modulus to the
entrywise flatness defect. Every remaining summand is a square, so this is a
literal sum-of-squares lower-bound certificate. -/
theorem target_sq_le_entrywise_flatness_defect_of_zero_entry
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) (target : ℝ) (p : m) (q : n)
    (hzero : A p q = 0) :
    target ^ 2 ≤
      ∑ i, ∑ j, (Complex.normSq (A i j) - target) ^ 2 := by
  have hInner :
      (Complex.normSq (A p q) - target) ^ 2 ≤
        ∑ j, (Complex.normSq (A p j) - target) ^ 2 := by
    exact Finset.single_le_sum
      (fun j _ ↦ sq_nonneg (Complex.normSq (A p j) - target))
      (Finset.mem_univ q)
  have hOuter :
      (∑ j, (Complex.normSq (A p j) - target) ^ 2) ≤
        ∑ i, ∑ j, (Complex.normSq (A i j) - target) ^ 2 := by
    exact Finset.single_le_sum
      (fun i _ ↦ Finset.sum_nonneg
        (fun j _ ↦ sq_nonneg (Complex.normSq (A i j) - target)))
      (Finset.mem_univ p)
  calc
    target ^ 2 = (Complex.normSq (A p q) - target) ^ 2 := by
      simp [hzero, pow_two]
    _ ≤ ∑ j, (Complex.normSq (A p j) - target) ^ 2 := hInner
    _ ≤ ∑ i, ∑ j, (Complex.normSq (A i j) - target) ^ 2 := hOuter

/-- At a nonzero target modulus, one structural zero makes the scalar
entrywise defect strictly positive. -/
theorem entrywise_flatness_defect_pos_of_zero_entry
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) (target : ℝ) (p : m) (q : n)
    (htarget : target ≠ 0) (hzero : A p q = 0) :
    0 < ∑ i, ∑ j, (Complex.normSq (A i j) - target) ^ 2 := by
  exact lt_of_lt_of_le (sq_pos_of_ne_zero htarget)
    (target_sq_le_entrywise_flatness_defect_of_zero_entry
      A target p q hzero)

/-- The normalized fixed-edge transition between two canonical Zauner
completions is one half of the unnormalized left-factor product. Its structural
zero gives the exact six-dimensional MUB defect margin `1 / 36`. -/
theorem zaunerCanonicalCompletion_normalized_defect_ge_one_div_thirty_six
    (F : Matrix (Fin 3) (Fin 3) ℂ)
    (x x' : Fin 3 → ℂ)
    (hF : F * Fᴴ = (1 : Matrix (Fin 3) (Fin 3) ℂ)) :
    (1 / 36 : ℝ) ≤
      ∑ p, ∑ q,
        (Complex.normSq
          ((((2 : ℂ)⁻¹) •
            (zaunerLeftFactor F x * (zaunerLeftFactor F x')ᴴ)) p q) -
          (1 / 6 : ℝ)) ^ 2 := by
  have hzero :
      ((((2 : ℂ)⁻¹) •
        (zaunerLeftFactor F x * (zaunerLeftFactor F x')ᴴ))
          ((0 : Fin 2), (0 : Fin 3))
          ((0 : Fin 2), (1 : Fin 3))) = 0 := by
    rw [Matrix.smul_apply,
      zaunerLeftFactor_mul_conjTranspose_offMode_zero
        F x x' hF (0 : Fin 2) (0 : Fin 2)
          (0 : Fin 3) (1 : Fin 3) (by decide)]
    simp
  have hCertificate :=
    target_sq_le_entrywise_flatness_defect_of_zero_entry
      (((2 : ℂ)⁻¹) •
        (zaunerLeftFactor F x * (zaunerLeftFactor F x')ᴴ))
      (1 / 6 : ℝ)
      ((0 : Fin 2), (0 : Fin 3))
      ((0 : Fin 2), (1 : Fin 3))
      hzero
  norm_num at hCertificate ⊢
  exact hCertificate

/-- The same structural zero excludes exact mutual unbiasedness of the two
normalized canonical completions. -/
theorem zaunerCanonicalCompletion_normalized_not_flat
    (F : Matrix (Fin 3) (Fin 3) ℂ)
    (x x' : Fin 3 → ℂ)
    (hF : F * Fᴴ = (1 : Matrix (Fin 3) (Fin 3) ℂ)) :
    ¬ ∀ p q,
      Complex.normSq
        ((((2 : ℂ)⁻¹) •
          (zaunerLeftFactor F x * (zaunerLeftFactor F x')ᴴ)) p q) =
        (1 / 6 : ℝ) := by
  intro hflat
  have h := hflat
    ((0 : Fin 2), (0 : Fin 3))
    ((0 : Fin 2), (1 : Fin 3))
  rw [Matrix.smul_apply,
    zaunerLeftFactor_mul_conjTranspose_offMode_zero
      F x x' hF (0 : Fin 2) (0 : Fin 2)
        (0 : Fin 3) (1 : Fin 3) (by decide)] at h
  norm_num at h

/-- The exact branch certificate packages both the positive SOS margin and the
resulting flatness exclusion. -/
theorem zaunerCanonicalCompletion_exact_sos_exclusion
    (F : Matrix (Fin 3) (Fin 3) ℂ)
    (x x' : Fin 3 → ℂ)
    (hF : F * Fᴴ = (1 : Matrix (Fin 3) (Fin 3) ℂ)) :
    ((1 / 36 : ℝ) ≤
      ∑ p, ∑ q,
        (Complex.normSq
          ((((2 : ℂ)⁻¹) •
            (zaunerLeftFactor F x * (zaunerLeftFactor F x')ᴴ)) p q) -
          (1 / 6 : ℝ)) ^ 2) ∧
    ¬ ∀ p q,
      Complex.normSq
        ((((2 : ℂ)⁻¹) •
          (zaunerLeftFactor F x * (zaunerLeftFactor F x')ᴴ)) p q) =
        (1 / 6 : ℝ) := by
  exact ⟨
    zaunerCanonicalCompletion_normalized_defect_ge_one_div_thirty_six
      F x x' hF,
    zaunerCanonicalCompletion_normalized_not_flat F x x' hF⟩

#print axioms target_sq_le_entrywise_flatness_defect_of_zero_entry
#print axioms entrywise_flatness_defect_pos_of_zero_entry
#print axioms zaunerCanonicalCompletion_normalized_defect_ge_one_div_thirty_six
#print axioms zaunerCanonicalCompletion_normalized_not_flat
#print axioms zaunerCanonicalCompletion_exact_sos_exclusion

end D5.S3.Quantum.Tomography.ZaunerFlatnessDefectCertificate
