/- GID: D5/S3/Quantum/Tomography/ComplexHadamardEntrywiseDefect
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/ComplexHadamardEntrywiseDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Entrywise complex-Hadamard flatness is exactly the vanishing of one nonnegative finite squared-deviation sum. -/

import D5.S3.Quantum.Tomography.MUBCompletionRelativeGramEquivalence

/- Library-search audit trail (2026-09-03):
   * Reuses `EntrywiseUnit` and `IsComplexHadamard`; no collision, frame
     potential, or alternative Hadamard predicate is introduced.
   * Reuses `Finset.sum_eq_zero_iff_of_nonneg` and the ordered-ring square
     API. Repository and Mathlib searches found no theorem already exposing
     this exact matrix-level flatness equivalence on the present carrier.
-/

open scoped BigOperators Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.ComplexHadamardEntrywiseDefect

open Matrix
open D5.S3.Quantum.Tomography.MUBHadamardCompatibility

/-- All entrywise unit-modulus equations are equivalent to one nonnegative
squared-deviation sum. The sum is deliberately kept inline, so this theorem
does not create a competing collision or frame-potential definition. -/
theorem entrywiseUnit_iff_sum_normSq_sub_one_sq_eq_zero
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) :
    EntrywiseUnit A ↔
      ∑ i, ∑ j, (Complex.normSq (A i j) - 1) ^ 2 = 0 := by
  constructor
  · intro hUnit
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    rw [hUnit i j]
    norm_num
  · intro hSum
    intro i j
    have hOuter :
        ∀ i ∈ (Finset.univ : Finset m),
          ∑ j, (Complex.normSq (A i j) - 1) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ sq_nonneg _))).mp hSum
    have hInner :
        ∀ j ∈ (Finset.univ : Finset n),
          (Complex.normSq (A i j) - 1) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ ↦ sq_nonneg _)).mp
          (hOuter i (Finset.mem_univ i))
    have hSquare := hInner j (Finset.mem_univ j)
    nlinarith

/-- A finite square matrix is complex Hadamard exactly when its single scalar
entrywise defect vanishes and its stored row Gram equation holds. -/
theorem isComplexHadamard_iff_scalarDefect_and_rowGram
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : ComplexSquare n) :
    IsComplexHadamard A ↔
      (∑ i, ∑ j, (Complex.normSq (A i j) - 1) ^ 2 = 0) ∧
      A * Aᴴ = (Fintype.card n : ℂ) • (1 : ComplexSquare n) := by
  constructor
  · intro hA
    exact ⟨
      (entrywiseUnit_iff_sum_normSq_sub_one_sq_eq_zero A).mp hA.1,
      hA.2⟩
  · rintro ⟨hDefect, hGram⟩
    exact ⟨
      (entrywiseUnit_iff_sum_normSq_sub_one_sq_eq_zero A).mpr hDefect,
      hGram⟩

#print axioms entrywiseUnit_iff_sum_normSq_sub_one_sq_eq_zero
#print axioms isComplexHadamard_iff_scalarDefect_and_rowGram

end D5.S3.Quantum.Tomography.ComplexHadamardEntrywiseDefect
