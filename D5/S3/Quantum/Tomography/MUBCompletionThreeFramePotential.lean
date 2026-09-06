/- GID: D5/S3/Quantum/Tomography/MUBCompletionThreeFramePotential
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/MUBCompletionThreeFramePotential
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fixed-edge double completion is exactly the zero locus of one nonnegative three-frame potential on the scaled relative Gram, and a structural zero gives unit margin. -/

import D5.S3.Quantum.Tomography.MUBCompletionRecoveredRowGram
import D5.S3.Quantum.Tomography.ZaunerFlatnessDefectCertificate

/- Library-search audit trail (2026-09-04):
   * Reuses `recoverFirst`, `recoverSecond`, the final one-relative-Gram
     equivalence, and the existing matrix-level scalar flatness theorem.
   * Reuses the structural-zero SOS certificate and the correct fixed-edge
     Zauner product. No competing Hadamard, collision, or completion carrier is
     introduced.
   * The scaled relative Gram `P = sqrt(d) K` avoids square roots in the formal
     system. Its normalized first defect is exactly the entrywise-unit defect
     of `K`; in dimension six the former `1/36` unitary-transition margin
     becomes the unit margin proved below.
-/

open scoped BigOperators Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.MUBCompletionThreeFramePotential

open Matrix
open D5.S3.Quantum.Tomography.MUBHadamardCompatibility
open D5.S3.Quantum.Tomography.MUBCubeCompatibility
open D5.S3.Quantum.Tomography.MUBCompletionSingleRelativeGram
open D5.S3.Quantum.Tomography.MUBCompletionRecoveredRowGram
open D5.S3.Quantum.Tomography.ComplexHadamardEntrywiseDefect
open D5.S3.Quantum.Tomography.ZaunerCompletionFibre
open D5.S3.Quantum.Tomography.ZaunerFlatnessDefectCertificate

/-- The entrywise flatness defect of the scaled relative Gram `P = sqrt(d) K`,
normalized so that it is exactly the unit-modulus defect of `K`.

Keeping `P` rather than `K` makes every coefficient rational and avoids a
formal square-root choice. -/
def scaledRelativeGramEntrywiseDefect
    {n : Type*} [Fintype n] (P : ComplexSquare n) : ℝ :=
  ((Fintype.card n : ℝ)⁻¹) ^ 2 *
    ∑ i, ∑ j,
      (Complex.normSq (P i j) - (Fintype.card n : ℝ)) ^ 2

/-- The exact three-frame potential on one scaled relative Gram.

The first term enforces flatness of `K = P / sqrt(d)`. The other two terms
enforce entrywise flatness of the rationally recovered factors
`d⁻¹ X P` and `d⁻¹ Y conjugate(P)`. -/
def completionThreeFramePotential
    {n : Type*} [Fintype n]
    (X Y P : ComplexSquare n) : ℝ :=
  scaledRelativeGramEntrywiseDefect P +
    (∑ i, ∑ j,
      (Complex.normSq ((recoverFirst X P) i j) - 1) ^ 2) +
    ∑ i, ∑ j,
      (Complex.normSq ((recoverSecond Y P) i j) - 1) ^ 2

/-- The normalized scaled-relative-Gram defect is nonnegative. -/
theorem scaledRelativeGramEntrywiseDefect_nonneg
    {n : Type*} [Fintype n] (P : ComplexSquare n) :
    0 ≤ scaledRelativeGramEntrywiseDefect P := by
  unfold scaledRelativeGramEntrywiseDefect
  positivity

/-- The full three-frame potential is a sum of squares with a nonnegative
coefficient. -/
theorem completionThreeFramePotential_nonneg
    {n : Type*} [Fintype n] (X Y P : ComplexSquare n) :
    0 ≤ completionThreeFramePotential X Y P := by
  unfold completionThreeFramePotential
  have hP := scaledRelativeGramEntrywiseDefect_nonneg P
  positivity

/-- Vanishing of the normalized first term is exactly flatness of the scaled
relative Gram: every entry has squared modulus `d`. -/
theorem scaledRelativeGramEntrywiseDefect_eq_zero_iff
    {n : Type*} [Fintype n] [Nonempty n]
    (P : ComplexSquare n) :
    scaledRelativeGramEntrywiseDefect P = 0 ↔
      ∀ i j, Complex.normSq (P i j) = (Fintype.card n : ℝ) := by
  have hd : (Fintype.card n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card n))
  have hCoefficient : ((Fintype.card n : ℝ)⁻¹) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (inv_ne_zero hd)
  constructor
  · intro hDefect
    have hSum :
        (∑ i, ∑ j,
          (Complex.normSq (P i j) - (Fintype.card n : ℝ)) ^ 2) = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left hCoefficient
      simpa [scaledRelativeGramEntrywiseDefect] using hDefect
    intro i j
    have hOuter :
        ∀ i ∈ (Finset.univ : Finset n),
          ∑ j,
            (Complex.normSq (P i j) - (Fintype.card n : ℝ)) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ ↦ Finset.sum_nonneg
          (fun j _ ↦ sq_nonneg
            (Complex.normSq (P i j) - (Fintype.card n : ℝ))))).mp hSum
    have hInner :
        ∀ j ∈ (Finset.univ : Finset n),
          (Complex.normSq (P i j) - (Fintype.card n : ℝ)) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ ↦ sq_nonneg
          (Complex.normSq (P i j) - (Fintype.card n : ℝ)))).mp
        (hOuter i (Finset.mem_univ i))
    nlinarith [hInner j (Finset.mem_univ j)]
  · intro hFlat
    unfold scaledRelativeGramEntrywiseDefect
    have hSum :
        (∑ i, ∑ j,
          (Complex.normSq (P i j) - (Fintype.card n : ℝ)) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      apply Finset.sum_eq_zero
      intro j hj
      rw [hFlat i j]
      norm_num
    rw [hSum, mul_zero]

/-- The three-frame potential vanishes exactly when all three entrywise
flatness systems hold. The row-Gram equations are intentionally absent here;
they are supplied separately by the scaled-Hadamard law of `P`. -/
theorem completionThreeFramePotential_eq_zero_iff
    {n : Type*} [Fintype n] [Nonempty n]
    (X Y P : ComplexSquare n) :
    completionThreeFramePotential X Y P = 0 ↔
      (∀ i j,
        Complex.normSq (P i j) = (Fintype.card n : ℝ)) ∧
      EntrywiseUnit (recoverFirst X P) ∧
      EntrywiseUnit (recoverSecond Y P) := by
  let firstDefect : ℝ :=
    ∑ i, ∑ j,
      (Complex.normSq ((recoverFirst X P) i j) - 1) ^ 2
  let secondDefect : ℝ :=
    ∑ i, ∑ j,
      (Complex.normSq ((recoverSecond Y P) i j) - 1) ^ 2
  have hPNonneg : 0 ≤ scaledRelativeGramEntrywiseDefect P :=
    scaledRelativeGramEntrywiseDefect_nonneg P
  have hFirstNonneg : 0 ≤ firstDefect := by
    dsimp [firstDefect]
    positivity
  have hSecondNonneg : 0 ≤ secondDefect := by
    dsimp [secondDefect]
    positivity
  constructor
  · intro hPotential
    have hPotential' :
        scaledRelativeGramEntrywiseDefect P + firstDefect + secondDefect = 0 := by
      simpa [completionThreeFramePotential, firstDefect, secondDefect,
        add_assoc] using hPotential
    have hPZero : scaledRelativeGramEntrywiseDefect P = 0 := by
      nlinarith
    have hFirstZero : firstDefect = 0 := by
      nlinarith
    have hSecondZero : secondDefect = 0 := by
      nlinarith
    exact ⟨
      (scaledRelativeGramEntrywiseDefect_eq_zero_iff P).mp hPZero,
      (entrywiseUnit_iff_sum_normSq_sub_one_sq_eq_zero
        (recoverFirst X P)).mpr (by simpa [firstDefect] using hFirstZero),
      (entrywiseUnit_iff_sum_normSq_sub_one_sq_eq_zero
        (recoverSecond Y P)).mpr (by simpa [secondDefect] using hSecondZero)⟩
  · rintro ⟨hPFlat, hFirstFlat, hSecondFlat⟩
    have hPZero :=
      (scaledRelativeGramEntrywiseDefect_eq_zero_iff P).mpr hPFlat
    have hFirstZero :=
      (entrywiseUnit_iff_sum_normSq_sub_one_sq_eq_zero
        (recoverFirst X P)).mp hFirstFlat
    have hSecondZero :=
      (entrywiseUnit_iff_sum_normSq_sub_one_sq_eq_zero
        (recoverSecond Y P)).mp hSecondFlat
    simpa [completionThreeFramePotential, hPZero, hFirstZero, hSecondZero]

/-- Fixed-edge double completion is exactly the zero locus of the three-frame
potential on the scaled-Hadamard row-Gram variety. -/
theorem doubleCompletion_iff_scaledRelativeGram_and_threeFramePotential_zero
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (H X Y : ComplexSquare n)
    (hH : EntrywiseUnit H)
    (hX : IsComplexHadamard X)
    (hY : IsComplexHadamard Y) :
    (∃ X' Y' : ComplexSquare n,
      IsComplexHadamard X' ∧
      IsComplexHadamard Y' ∧
      HadamardUnbiased X X' ∧
      (factorizedCubeMatrix H X Y)ᴴ *
          factorizedCubeMatrix H X' Y' =
        fun _ _ ↦ (Fintype.card n : ℂ)) ↔
    ∃ P : ComplexSquare n,
      P * Pᴴ =
        ((Fintype.card n : ℂ) * (Fintype.card n : ℂ)) •
          (1 : ComplexSquare n) ∧
      completionThreeFramePotential X Y P = 0 := by
  have hBase :=
    doubleCompletion_iff_scaledRelativeGram_and_twoDefects
      H X Y hH hX hY
  constructor
  · intro hCompletion
    rcases hBase.mp hCompletion with
      ⟨P, hPFlat, hPGram, hFirstDefect, hSecondDefect⟩
    refine ⟨P, hPGram, ?_⟩
    apply (completionThreeFramePotential_eq_zero_iff X Y P).mpr
    exact ⟨hPFlat,
      (entrywiseUnit_iff_sum_normSq_sub_one_sq_eq_zero
        (recoverFirst X P)).mpr hFirstDefect,
      (entrywiseUnit_iff_sum_normSq_sub_one_sq_eq_zero
        (recoverSecond Y P)).mpr hSecondDefect⟩
  · rintro ⟨P, hPGram, hPotential⟩
    rcases (completionThreeFramePotential_eq_zero_iff X Y P).mp hPotential with
      ⟨hPFlat, hFirstFlat, hSecondFlat⟩
    apply hBase.mpr
    exact ⟨P, hPFlat, hPGram,
      (entrywiseUnit_iff_sum_normSq_sub_one_sq_eq_zero
        (recoverFirst X P)).mp hFirstFlat,
      (entrywiseUnit_iff_sum_normSq_sub_one_sq_eq_zero
        (recoverSecond Y P)).mp hSecondFlat⟩

/-- A positive lower bound for the potential on the scaled-Hadamard constraint
set is an exact branch-exclusion certificate. -/
theorem no_doubleCompletion_of_threeFramePotential_margin
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (H X Y : ComplexSquare n)
    (hH : EntrywiseUnit H)
    (hX : IsComplexHadamard X)
    (hY : IsComplexHadamard Y)
    (epsilon : ℝ) (hEpsilon : 0 < epsilon)
    (hMargin : ∀ P : ComplexSquare n,
      (∀ i j,
        Complex.normSq (P i j) = (Fintype.card n : ℝ)) →
      P * Pᴴ =
        ((Fintype.card n : ℂ) * (Fintype.card n : ℂ)) •
          (1 : ComplexSquare n) →
      epsilon ≤ completionThreeFramePotential X Y P) :
    ¬ ∃ X' Y' : ComplexSquare n,
      IsComplexHadamard X' ∧
      IsComplexHadamard Y' ∧
      HadamardUnbiased X X' ∧
      (factorizedCubeMatrix H X Y)ᴴ *
          factorizedCubeMatrix H X' Y' =
        fun _ _ ↦ (Fintype.card n : ℂ) := by
  intro hCompletion
  rcases
      (doubleCompletion_iff_scaledRelativeGram_and_threeFramePotential_zero
        H X Y hH hX hY).mp hCompletion with
    ⟨P, hPGram, hPotential⟩
  have hPFlat :=
    (completionThreeFramePotential_eq_zero_iff X Y P).mp hPotential |>.1
  have hLower := hMargin P hPFlat hPGram
  rw [hPotential] at hLower
  linarith

/-- A structural zero of the scaled relative Gram contributes one full unit to
its normalized defect, independently of the dimension. -/
theorem one_le_scaledRelativeGramEntrywiseDefect_of_zero_entry
    {n : Type*} [Fintype n] [Nonempty n]
    (P : ComplexSquare n) (p q : n) (hzero : P p q = 0) :
    1 ≤ scaledRelativeGramEntrywiseDefect P := by
  let d : ℝ := Fintype.card n
  have hd : d ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card n))
  have hRaw :
      d ^ 2 ≤
        ∑ i, ∑ j, (Complex.normSq (P i j) - d) ^ 2 :=
    target_sq_le_entrywise_flatness_defect_of_zero_entry P d p q hzero
  calc
    1 = d⁻¹ ^ 2 * d ^ 2 := by field_simp [hd]
    _ ≤ d⁻¹ ^ 2 *
        (∑ i, ∑ j, (Complex.normSq (P i j) - d) ^ 2) :=
      mul_le_mul_of_nonneg_left hRaw (sq_nonneg d⁻¹)
    _ = scaledRelativeGramEntrywiseDefect P := by
      simp [scaledRelativeGramEntrywiseDefect, d]

/-- The first term is a lower bound for the full three-frame potential. -/
theorem scaledRelativeGramEntrywiseDefect_le_completionThreeFramePotential
    {n : Type*} [Fintype n]
    (X Y P : ComplexSquare n) :
    scaledRelativeGramEntrywiseDefect P ≤
      completionThreeFramePotential X Y P := by
  unfold completionThreeFramePotential
  have hFirst :
      0 ≤ ∑ i, ∑ j,
        (Complex.normSq ((recoverFirst X P) i j) - 1) ^ 2 := by
    positivity
  have hSecond :
      0 ≤ ∑ i, ∑ j,
        (Complex.normSq ((recoverSecond Y P) i j) - 1) ^ 2 := by
    positivity
  linarith

/-- A single structural zero in `P` gives the branch-independent unit margin
for the complete three-frame potential. -/
theorem one_le_completionThreeFramePotential_of_scaledRelativeGram_zero_entry
    {n : Type*} [Fintype n] [Nonempty n]
    (X Y P : ComplexSquare n) (p q : n) (hzero : P p q = 0) :
    1 ≤ completionThreeFramePotential X Y P :=
  le_trans
    (one_le_scaledRelativeGramEntrywiseDefect_of_zero_entry P p q hzero)
    (scaledRelativeGramEntrywiseDefect_le_completionThreeFramePotential X Y P)

/-- The scaled relative Gram corresponding to the normalized Zauner transition
`(1/2) Z₁ Z₁'ᴴ` in dimension six. Since `P = 6K_unitary`, the rational
coordinate is `P = 3 Z₁ Z₁'ᴴ`. -/
def zaunerScaledRelativeGram
    (F : Matrix (Fin 3) (Fin 3) ℂ)
    (x x' : Fin 3 → ℂ) :
    ComplexSquare (Fin 2 × Fin 3) :=
  (3 : ℂ) •
    (zaunerLeftFactor F x * (zaunerLeftFactor F x')ᴴ)

/-- Every off-mode structural zero survives the rational scaling to `P`. -/
theorem zaunerScaledRelativeGram_offMode_zero
    (F : Matrix (Fin 3) (Fin 3) ℂ)
    (x x' : Fin 3 → ℂ)
    (hF : F * Fᴴ = (1 : Matrix (Fin 3) (Fin 3) ℂ))
    (r s : Fin 2) (i j : Fin 3) (hij : i ≠ j) :
    zaunerScaledRelativeGram F x x' (r, i) (s, j) = 0 := by
  rw [zaunerScaledRelativeGram, Matrix.smul_apply,
    zaunerLeftFactor_mul_conjTranspose_offMode_zero
      F x x' hF r s i j hij]
  simp

/-- First branch-specific strong certificate: every Zauner canonical scaled
relative Gram has three-frame potential at least one. In the normalized
unitary-transition coordinate this is exactly the earlier `1/36` defect
margin, multiplied by the scaling factor `36`. -/
theorem zaunerCanonicalCompletion_threeFramePotential_ge_one
    (F : Matrix (Fin 3) (Fin 3) ℂ)
    (x x' : Fin 3 → ℂ)
    (hF : F * Fᴴ = (1 : Matrix (Fin 3) (Fin 3) ℂ))
    (X Y : ComplexSquare (Fin 2 × Fin 3)) :
    1 ≤ completionThreeFramePotential X Y
      (zaunerScaledRelativeGram F x x') := by
  exact
    one_le_completionThreeFramePotential_of_scaledRelativeGram_zero_entry
      X Y (zaunerScaledRelativeGram F x x')
      ((0 : Fin 2), (0 : Fin 3))
      ((0 : Fin 2), (1 : Fin 3))
      (zaunerScaledRelativeGram_offMode_zero
        F x x' hF (0 : Fin 2) (0 : Fin 2)
          (0 : Fin 3) (1 : Fin 3) (by decide))

/-- Consequently a Zauner canonical scaled relative Gram cannot lie on the
zero locus required by fixed-edge double completion. -/
theorem zaunerCanonicalCompletion_threeFramePotential_ne_zero
    (F : Matrix (Fin 3) (Fin 3) ℂ)
    (x x' : Fin 3 → ℂ)
    (hF : F * Fᴴ = (1 : Matrix (Fin 3) (Fin 3) ℂ))
    (X Y : ComplexSquare (Fin 2 × Fin 3)) :
    completionThreeFramePotential X Y
      (zaunerScaledRelativeGram F x x') ≠ 0 := by
  have hMargin :=
    zaunerCanonicalCompletion_threeFramePotential_ge_one
      F x x' hF X Y
  linarith

#print axioms scaledRelativeGramEntrywiseDefect_nonneg
#print axioms completionThreeFramePotential_nonneg
#print axioms scaledRelativeGramEntrywiseDefect_eq_zero_iff
#print axioms completionThreeFramePotential_eq_zero_iff
#print axioms doubleCompletion_iff_scaledRelativeGram_and_threeFramePotential_zero
#print axioms no_doubleCompletion_of_threeFramePotential_margin
#print axioms one_le_scaledRelativeGramEntrywiseDefect_of_zero_entry
#print axioms scaledRelativeGramEntrywiseDefect_le_completionThreeFramePotential
#print axioms one_le_completionThreeFramePotential_of_scaledRelativeGram_zero_entry
#print axioms zaunerScaledRelativeGram_offMode_zero
#print axioms zaunerCanonicalCompletion_threeFramePotential_ge_one
#print axioms zaunerCanonicalCompletion_threeFramePotential_ne_zero

end D5.S3.Quantum.Tomography.MUBCompletionThreeFramePotential
