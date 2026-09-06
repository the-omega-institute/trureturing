/- GID: D5/S3/Quantum/Tomography/SupportFaceFlatnessDefect
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/SupportFaceFlatnessDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A scaled-Hadamard row supported on two of six coordinates has exact flatness-defect floor twelve; six such rows give the sharp support-face floor seventy-two. -/

import D5.S3.Quantum.Tomography.MUBCompletionThreeFramePotential
import Mathlib.Tactic.FinCases

/- Library-search audit trail (2026-09-04):
   * Reuses `scaledRelativeGramEntrywiseDefect`, the existing scaled row-Gram
     convention, `Complex.normSq`, and Mathlib finite-sum enumeration.
   * Repository and pinned Mathlib searches found no declaration exposing this
     exact support-face Pythagoras identity on the present matrix carrier.
   * No new Hadamard, unitary, collision, or completion predicate is introduced.
-/

open scoped BigOperators Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.SupportFaceFlatnessDefect

open Matrix
open D5.S3.Quantum.Tomography.MUBHadamardCompatibility
open D5.S3.Quantum.Tomography.MUBCompletionThreeFramePotential

/-- A scalar row-Gram equation fixes the sum of squared complex moduli in each
row. The statement is normalized for the scaled-relative-Gram convention
`P Pᴴ = d² I`. -/
theorem row_normSq_sum_of_cardSq_rowGram
    {n : Type*} [Fintype n] [DecidableEq n]
    (P : ComplexSquare n)
    (hP : P * Pᴴ =
      ((Fintype.card n : ℂ) * (Fintype.card n : ℂ)) •
        (1 : ComplexSquare n))
    (i : n) :
    ∑ j, Complex.normSq (P i j) = (Fintype.card n : ℝ) ^ 2 := by
  have hEntry := congrFun (congrFun hP i) i
  have hReal := congrArg Complex.re hEntry
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.normSq_eq_conj_mul_self, Matrix.one_apply,
    mul_comm, pow_two] using hReal

/-- The raw six-column squared-deviation defect of one row. -/
def sixRowRawDefect
    (P : ComplexSquare (Fin 2 × Fin 3))
    (r : Fin 2) (i : Fin 3) : ℝ :=
  ∑ s, ∑ j,
    (Complex.normSq (P (r, i) (s, j)) - 6) ^ 2

/-- If a six-column row carries total squared norm `36` on only two active
coordinates, its raw defect from the flat target `6` is at least `432`.
After the global factor `1/36`, this is the rowwise margin `12`. -/
theorem sixRowRawDefect_ge_four_hundred_thirty_two
    (P : ComplexSquare (Fin 2 × Fin 3))
    (hP : P * Pᴴ = (36 : ℂ) •
      (1 : ComplexSquare (Fin 2 × Fin 3)))
    (hOff : ∀ (r s : Fin 2) (i j : Fin 3),
      i ≠ j → P (r, i) (s, j) = 0)
    (r : Fin 2) (i : Fin 3) :
    (432 : ℝ) ≤ sixRowRawDefect P r i := by
  have hGram : P * Pᴴ =
      (((Fintype.card (Fin 2 × Fin 3) : ℂ) *
        (Fintype.card (Fin 2 × Fin 3) : ℂ)) •
        (1 : ComplexSquare (Fin 2 × Fin 3))) := by
    norm_num at hP ⊢
    exact hP
  have hmass :=
    row_normSq_sum_of_cardSq_rowGram P hGram (r, i)
  fin_cases i
  · have h001 : P (r, 0) (0, 1) = 0 :=
      hOff r 0 0 1 (by decide)
    have h002 : P (r, 0) (0, 2) = 0 :=
      hOff r 0 0 2 (by decide)
    have h101 : P (r, 0) (1, 1) = 0 :=
      hOff r 1 0 1 (by decide)
    have h102 : P (r, 0) (1, 2) = 0 :=
      hOff r 1 0 2 (by decide)
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_three] at hmass
    rw [h001, h002, h101, h102] at hmass
    simp only [Complex.normSq_zero] at hmass
    norm_num [Fintype.card_prod] at hmass
    unfold sixRowRawDefect
    rw [Fin.sum_univ_two]
    simp only [Fin.sum_univ_three]
    rw [h001, h002, h101, h102]
    simp only [Complex.normSq_zero]
    norm_num
    nlinarith [sq_nonneg
      (Complex.normSq (P (r, 0) (0, 0)) -
        Complex.normSq (P (r, 0) (1, 0)))]
  · have h000 : P (r, 1) (0, 0) = 0 :=
      hOff r 0 1 0 (by decide)
    have h002 : P (r, 1) (0, 2) = 0 :=
      hOff r 0 1 2 (by decide)
    have h100 : P (r, 1) (1, 0) = 0 :=
      hOff r 1 1 0 (by decide)
    have h102 : P (r, 1) (1, 2) = 0 :=
      hOff r 1 1 2 (by decide)
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_three] at hmass
    rw [h000, h002, h100, h102] at hmass
    simp only [Complex.normSq_zero] at hmass
    norm_num [Fintype.card_prod] at hmass
    unfold sixRowRawDefect
    rw [Fin.sum_univ_two]
    simp only [Fin.sum_univ_three]
    rw [h000, h002, h100, h102]
    simp only [Complex.normSq_zero]
    norm_num
    nlinarith [sq_nonneg
      (Complex.normSq (P (r, 1) (0, 1)) -
        Complex.normSq (P (r, 1) (1, 1)))]
  · have h000 : P (r, 2) (0, 0) = 0 :=
      hOff r 0 2 0 (by decide)
    have h001 : P (r, 2) (0, 1) = 0 :=
      hOff r 0 2 1 (by decide)
    have h100 : P (r, 2) (1, 0) = 0 :=
      hOff r 1 2 0 (by decide)
    have h101 : P (r, 2) (1, 1) = 0 :=
      hOff r 1 2 1 (by decide)
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_three] at hmass
    rw [h000, h001, h100, h101] at hmass
    simp only [Complex.normSq_zero] at hmass
    norm_num [Fintype.card_prod] at hmass
    unfold sixRowRawDefect
    rw [Fin.sum_univ_two]
    simp only [Fin.sum_univ_three]
    rw [h000, h001, h100, h101]
    simp only [Complex.normSq_zero]
    norm_num
    nlinarith [sq_nonneg
      (Complex.normSq (P (r, 2) (0, 2)) -
        Complex.normSq (P (r, 2) (1, 2)))]

/-- Six rows, each supported on the two coordinates with its own mode index,
force the normalized scaled-relative-Gram defect to be at least `72`.
This is the exact squared distance from the corresponding Birkhoff support face
to the flat center in the repository's unaveraged normalization. -/
theorem twoModeSupport_scaledRelativeGramDefect_ge_seventy_two
    (P : ComplexSquare (Fin 2 × Fin 3))
    (hP : P * Pᴴ = (36 : ℂ) •
      (1 : ComplexSquare (Fin 2 × Fin 3)))
    (hOff : ∀ (r s : Fin 2) (i j : Fin 3),
      i ≠ j → P (r, i) (s, j) = 0) :
    (72 : ℝ) ≤ scaledRelativeGramEntrywiseDefect P := by
  have h00 := sixRowRawDefect_ge_four_hundred_thirty_two
    P hP hOff 0 0
  have h01 := sixRowRawDefect_ge_four_hundred_thirty_two
    P hP hOff 0 1
  have h02 := sixRowRawDefect_ge_four_hundred_thirty_two
    P hP hOff 0 2
  have h10 := sixRowRawDefect_ge_four_hundred_thirty_two
    P hP hOff 1 0
  have h11 := sixRowRawDefect_ge_four_hundred_thirty_two
    P hP hOff 1 1
  have h12 := sixRowRawDefect_ge_four_hundred_thirty_two
    P hP hOff 1 2
  unfold scaledRelativeGramEntrywiseDefect
  norm_num only [Fintype.card_prod, Fintype.card_fin, Nat.cast_ofNat]
  rw [Fintype.sum_prod_type]
  change (72 : ℝ) ≤ (6 : ℝ)⁻¹ ^ 2 *
    ∑ r : Fin 2, ∑ i : Fin 3, sixRowRawDefect P r i
  simp only [Fin.sum_univ_two, Fin.sum_univ_three]
  norm_num at h00 h01 h02 h10 h11 h12 ⊢
  nlinarith

/-- The same support-face floor transfers immediately to the complete
three-frame potential because its two recovered-factor defects are
nonnegative. -/
theorem twoModeSupport_completionThreeFramePotential_ge_seventy_two
    (X Y P : ComplexSquare (Fin 2 × Fin 3))
    (hP : P * Pᴴ = (36 : ℂ) •
      (1 : ComplexSquare (Fin 2 × Fin 3)))
    (hOff : ∀ (r s : Fin 2) (i j : Fin 3),
      i ≠ j → P (r, i) (s, j) = 0) :
    (72 : ℝ) ≤ completionThreeFramePotential X Y P := by
  exact le_trans
    (twoModeSupport_scaledRelativeGramDefect_ge_seventy_two P hP hOff)
    (scaledRelativeGramEntrywiseDefect_le_completionThreeFramePotential
      X Y P)

#print axioms row_normSq_sum_of_cardSq_rowGram
#print axioms sixRowRawDefect_ge_four_hundred_thirty_two
#print axioms twoModeSupport_scaledRelativeGramDefect_ge_seventy_two
#print axioms twoModeSupport_completionThreeFramePotential_ge_seventy_two

end D5.S3.Quantum.Tomography.SupportFaceFlatnessDefect
