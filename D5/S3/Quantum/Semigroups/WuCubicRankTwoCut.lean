/- GID: D5/S3/Quantum/Semigroups/WuCubicRankTwoCut
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicRankTwoCut
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp directed rank-two cut bounds at fixed even occupation and charge control the reverse cubic penalty. -/

import D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap
import Batteries.Tactic.OpenPrivate
import OmegaBuild.Commands

/-!
# Rank-two cut bounds for the two physical CAR jumps

The cut separates frame columns (0,1) from (2,3) in an arbitrary complex
unitary frame. The two directions have the same determinant correction and
opposite signs for the occupation imbalance.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace D5.S3.Quantum.Semigroups.WuCubicRankTwoCut

open WuCubicDirectedOccupationCap (Mat frameVector frameWeight frameWeight_eq_jumpWeight
  frameWeight_rowImbalance rowImbalance jumpWeight emptyProbability fullProbability
  evenProbability oddProbability)
open WuCubicOccupationEnvelope (edgeSum)

open private lowering_amplitudes jumpWeight_self frameWeight_marginals odd_eq_one_sub_even from
  D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap

/-- The empty-state mass of the first two frame columns. -/
def cutEmpty (U : unitary Mat) : ℝ :=
  emptyProbability (frameVector U 0) + emptyProbability (frameVector U 1)

/-- The full-state mass of the first two frame columns. -/
def cutFull (U : unitary Mat) : ℝ :=
  fullProbability (frameVector U 0) + fullProbability (frameVector U 1)

/-- The even mass of the first two frame columns, centered at one. -/
def cutEvenOffset (U : unitary Mat) : ℝ :=
  cutEmpty U + cutFull U - 1

/-- The empty minus full occupation of the first two frame columns. -/
def cutImbalance (U : unitary Mat) : ℝ :=
  cutEmpty U - cutFull U

/-- The cut weight with sources in the first two frame columns. -/
def reverseCutWeight (U : unitary Mat) : ℝ :=
  frameWeight U 2 0 + frameWeight U 2 1 + frameWeight U 3 0 + frameWeight U 3 1

/-- The cut weight with targets in the first two frame columns. -/
def forwardCutWeight (U : unitary Mat) : ℝ :=
  frameWeight U 0 2 + frameWeight U 0 3 + frameWeight U 1 2 + frameWeight U 1 3

private def evenMinor (x y : Fin 4 → ℂ) : ℂ := x 0 * y 3 - x 3 * y 0

private def oddMinor (x y : Fin 4 → ℂ) : ℂ := x 1 * y 2 - x 2 * y 1

private def interference (U : unitary Mat) : ℝ :=
  (conj (evenMinor (frameVector U 0) (frameVector U 1)) *
    oddMinor (frameVector U 0) (frameVector U 1)).re

private theorem jumpWeight_add_swap (x y : Fin 4 → ℂ) :
    jumpWeight x y + jumpWeight y x =
      evenProbability x * oddProbability y + oddProbability x * evenProbability y +
        2 * (conj (evenMinor x y) * oddMinor x y).re := by
  obtain ⟨hxy₀, hxy₁⟩ := lowering_amplitudes x y
  obtain ⟨hyx₀, hyx₁⟩ := lowering_amplitudes y x
  simp only [jumpWeight, Fin.sum_univ_two, hxy₀, hxy₁, hyx₀, hyx₁, evenProbability,
    emptyProbability, fullProbability, oddProbability, evenMinor, oddMinor,
    Complex.normSq_apply, Complex.star_def, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.conj_re, Complex.conj_im]
  ring

private theorem normSq_minor_add_inner (a b c d : ℂ) :
    Complex.normSq (a * d - b * c) + Complex.normSq (conj a * c + conj b * d) =
      (Complex.normSq a + Complex.normSq b) * (Complex.normSq c + Complex.normSq d) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

private theorem row_mass (U : unitary Mat) (i : Fin 4) :
    (∑ j, Complex.normSq ((U : Mat) i j)) = 1 := by
  have h : (U : Mat) * (U : Mat)ᴴ = 1 := Unitary.coe_mul_star_self U
  calc
    _ = (((U : Mat) * (U : Mat)ᴴ) i i).re := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
        Complex.mul_conj, Complex.re_sum, Complex.ofReal_re]
    _ = 1 := by rw [h, Matrix.one_apply_eq, Complex.one_re]

private theorem row_pair_mass_mem (U : unitary Mat) (i : Fin 4) :
    Complex.normSq ((U : Mat) i 0) + Complex.normSq ((U : Mat) i 1) ∈ Set.Icc 0 1 := by
  have h := row_mass U i
  rw [Fin.sum_univ_four] at h
  exact ⟨add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _),
    by linarith only [h, Complex.normSq_nonneg ((U : Mat) i 2),
      Complex.normSq_nonneg ((U : Mat) i 3)]⟩

private theorem cutEmpty_mem (U : unitary Mat) : cutEmpty U ∈ Set.Icc 0 1 :=
  row_pair_mass_mem U 0

private theorem cutFull_mem (U : unitary Mat) : cutFull U ∈ Set.Icc 0 1 :=
  row_pair_mass_mem U 3

private theorem normSq_evenMinor_le (U : unitary Mat) :
    Complex.normSq (evenMinor (frameVector U 0) (frameVector U 1)) ≤
      cutEmpty U * cutFull U := by
  have h := normSq_minor_add_inner ((U : Mat) 0 0) ((U : Mat) 0 1)
    ((U : Mat) 3 0) ((U : Mat) 3 1)
  rw [mul_comm ((U : Mat) 0 1) ((U : Mat) 3 0)] at h
  change Complex.normSq (evenMinor (frameVector U 0) (frameVector U 1)) + _ =
    cutEmpty U * cutFull U at h
  exact (le_add_of_nonneg_right (Complex.normSq_nonneg _)).trans_eq h

private theorem normSq_minor_difference (U : unitary Mat) :
    Complex.normSq (evenMinor (frameVector U 0) (frameVector U 1)) -
      Complex.normSq (oddMinor (frameVector U 0) (frameVector U 1)) = cutEvenOffset U := by
  let x := frameVector U 0
  let y := frameVector U 1
  let z := conj (x 0) * y 0 + conj (x 3) * y 3
  let w := conj (x 1) * y 1 + conj (x 2) * y 2
  have hU : (U : Mat)ᴴ * (U : Mat) = 1 := Unitary.coe_star_mul_self U
  have hxy : (∑ i, conj (x i) * y i) = 0 := by
    change ((U : Mat)ᴴ * (U : Mat)) 0 1 = 0
    rw [hU, Matrix.one_apply_ne (by decide : (0 : Fin 4) ≠ 1)]
  have hzw : z + w = 0 := by
    simpa only [z, w, Fin.sum_univ_four, add_assoc, add_left_comm, add_comm] using hxy
  have hz : z = -w := by linear_combination hzw
  have hnorm : Complex.normSq z = Complex.normSq w := by
    rw [hz, Complex.normSq_neg]
  have he : Complex.normSq (evenMinor x y) + Complex.normSq z =
      evenProbability x * evenProbability y := normSq_minor_add_inner (x 0) (x 3) (y 0) (y 3)
  have ho : Complex.normSq (oddMinor x y) + Complex.normSq w =
      oddProbability x * oddProbability y := normSq_minor_add_inner (x 1) (x 2) (y 1) (y 2)
  rw [hnorm] at he
  rw [show oddProbability x = 1 - evenProbability x from odd_eq_one_sub_even U 0,
    show oddProbability y = 1 - evenProbability y from odd_eq_one_sub_even U 1] at ho
  have hoffset : cutEvenOffset U = evenProbability x + evenProbability y - 1 := by
    simp only [cutEvenOffset, cutEmpty, cutFull, evenProbability, x, y]
    ring
  change Complex.normSq (evenMinor x y) - Complex.normSq (oddMinor x y) = cutEvenOffset U
  rw [hoffset]
  linear_combination he - ho

private theorem interference_le (U : unitary Mat) :
    interference U ≤
      Real.sqrt (cutEmpty U * cutFull U * ((1 - cutEmpty U) * (1 - cutFull U))) := by
  have hD := normSq_evenMinor_le U
  have hO : Complex.normSq (oddMinor (frameVector U 0) (frameVector U 1)) ≤
      (1 - cutEmpty U) * (1 - cutFull U) := by
    have hdiff := normSq_minor_difference U
    unfold cutEvenOffset at hdiff
    nlinarith only [hD, hdiff]
  unfold interference
  refine (Complex.re_le_norm _).trans ?_
  rw [Complex.norm_def, Complex.normSq_mul, Complex.normSq_conj]
  exact Real.sqrt_le_sqrt (mul_le_mul hD hO (Complex.normSq_nonneg _)
    (mul_nonneg (cutEmpty_mem U).1 (cutFull_mem U).1))

private theorem internalWeight_eq (U : unitary Mat) :
    frameWeight U 0 0 + frameWeight U 0 1 + frameWeight U 1 0 + frameWeight U 1 1 =
      1 - cutEvenOffset U ^ 2 + 2 * interference U := by
  simp only [frameWeight_eq_jumpWeight, jumpWeight_self]
  rw [add_assoc (evenProbability _ * oddProbability _) (jumpWeight _ _) (jumpWeight _ _),
    jumpWeight_add_swap]
  simp only [odd_eq_one_sub_even, cutEvenOffset, cutEmpty, cutFull, evenProbability, interference]
  ring

private theorem cutWeights_eq (U : unitary Mat) :
    reverseCutWeight U = 1 + cutEvenOffset U ^ 2 - cutImbalance U - 2 * interference U ∧
    forwardCutWeight U = 1 + cutEvenOffset U ^ 2 + cutImbalance U - 2 * interference U := by
  have hsum (i : Fin 4) : (∑ j, frameWeight U i j) + (∑ j, frameWeight U j i) = 2 := by
    rw [(frameWeight_marginals U i).1, (frameWeight_marginals U i).2]
    ring
  have hsum₀ := hsum 0
  have hsum₁ := hsum 1
  have himb₀ := frameWeight_rowImbalance U 0
  have himb₁ := frameWeight_rowImbalance U 1
  have hinternal := internalWeight_eq U
  simp only [rowImbalance, Fin.sum_univ_four] at hsum₀ hsum₁ himb₀ himb₁
  unfold reverseCutWeight forwardCutWeight cutImbalance cutEmpty cutFull
  constructor <;> linarith only [hsum₀, hsum₁, himb₀, himb₁, hinternal]

/-- Both directed cut weights in an arbitrary complex unitary frame obey the
square-root bound from the even and odd minors of its first two columns. -/
theorem cutWeight_ge_sqrt (U : unitary Mat) :
    let a := cutEmpty U
    let b := cutFull U
    let t := cutEvenOffset U
    let g := cutImbalance U
    1 + t ^ 2 - g - 2 * Real.sqrt (a * b * ((1 - a) * (1 - b))) ≤ reverseCutWeight U ∧
    1 + t ^ 2 + g - 2 * Real.sqrt (a * b * ((1 - a) * (1 - b))) ≤ forwardCutWeight U := by
  dsimp only
  obtain ⟨hr, hf⟩ := cutWeights_eq U
  constructor <;> linarith only [hr, hf, interference_le U]

private theorem sqrt_correction_le {a b : ℝ} (ha : a ∈ Set.Icc 0 1)
    (hb : b ∈ Set.Icc 0 1) :
    4 * Real.sqrt (a * b * ((1 - a) * (1 - b))) ≤ 1 - (a + b - 1) ^ 2 - (a - b) ^ 2 := by
  let q := 1 - (a + b - 1) ^ 2 - (a - b) ^ 2
  have hqa : 0 ≤ a * (1 - a) := mul_nonneg ha.1 (sub_nonneg.mpr ha.2)
  have hqb : 0 ≤ b * (1 - b) := mul_nonneg hb.1 (sub_nonneg.mpr hb.2)
  have hq_eq : q = 2 * (a * (1 - a) + b * (1 - b)) := by dsimp [q]; ring
  have hq : 0 ≤ q := by rw [hq_eq]; positivity
  have hsq : q ^ 2 - 16 * (a * b * ((1 - a) * (1 - b))) =
      4 * ((a + b - 1) ^ 2 * (a - b) ^ 2) := by dsimp [q]; ring
  have hsqrt : Real.sqrt (a * b * ((1 - a) * (1 - b))) ≤ q / 4 := by
    apply (Real.sqrt_le_left (show 0 ≤ q / 4 by positivity)).2
    nlinarith only [hsq, mul_nonneg (sq_nonneg (a + b - 1)) (sq_nonneg (a - b))]
  linarith only [hsqrt]

/-- A polynomial lower bound for each directed weight across the rank-two cut. -/
private theorem cutWeight_ge_polynomial (U : unitary Mat) :
    let t := cutEvenOffset U
    let g := cutImbalance U
    (1 - g) ^ 2 / 2 + 3 * t ^ 2 / 2 ≤ reverseCutWeight U ∧
    (1 + g) ^ 2 / 2 + 3 * t ^ 2 / 2 ≤ forwardCutWeight U := by
  dsimp only
  obtain ⟨hr, hf⟩ := cutWeight_ge_sqrt U
  have h := sqrt_correction_le (cutEmpty_mem U) (cutFull_mem U)
  change 4 * _ ≤ 1 - cutEvenOffset U ^ 2 - cutImbalance U ^ 2 at h
  constructor <;> nlinarith only [hr, hf, h]

private theorem reverseCubicPenalty_ge_cut (U : unitary Mat) {u : Fin 4 → ℝ}
    (hu : Monotone u) :
    (u 2 - u 1) ^ 3 * reverseCutWeight U ≤
      edgeSum (fun i j => frameWeight U j i * (u j - u i) ^ 3) := by
  have hweight (i j : Fin 4) : 0 ≤ frameWeight U i j :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hgap : 0 ≤ u 2 - u 1 := sub_nonneg.mpr (hu (by decide))
  have hcross {i j : Fin 4} (hi : i ≤ 1) (hj : 2 ≤ j) :
      (u 2 - u 1) ^ 3 * frameWeight U j i ≤ frameWeight U j i * (u j - u i) ^ 3 := by
    rw [mul_comm ((u 2 - u 1) ^ 3)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hgap (sub_le_sub (hu hj) (hu hi)) 3) (hweight j i)
  have h01 : 0 ≤ frameWeight U 1 0 * (u 1 - u 0) ^ 3 :=
    mul_nonneg (hweight _ _) (pow_nonneg (sub_nonneg.mpr (hu (by decide))) _)
  have h23 : 0 ≤ frameWeight U 3 2 * (u 3 - u 2) ^ 3 :=
    mul_nonneg (hweight _ _) (pow_nonneg (sub_nonneg.mpr (hu (by decide))) _)
  unfold edgeSum reverseCutWeight
  rw [mul_add, mul_add, mul_add]
  linarith only [h01, h23, hcross (i := 0) (j := 2) (by decide) (by decide),
    hcross (i := 0) (j := 3) (by decide) (by decide),
    hcross (i := 1) (j := 2) (by decide) (by decide),
    hcross (i := 1) (j := 3) (by decide) (by decide)]

/-- The reverse-edge sum also inherits the sharp square-root cut bound. -/
theorem reverseCubicPenalty_ge_sqrt (U : unitary Mat) {u : Fin 4 → ℝ} (hu : Monotone u) :
    let a := cutEmpty U
    let b := cutFull U
    (u 2 - u 1) ^ 3 *
        (1 + cutEvenOffset U ^ 2 - cutImbalance U -
          2 * Real.sqrt (a * b * ((1 - a) * (1 - b)))) ≤
      edgeSum (fun i j => frameWeight U j i * (u j - u i) ^ 3) :=
  (mul_le_mul_of_nonneg_left (cutWeight_ge_sqrt U).1
    (pow_nonneg (sub_nonneg.mpr (hu (by decide))) _)).trans (reverseCubicPenalty_ge_cut U hu)

/-- The reverse-edge sum in the cubic energy reduction pays at least the
cube of the middle gap times the polynomial cut bound. The result applies
to sorted cube roots and holds for every monotone real tuple. -/
private theorem reverseCubicPenalty_ge_polynomial (U : unitary Mat) {u : Fin 4 → ℝ}
    (hu : Monotone u) :
    (u 2 - u 1) ^ 3 * ((1 - cutImbalance U) ^ 2 / 2 + 3 * cutEvenOffset U ^ 2 / 2) ≤
      edgeSum (fun i j => frameWeight U j i * (u j - u i) ^ 3) :=
  (mul_le_mul_of_nonneg_left (cutWeight_ge_polynomial U).1
    (pow_nonneg (sub_nonneg.mpr (hu (by decide))) _)).trans (reverseCubicPenalty_ge_cut U hu)

private def sharpMatrix (a b : ℝ) : Mat :=
  !![↑(Real.sqrt a), 0, -↑(Real.sqrt (1 - a)), 0;
    ↑(Real.sqrt (1 - a)), 0, ↑(Real.sqrt a), 0;
    0, ↑(Real.sqrt (1 - b)), 0, ↑(Real.sqrt b);
    0, ↑(Real.sqrt b), 0, -↑(Real.sqrt (1 - b))]

private def sharpFrame {a b : ℝ} (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) :
    unitary Mat := by
  refine ⟨sharpMatrix a b, Unitary.mem_iff.mpr ⟨?_, ?_⟩⟩
  all_goals
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      norm_num [sharpMatrix, Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply,
        Fin.sum_univ_four, Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.add_re,
        Complex.add_im, Complex.neg_re, Complex.neg_im] <;>
      nlinarith only [Real.sq_sqrt ha.1, Real.sq_sqrt (sub_nonneg.mpr ha.2),
        Real.sq_sqrt hb.1, Real.sq_sqrt (sub_nonneg.mpr hb.2)]

/-- For every admissible pair of occupation masses, one physical frame attains
both square-root bounds simultaneously. -/
theorem cutWeight_sqrt_attained {a b : ℝ} (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) :
    ∃ U : unitary Mat, cutEmpty U = a ∧ cutFull U = b ∧
      reverseCutWeight U =
        1 + (a + b - 1) ^ 2 - (a - b) - 2 * Real.sqrt (a * b * ((1 - a) * (1 - b))) ∧
      forwardCutWeight U =
        1 + (a + b - 1) ^ 2 + (a - b) - 2 * Real.sqrt (a * b * ((1 - a) * (1 - b))) := by
  let U := sharpFrame ha hb
  have hA : cutEmpty U = a := by
    norm_num [cutEmpty, emptyProbability, frameVector, U, sharpFrame, sharpMatrix,
      Complex.normSq_ofReal, ← pow_two, Real.sq_sqrt ha.1]
  have hB : cutFull U = b := by
    norm_num [cutFull, fullProbability, frameVector, U, sharpFrame, sharpMatrix,
      Complex.normSq_ofReal, ← pow_two, Real.sq_sqrt hb.1]
  have hI : interference U = Real.sqrt (a * b * ((1 - a) * (1 - b))) := by
    rw [Real.sqrt_mul (mul_nonneg ha.1 hb.1), Real.sqrt_mul ha.1,
      Real.sqrt_mul (sub_nonneg.mpr ha.2)]
    norm_num [interference, evenMinor, oddMinor, frameVector, U, sharpFrame, sharpMatrix,
      Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
  obtain ⟨hr, hf⟩ := cutWeights_eq U
  refine ⟨U, hA, hB, ?_⟩
  simpa only [cutEvenOffset, cutImbalance, hA, hB, hI] using And.intro hr hf

end D5.S3.Quantum.Semigroups.WuCubicRankTwoCut
