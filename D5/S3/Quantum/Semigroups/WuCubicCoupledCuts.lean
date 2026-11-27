/- GID: D5/S3/Quantum/Semigroups/WuCubicCoupledCuts
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicCoupledCuts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The middle cut controls both adjacent overlaps in an arbitrary complex CAR jump frame. -/

import D5.S3.Quantum.Semigroups.WuCubicRankTwoCut
import Batteries.Tactic.OpenPrivate
import OmegaBuild.Commands

/-!
# Adjacent and middle spectral cuts for the two CAR jumps

The edges crossing two consecutive spectral cuts share a lower bound from
the middle cut. The exact correction on each side is a difference of diagonal
jump weights, determined by the odd occupation of the corresponding columns.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace D5.S3.Quantum.Semigroups.WuCubicCoupledCuts

open WuCubicDirectedOccupationCap (Mat frameVector frameWeight frameWeight_eq_jumpWeight
  jumpWeight evenProbability oddProbability emptyProbability fullProbability)
open WuCubicOccupationEnvelope (sym)
open WuCubicRankTwoCut

open private jumpWeight_self frameWeight_marginals odd_eq_one_sub_even from
  D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap
open private row_mass cutEmpty_mem cutFull_mem cutWeight_ge_polynomial evenMinor oddMinor
  jumpWeight_add_swap normSq_minor_add_inner sqrt_correction_le from
  D5.S3.Quantum.Semigroups.WuCubicRankTwoCut

/-- The symmetric weight of the edges crossing both the first and middle cuts. -/
def lowerAdjacentCutWeight (U : unitary Mat) : ℝ :=
  sym (frameWeight U) 0 2 + sym (frameWeight U) 0 3

/-- The symmetric weight of the edges crossing both the middle and last cuts. -/
def upperAdjacentCutWeight (U : unitary Mat) : ℝ :=
  sym (frameWeight U) 0 3 + sym (frameWeight U) 1 3

private theorem combinedMarginal (U : unitary Mat) (i : Fin 4) :
    (∑ j, sym (frameWeight U) i j) = 2 := by
  simp only [sym, Finset.sum_add_distrib, (frameWeight_marginals U i).1,
    (frameWeight_marginals U i).2]
  ring

private theorem frameWeight_diagonal (U : unitary Mat) (i : Fin 4) :
    frameWeight U i i =
      oddProbability (frameVector U i) * (1 - oddProbability (frameVector U i)) := by
  rw [frameWeight_eq_jumpWeight, jumpWeight_self, odd_eq_one_sub_even]
  ring

/-- Half the total middle cut weight and the diagonal differences determine
both adjacent overlaps exactly. -/
theorem adjacentCutWeight_eq (U : unitary Mat) :
    let f := fun i => oddProbability (frameVector U i) * (1 - oddProbability (frameVector U i))
    lowerAdjacentCutWeight U = (forwardCutWeight U + reverseCutWeight U) / 2 + f 1 - f 0 ∧
    upperAdjacentCutWeight U = (forwardCutWeight U + reverseCutWeight U) / 2 + f 2 - f 3 := by
  have h₀ := combinedMarginal U 0
  have h₁ := combinedMarginal U 1
  have h₂ := combinedMarginal U 2
  have h₃ := combinedMarginal U 3
  simp only [Fin.sum_univ_four, sym, frameWeight_diagonal] at h₀ h₁ h₂ h₃
  simp only [lowerAdjacentCutWeight, upperAdjacentCutWeight, forwardCutWeight,
    reverseCutWeight, sym]
  constructor
  · linarith only [h₀, h₁]
  · linarith only [h₂, h₃]

/-- The absolute even offset and absolute charge imbalance of the middle cut
sum to at most one. -/
theorem abs_cutEvenOffset_add_abs_cutImbalance_le_one (U : unitary Mat) :
    |cutEvenOffset U| + |cutImbalance U| ≤ 1 := by
  have ha := cutEmpty_mem U
  have hb := cutFull_mem U
  have h₁ : |cutImbalance U| ≤ 1 + cutEvenOffset U := by
    rw [abs_le]
    unfold cutImbalance cutEvenOffset
    constructor <;> linarith only [ha.1, hb.1]
  have h₂ : |cutImbalance U| ≤ 1 - cutEvenOffset U := by
    rw [abs_le]
    unfold cutImbalance cutEvenOffset
    constructor <;> linarith only [ha.2, hb.2]
  have hoffset : |cutEvenOffset U| ≤ 1 - |cutImbalance U| := by
    rw [abs_le]
    constructor <;> linarith only [h₁, h₂]
  linarith only [hoffset]

/-- A lower endpoint for the absolute middle-cut imbalance gives an extra
quadratic occupation penalty, including at absolute imbalance one. -/
theorem middleCutWeight_ge_sqrt_surplus (U : unitary Mat) {lo : ℝ}
    (hlo : 0 ≤ lo) (hlt : lo < 1) (hle : lo ≤ |cutImbalance U|) :
    let u := cutEvenOffset U
    let v := |cutImbalance U|
    1 + v ^ 2 + 3 * u ^ 2 + (2 * lo ^ 2 / (1 - lo ^ 2)) * u ^ 2 ≤
      forwardCutWeight U + reverseCutWeight U := by
  let a := cutEmpty U
  let b := cutFull U
  let u := cutEvenOffset U
  let v := |cutImbalance U|
  let A := 1 - u ^ 2 - v ^ 2
  let s := 4 * Real.sqrt (a * b * ((1 - a) * (1 - b)))
  have ha : a ∈ Set.Icc (0 : ℝ) 1 := cutEmpty_mem U
  have hb : b ∈ Set.Icc (0 : ℝ) 1 := cutFull_mem U
  have hab : 0 ≤ a * b * ((1 - a) * (1 - b)) :=
    mul_nonneg (mul_nonneg ha.1 hb.1)
      (mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hb.2))
  have hv_sq : v ^ 2 = (a - b) ^ 2 := sq_abs _
  have hs_nonneg : 0 ≤ s := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hs_le : s ≤ A := by
    dsimp only [A]
    rw [hv_sq]
    exact sqrt_correction_le ha hb
  have hs_sq : s ^ 2 = 16 * (a * b * ((1 - a) * (1 - b))) := by
    dsimp only [s]
    rw [mul_pow, Real.sq_sqrt hab]
    ring
  have hproduct : (A - s) * (A + s) = 4 * u ^ 2 * v ^ 2 := calc
    _ = A ^ 2 - s ^ 2 := by ring
    _ = 4 * u ^ 2 * v ^ 2 := by
      rw [hs_sq]
      dsimp only [A]
      rw [hv_sq]
      change (1 - (a + b - 1) ^ 2 - (a - b) ^ 2) ^ 2 - _ =
        4 * (a + b - 1) ^ 2 * (a - b) ^ 2
      ring
  have hlo_sq : lo ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ hlo hle 2
  have hden : 0 < 1 - lo ^ 2 := by
    have h := mul_pos (sub_pos.mpr hlt) (show 0 < 1 + lo by linarith only [hlo])
    nlinarith only [h]
  have hsum_le : A + s ≤ 2 * (1 - lo ^ 2) := calc
    A + s ≤ 2 * A := by linarith only [hs_le]
    _ ≤ 2 * (1 - lo ^ 2) := by
      dsimp only [A]
      linarith only [hlo_sq, sq_nonneg u]
  -- Multiply before dividing so the bound also covers a vanishing sum A + s.
  have hscale := mul_le_mul_of_nonneg_left hsum_le (sub_nonneg.mpr hs_le)
  have hnum := mul_le_mul_of_nonneg_right hlo_sq (sq_nonneg u)
  have hsurplus : (2 * lo ^ 2 / (1 - lo ^ 2)) * u ^ 2 ≤ A - s := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    linarith only [hproduct, hscale, hnum]
  have hmiddle : 2 + 2 * u ^ 2 - s ≤ forwardCutWeight U + reverseCutWeight U := by
    obtain ⟨hReverse, hForward⟩ := cutWeight_ge_sqrt U
    dsimp only [s]
    linarith only [hReverse, hForward]
  change 1 + v ^ 2 + 3 * u ^ 2 + (2 * lo ^ 2 / (1 - lo ^ 2)) * u ^ 2 ≤ _
  dsimp only [A] at hsurplus
  linarith only [hmiddle, hsurplus]

/-- Each adjacent overlap inherits half the middle-cut surplus, with its
exact diagonal correction. -/
theorem adjacentCutWeight_ge_sqrt_surplus (U : unitary Mat) {lo : ℝ}
    (hlo : 0 ≤ lo) (hlt : lo < 1) (hle : lo ≤ |cutImbalance U|) :
    let u := cutEvenOffset U
    let v := |cutImbalance U|
    let f := fun i => oddProbability (frameVector U i) * (1 - oddProbability (frameVector U i))
    let halfCut := (1 + v ^ 2 + 3 * u ^ 2 + (2 * lo ^ 2 / (1 - lo ^ 2)) * u ^ 2) / 2
    halfCut + f 1 - f 0 ≤ lowerAdjacentCutWeight U ∧
    halfCut + f 2 - f 3 ≤ upperAdjacentCutWeight U := by
  have hmiddle := middleCutWeight_ge_sqrt_surplus U hlo hlt hle
  obtain ⟨hLower, hUpper⟩ := adjacentCutWeight_eq U
  constructor
  · linarith only [hmiddle, hLower]
  · linarith only [hmiddle, hUpper]

private theorem oddPairMass_eq (U : unitary Mat) :
    let t := fun i => oddProbability (frameVector U i)
    let u := -cutEvenOffset U
    t 0 + t 1 = 1 + u ∧ t 2 + t 3 = 1 - u := by
  let t : Fin 4 → ℝ := fun i => oddProbability (frameVector U i)
  let u := -cutEvenOffset U
  have hleft : t 0 + t 1 = 1 + u := by
    simp only [t, u, odd_eq_one_sub_even, evenProbability, cutEvenOffset, cutEmpty, cutFull]
    ring
  have htotal : t 0 + t 1 + t 2 + t 3 = 2 := by
    have h₁ := row_mass U 1
    have h₂ := row_mass U 2
    simp only [Fin.sum_univ_four] at h₁ h₂
    simp only [t, oddProbability, frameVector]
    linarith only [h₁, h₂]
  have hright : t 2 + t 3 = 1 - u := by
    linarith only [hleft, htotal]
  exact ⟨hleft, hright⟩

/-- The signed odd offset of the first two columns couples the lower and
upper adjacent overlaps to the same middle cut. -/
theorem adjacentCutWeight_ge_signed (U : unitary Mat) :
    let t := fun i => oddProbability (frameVector U i)
    let u := -cutEvenOffset U
    let v := |cutImbalance U|
    1 + v ^ 2 + 3 * u ^ 2 ≤ forwardCutWeight U + reverseCutWeight U ∧
    (1 + v ^ 2) / 2 + (2 * t 0 - 1) * u + u ^ 2 / 2 ≤ lowerAdjacentCutWeight U ∧
    (1 + v ^ 2) / 2 - (2 * t 3 - 1) * u + u ^ 2 / 2 ≤ upperAdjacentCutWeight U := by
  let t : Fin 4 → ℝ := fun i => oddProbability (frameVector U i)
  let u := -cutEvenOffset U
  let v := |cutImbalance U|
  obtain ⟨hleft, hright⟩ := oddPairMass_eq U
  have hmiddle : 1 + v ^ 2 + 3 * u ^ 2 ≤ forwardCutWeight U + reverseCutWeight U := by
    obtain ⟨hr, hf⟩ := cutWeight_ge_polynomial U
    simp only [v, u, sq_abs, neg_sq]
    linarith only [hr, hf]
  have hLowerCorrection :
      t 1 * (1 - t 1) - t 0 * (1 - t 0) = (2 * t 0 - 1) * u - u ^ 2 := by
    rw [show t 1 = 1 + u - t 0 by linarith only [hleft]]
    ring
  have hUpperCorrection :
      t 2 * (1 - t 2) - t 3 * (1 - t 3) = -(2 * t 3 - 1) * u - u ^ 2 := by
    rw [show t 2 = 1 - u - t 3 by linarith only [hright]]
    ring
  obtain ⟨hLower, hUpper⟩ := adjacentCutWeight_eq U
  change lowerAdjacentCutWeight U = (forwardCutWeight U + reverseCutWeight U) / 2 +
    t 1 * (1 - t 1) - t 0 * (1 - t 0) at hLower
  change upperAdjacentCutWeight U = (forwardCutWeight U + reverseCutWeight U) / 2 +
    t 2 * (1 - t 2) - t 3 * (1 - t 3) at hUpper
  refine ⟨hmiddle, ?_, ?_⟩
  · change (1 + v ^ 2) / 2 + (2 * t 0 - 1) * u + u ^ 2 / 2 ≤ _
    linarith only [hmiddle, hLower, hLowerCorrection]
  · change (1 + v ^ 2) / 2 - (2 * t 3 - 1) * u + u ^ 2 / 2 ≤ _
    linarith only [hmiddle, hUpper, hUpperCorrection]

private theorem sym_frameWeight_le_one (U : unitary Mat) (i j : Fin 4) :
    sym (frameWeight U) i j ≤ 1 := by
  let x := frameVector U i
  let y := frameVector U j
  have he : Complex.normSq (evenMinor x y) ≤ evenProbability x * evenProbability y :=
    (le_add_of_nonneg_right (Complex.normSq_nonneg _)).trans_eq
      (normSq_minor_add_inner (x 0) (x 3) (y 0) (y 3))
  have ho : Complex.normSq (oddMinor x y) ≤ oddProbability x * oddProbability y :=
    (le_add_of_nonneg_right (Complex.normSq_nonneg _)).trans_eq
      (normSq_minor_add_inner (x 1) (x 2) (y 1) (y 2))
  have hcross : 2 * (conj (evenMinor x y) * oddMinor x y).re ≤
      Complex.normSq (evenMinor x y) + Complex.normSq (oddMinor x y) := by
    have h := Complex.normSq_nonneg (evenMinor x y - oddMinor x y)
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.conj_re, Complex.conj_im] at h ⊢
    linarith only [h]
  have hx : oddProbability x = 1 - evenProbability x := odd_eq_one_sub_even U i
  have hy : oddProbability y = 1 - evenProbability y := odd_eq_one_sub_even U j
  simp only [sym, frameWeight_eq_jumpWeight]
  change jumpWeight x y + jumpWeight y x ≤ 1
  calc
    _ ≤ (evenProbability x + oddProbability x) * (evenProbability y + oddProbability y) := by
      rw [jumpWeight_add_swap]
      linarith only [he, ho, hcross]
    _ = 1 := by rw [hx, hy]; ring

private theorem singletonCutWeight_eq (U : unitary Mat) :
    let y := fun i => 1 - 2 * oddProbability (frameVector U i)
    let S := sym (frameWeight U)
    S 0 1 + S 0 2 + S 0 3 = 3 / 2 + y 0 ^ 2 / 2 ∧
    S 0 3 + S 1 3 + S 2 3 = 3 / 2 + y 3 ^ 2 / 2 := by
  have h₀ := combinedMarginal U 0
  have h₃ := combinedMarginal U 3
  simp only [Fin.sum_univ_four, sym, frameWeight_diagonal] at h₀ h₃
  simp only [sym]
  constructor
  · linarith only [h₀]
  · linarith only [h₃]

private theorem adjacentCutWeight_ge_local (U : unitary Mat) :
    let t := fun i => oddProbability (frameVector U i)
    1 - 2 * t 0 * (1 - t 0) ≤ lowerAdjacentCutWeight U ∧
    1 - 2 * t 3 * (1 - t 3) ≤ upperAdjacentCutWeight U := by
  obtain ⟨h₀, h₃⟩ := singletonCutWeight_eq U
  simp only [lowerAdjacentCutWeight, upperAdjacentCutWeight]
  constructor
  · linarith only [h₀, sym_frameWeight_le_one U 0 1]
  · linarith only [h₃, sym_frameWeight_le_one U 2 3]

private theorem unsignedCutBound_le_signed (t u v : ℝ) (hu : |u| ≤ 1 - v) :
    (1 + v ^ 2) / 2 - (2 * max t (1 - t) - 1) * (1 - v) ≤
      (1 + v ^ 2) / 2 + (2 * t - 1) * u + u ^ 2 / 2 := by
  have hmax : |2 * t - 1| = 2 * max t (1 - t) - 1 := by
    rcases le_total t (1 - t) with ht | ht
    · rw [max_eq_right ht, abs_of_nonpos (by linarith only [ht])]
      ring
    · rw [max_eq_left ht, abs_of_nonneg (by linarith only [ht])]
  have hmul := mul_le_mul_of_nonneg_left hu (abs_nonneg (2 * t - 1))
  have hprod := neg_abs_le ((2 * t - 1) * u)
  rw [hmax] at hmul
  rw [abs_mul, hmax] at hprod
  linarith only [hmul, hprod, sq_nonneg u]

/-- Each overlap obeys both the local pair-cap bound and the bound from the
middle cut imbalance. At absolute imbalance one the latter gives one. -/
theorem adjacentCutWeight_ge_max (U : unitary Mat) :
    let t := fun i => oddProbability (frameVector U i)
    let q := fun i => max (t i) (1 - t i)
    let v := |cutImbalance U|
    max (1 - 2 * t 0 * (1 - t 0)) ((1 + v ^ 2) / 2 - (2 * q 0 - 1) * (1 - v)) ≤
      lowerAdjacentCutWeight U ∧
    max (1 - 2 * t 3 * (1 - t 3)) ((1 + v ^ 2) / 2 - (2 * q 3 - 1) * (1 - v)) ≤
      upperAdjacentCutWeight U := by
  let t : Fin 4 → ℝ := fun i => oddProbability (frameVector U i)
  let u := -cutEvenOffset U
  let v := |cutImbalance U|
  have hu : |u| ≤ 1 - v := by
    have h := abs_cutEvenOffset_add_abs_cutImbalance_le_one U
    simp only [u, abs_neg, v]
    linarith only [h]
  obtain ⟨hLowerLocal, hUpperLocal⟩ := adjacentCutWeight_ge_local U
  obtain ⟨_, hLower, hUpper⟩ := adjacentCutWeight_ge_signed U
  have hLowerCoupled := unsignedCutBound_le_signed (t 0) u v hu
  have hUpperCoupled := unsignedCutBound_le_signed (t 3) (-u) v (by rwa [abs_neg])
  change (1 + v ^ 2) / 2 + (2 * t 0 - 1) * u + u ^ 2 / 2 ≤ _ at hLower
  change (1 + v ^ 2) / 2 - (2 * t 3 - 1) * u + u ^ 2 / 2 ≤ _ at hUpper
  exact ⟨max_le hLowerLocal (hLowerCoupled.trans hLower),
    max_le hUpperLocal (by linarith only [hUpperCoupled, hUpper])⟩

/-- Averaging the local pair-cap estimate with the signed middle-cut estimate
gives squares with opposite offset signs at the two ends. -/
theorem adjacentCutWeight_ge_quadratic (U : unitary Mat) :
    let y := fun i => 1 - 2 * oddProbability (frameVector U i)
    let u := -cutEvenOffset U
    let v := |cutImbalance U|
    1 / 2 + v ^ 2 / 4 + (y 0 - u) ^ 2 / 4 ≤ lowerAdjacentCutWeight U ∧
    1 / 2 + v ^ 2 / 4 + (y 3 + u) ^ 2 / 4 ≤ upperAdjacentCutWeight U := by
  obtain ⟨hLowerLocal, hUpperLocal⟩ := adjacentCutWeight_ge_local U
  obtain ⟨_, hLowerSigned, hUpperSigned⟩ := adjacentCutWeight_ge_signed U
  dsimp only
  constructor
  · linarith only [hLowerLocal, hLowerSigned]
  · linarith only [hUpperLocal, hUpperSigned]

/-- The signed end charges of the upper spectral projections are minus the
charge of column zero and the charge of column three. Each is bounded by
its own even mass and by the middle imbalance plus its partner's even mass. -/
theorem endCutCharge_abs_le (U : unitary Mat) :
    let t := fun i => oddProbability (frameVector U i)
    let y := fun i => 1 - 2 * t i
    let u := -cutEvenOffset U
    let v := |cutImbalance U|
    let charge := fun i =>
      emptyProbability (frameVector U i) - fullProbability (frameVector U i)
    |-charge 0| ≤ min ((1 + y 0) / 2) (v + (1 - y 0) / 2 - u) ∧
    |charge 3| ≤ min ((1 + y 3) / 2) (v + (1 - y 3) / 2 + u) := by
  let t : Fin 4 → ℝ := fun i => oddProbability (frameVector U i)
  let charge : Fin 4 → ℝ := fun i =>
    emptyProbability (frameVector U i) - fullProbability (frameVector U i)
  have hcharge (i : Fin 4) : |charge i| ≤ 1 - t i := by
    rw [show t i = 1 - evenProbability (frameVector U i) from odd_eq_one_sub_even U i]
    rw [abs_le]
    unfold charge evenProbability emptyProbability fullProbability
    constructor <;> linarith only [Complex.normSq_nonneg (frameVector U i 0),
      Complex.normSq_nonneg (frameVector U i 3)]
  have hleft : -charge 0 = -cutImbalance U + charge 1 := by
    dsimp only [charge, cutImbalance, cutEmpty, cutFull]
    ring
  have hright : charge 3 = -cutImbalance U - charge 2 := by
    have hEmpty := row_mass U 0
    have hFull := row_mass U 3
    simp only [Fin.sum_univ_four] at hEmpty hFull
    simp only [charge, cutImbalance, cutEmpty, cutFull, emptyProbability, fullProbability,
      frameVector]
    linarith only [hEmpty, hFull]
  have hLower := abs_add_le (-cutImbalance U) (charge 1)
  have hUpper : |-cutImbalance U - charge 2| ≤ |cutImbalance U| + |charge 2| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (-cutImbalance U) (-charge 2)
  rw [← hleft, abs_neg (cutImbalance U)] at hLower
  rw [← hright] at hUpper
  obtain ⟨hOddLower, hOddUpper⟩ := oddPairMass_eq U
  refine ⟨le_min ?_ ?_, le_min ?_ ?_⟩
  · rw [abs_neg]
    linarith only [hcharge 0]
  · linarith only [hLower, hcharge 1, hOddLower]
  · linarith only [hcharge 3]
  · linarith only [hUpper, hcharge 2, hOddUpper]

/-- Quadratic lower bound on the retained cut cost in the signed expansion.
The coefficients of the three cuts are `A`, their signed-charge coefficients
are `B`, and `Z₀`, `Z₂` weight the two adjacent overlaps. The charge terms
use the upper-side convention, with full occupation contributing negatively. -/
theorem retainedCutCost_ge_quadratic (U : unitary Mat) (A B : Fin 3 → ℝ) (Z₀ Z₂ : ℝ)
    (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i) (hZ₀ : 0 ≤ Z₀) (hZ₂ : 0 ≤ Z₂) :
    let y := fun i => 1 - 2 * oddProbability (frameVector U i)
    let u := -cutEvenOffset U
    let v := |cutImbalance U|
    let L := Z₀ / 2
    let R := Z₂ / 2
    let S := (L + R) / 2
    let W := sym (frameWeight U)
    let charge := fun i =>
      emptyProbability (frameVector U i) - fullProbability (frameVector U i)
    A 1 + (Z₀ + Z₂) / 2 + (3 * A 0 + 3 * A 2 - B 0 - B 2) / 2 +
        (A 1 + S) * v ^ 2 - B 1 * v + (3 * A 1 + S) * u ^ 2 -
        (L * y 0 - R * y 3) * u +
        (A 0 + L) * y 0 ^ 2 / 2 + (A 2 + R) * y 3 ^ 2 / 2 -
        (B 0 * y 0 + B 2 * y 3) / 2 ≤
      A 0 * (W 0 1 + W 0 2 + W 0 3) +
        A 1 * (forwardCutWeight U + reverseCutWeight U) +
        A 2 * (W 0 3 + W 1 3 + W 2 3) +
        B 0 * (-charge 0) + B 1 * (-cutImbalance U) + B 2 * charge 3 +
        Z₀ * lowerAdjacentCutWeight U + Z₂ * upperAdjacentCutWeight U := by
  obtain ⟨hD₀, hD₂⟩ := singletonCutWeight_eq U
  obtain ⟨hD₁, _, _⟩ := adjacentCutWeight_ge_signed U
  obtain ⟨hLower, hUpper⟩ := adjacentCutWeight_ge_quadratic U
  obtain ⟨hCharge₀, hCharge₂⟩ := endCutCharge_abs_le U
  have hCost₀ := mul_le_mul_of_nonneg_left hD₀.ge (hA 0)
  have hCost₁ := mul_le_mul_of_nonneg_left hD₁ (hA 1)
  have hCost₂ := mul_le_mul_of_nonneg_left hD₂.ge (hA 2)
  have hAdj₀ := mul_le_mul_of_nonneg_left hLower hZ₀
  have hAdj₂ := mul_le_mul_of_nonneg_left hUpper hZ₂
  have hPenalty₀ := mul_le_mul_of_nonneg_left (abs_le.mp (hCharge₀.trans
    (min_le_left _ _))).1 (hB 0)
  have hPenalty₁ := mul_le_mul_of_nonneg_left (le_abs_self (cutImbalance U)) (hB 1)
  have hPenalty₂ := mul_le_mul_of_nonneg_left (abs_le.mp (hCharge₂.trans
    (min_le_left _ _))).1 (hB 2)
  dsimp only
  linarith only [hCost₀, hCost₁, hCost₂, hAdj₀, hAdj₂, hPenalty₀, hPenalty₁, hPenalty₂]

#print axioms adjacentCutWeight_eq
#print axioms abs_cutEvenOffset_add_abs_cutImbalance_le_one
#print axioms middleCutWeight_ge_sqrt_surplus
#print axioms adjacentCutWeight_ge_sqrt_surplus
#print axioms adjacentCutWeight_ge_signed
#print axioms adjacentCutWeight_ge_max
#print axioms adjacentCutWeight_ge_quadratic
#print axioms endCutCharge_abs_le
#print axioms retainedCutCost_ge_quadratic

end D5.S3.Quantum.Semigroups.WuCubicCoupledCuts
