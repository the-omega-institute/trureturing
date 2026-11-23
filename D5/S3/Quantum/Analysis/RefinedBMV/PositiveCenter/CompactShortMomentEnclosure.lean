/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortMomentEnclosure
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One-dimensional moment formulas for the compact short-gap certificate. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortMidpoint
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactPositiveMomentTails
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactTaylorMoments
import Mathlib.Tactic.FinCases

/-! The conditional even weights used by the fourth-order midpoint certificate. -/

namespace RefinedBMV.PositiveCenter

open scoped BigOperators

/-- The first four conditional even moments as polynomials in the grid spacing and width. -/
noncomputable def shortConditionalEvenWeight (j : Fin 4) (h t : ℝ) : ℝ :=
  match j.val with
  | 0 => 1
  | 1 => (t^2 - h^2) / 3
  | 2 => (t^2 - h^2) * (3*t^2 - 7*h^2) / 15
  | _ => (t^2 - h^2) * (3*t^4 - 18*h^2*t^2 + 31*h^4) / 21

private theorem shortGridEvenSum_scaled (n : ℕ) (j : Fin 4) (h : ℝ) :
    h ^ (2 * (j : ℕ)) * shortGridEvenSum n j = (n : ℝ) * shortConditionalEvenWeight j h (h*n) := by
  fin_cases j
  · simp [shortGridEvenSum, shortConditionalEvenWeight]
  · norm_num [shortGridEvenSum_two, shortConditionalEvenWeight] <;> ring
  · norm_num [shortGridEvenSum_four, shortConditionalEvenWeight] <;> ring
  · norm_num [shortGridEvenSum_six, shortConditionalEvenWeight] <;> ring

/-- The midpoint moments reduce to a single marginal sum with a fixed polynomial weight. -/
theorem shortMidpointMoment_eq_marginal {p : ℕ} (hp : 0 < p) (j : Fin 4) (k : ℕ) (w : ℝ) :
    let h := 3 / (p : ℝ)
    shortMidpointMoment p j k w =
      (∑ i ∈ Finset.range (p+1),
        let z := h*i-1
        (↑(p+1-i) : ℝ) * Real.exp (-z*w) * (-z)^k *
          shortConditionalEvenWeight j h (2+h-z)) / ((DimThree.gaps p).length : ℝ) := by
  intro h
  rw [shortMidpointMoment_conditioned hp]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hip : i ≤ p := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hscale : h * p = 3 := by
    dsimp only [h]
    exact div_mul_cancel₀ _ (by exact_mod_cast hp.ne')
  have hwidth : h * (↑(p+1-i) : ℝ) = 2+h-(h*i-1) := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    linear_combination hscale
  rw [shortGridEvenSum_scaled, hwidth]
  ring

private def shortEvenTerm (j l : ℕ) : ℕ × ℚ :=
  match j, l with
  | 0, 0 => (0, 1)
  | 1, 0 => (2, -1 / 3)
  | 1, 1 => (0, 1 / 3)
  | 2, 0 => (4, 7 / 15)
  | 2, 1 => (2, -2 / 3)
  | 2, 2 => (0, 1 / 5)
  | 3, 0 => (6, -31 / 21)
  | 3, 1 => (4, 7 / 3)
  | 3, 2 => (2, -1)
  | 3, 3 => (0, 1 / 7)
  | _, _ => (0, 0)

private noncomputable def shortEvenCoefficient (j l : ℕ) (h : ℝ) : ℝ :=
  let (power, coefficient) := shortEvenTerm j l
  (coefficient : ℝ) * h ^ power

private theorem shortConditionalEvenWeight_eq_sum (j : Fin 4) (h t : ℝ) :
    shortConditionalEvenWeight j h t =
      ∑ l : Fin 4, shortEvenCoefficient j l h * t ^ (2 * (l : ℕ)) := by
  fin_cases j <;>
    norm_num [shortConditionalEvenWeight, shortEvenCoefficient, shortEvenTerm, Fin.sum_univ_succ] <;> ring

open private gridPoint gridAverage gridAverage_sum gridAverage_const_mul
  gridAverage_weighted_pow_eq gridAverage_sub gridPoint_bounds spacing_le
  abs_gridAverage_le_square expTaylor expTaylor_geometric_error from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactPositiveMomentTails

private noncomputable def shortMomentCoefficient (h : ℝ) (j : Fin 4) (k : ℕ) : ℝ :=
  ∑ l : Fin 4, (shortEvenCoefficient j l h * (-1)^k) *
    compactPositiveMomentCoefficient h (2 * (l : ℕ)) k

private theorem shortMomentCoefficient_eq {p : ℕ} (hp : 0 < p) (j : Fin 4) (k : ℕ) :
    let h := 3 / (p : ℝ)
    gridAverage p (fun z ↦ shortConditionalEvenWeight j h (2+h-z) * (-z)^k) =
      shortMomentCoefficient h j k := by
  intro h
  have hweight (z : ℝ) :
      shortConditionalEvenWeight j h (2+h-z) * (-z)^k =
        ∑ l : Fin 4, (shortEvenCoefficient j l h * (-1)^k) *
          ((2+h-z) ^ (2 * (l : ℕ)) * z^k) := by
    rw [shortConditionalEvenWeight_eq_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    rw [show -z = (-1)*z by ring, mul_pow]
    ring
  simp_rw [hweight, gridAverage_sum, gridAverage_const_mul]
  unfold shortMomentCoefficient
  exact Finset.sum_congr rfl fun l _ ↦
    congrArg (_ * ·) (gridAverage_weighted_pow_eq hp (2 * (l : ℕ)) k)

private theorem shortMidpointMoment_eq_gridAverage {p : ℕ} (hp : 0 < p)
    (j : Fin 4) (k : ℕ) (w : ℝ) :
    shortMidpointMoment p j k w = gridAverage p (fun z ↦
      shortConditionalEvenWeight j (3 / (p : ℝ)) (2+3/(p : ℝ)-z) * (-z)^k * Real.exp (-z*w)) := by
  rw [shortMidpointMoment_eq_marginal hp]
  unfold gridAverage gridPoint
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- Taylor polynomial in the midpoint coordinate for the tilted separation moment. -/
noncomputable def shortMomentTaylor (h : ℝ) (j : Fin 4) (k n : ℕ) (w : ℝ) : ℝ :=
  ∑ m ∈ Finset.range n, shortMomentCoefficient h j (k+m) * w^m / (m.factorial : ℝ)

open SmallCorner (momentHorner)
open private coeffScale coeffMul coeffSum horner_scale horner_mul horner_sum horner_monomial from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MomentPolynomial

/-- Exact spacing coefficients for the corresponding midpoint Taylor coefficient. -/
def shortMomentTaylorCoefficients (j : Fin 4) (k n : ℕ) : List ℚ :=
  coeffSum (fun l ↦
    let (power, coefficient) := shortEvenTerm j l
    let weight := coefficient * (-1 : ℚ) ^ (k+n) * ((k+n).factorial : ℚ) / (n.factorial : ℚ)
    coeffScale weight (coeffMul (List.replicate power 0 ++ [1])
      (compactTiltedMomentCoefficients (2*l) (k+n)))) 4

private theorem shortMomentTaylorCoefficients_eval (h : ℝ) (j : Fin 4) (k n : ℕ) :
    momentHorner h (shortMomentTaylorCoefficients j k n) =
      shortMomentCoefficient h j (k+n) / (n.factorial : ℝ) := by
  rw [shortMomentTaylorCoefficients, horner_sum, shortMomentCoefficient, Finset.sum_div,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  cases he : shortEvenTerm j l with
  | mk power coefficient =>
    simp only [shortEvenCoefficient, he, horner_scale, horner_mul, horner_monomial,
      compactTiltedMomentCoefficients_eval, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast,
      Rat.cast_pow, Rat.cast_neg, Rat.cast_one, one_mul]
    have hfac : ((k+n).factorial : ℝ) ≠ 0 := by positivity
    field_simp [hfac]

private theorem shortMomentTaylor_eq {p : ℕ} (hp : 0 < p) (j : Fin 4) (k n : ℕ) (w : ℝ) :
    let h := 3 / (p : ℝ)
    shortMomentTaylor h j k n w = gridAverage p (fun z ↦
      shortConditionalEvenWeight j h (2+h-z) * (-z)^k *
        (∑ m ∈ Finset.range n, (-z*w)^m / (m.factorial : ℝ))) := by
  intro h
  have expand (z : ℝ) :
      shortConditionalEvenWeight j h (2+h-z) * (-z)^k *
        (∑ m ∈ Finset.range n, (-z*w)^m / (m.factorial : ℝ)) =
      ∑ m ∈ Finset.range n, (w^m / (m.factorial : ℝ)) *
        (shortConditionalEvenWeight j h (2+h-z) * (-z)^(k+m)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ ↦ by
      rw [pow_add, mul_pow]
      ring
  simp_rw [expand, gridAverage_sum, gridAverage_const_mul]
  unfold shortMomentTaylor
  exact Finset.sum_congr rfl fun m _ ↦ by
    rw [shortMomentCoefficient_eq hp]
    ring

private theorem shortConditionalEvenWeight_abs_le {p i : ℕ} (hp : 0 < p) (hi : i ≤ p)
    (j : Fin 4) :
    let h := 3 / (p : ℝ)
    |shortConditionalEvenWeight j h (2+h-gridPoint p i)| ≤ (3 : ℝ)^(2*(j : ℕ)) := by
  intro h
  let n := p + 1 - i
  have hn : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by dsimp [n]; omega)
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have htotal : h * p = 3 := by
    dsimp only [h]
    exact div_mul_cancel₀ _ (by exact_mod_cast hp.ne')
  have hwidth : h * n = 2+h-gridPoint p i := by
    dsimp only [n, gridPoint]
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    change h * ((p : ℝ) + 1 - i) = 2+h-(h*i-1)
    linear_combination htotal
  have hsum :
      (∑ m ∈ Finset.range n, (h * ((n : ℝ)-1-2*m))^(2*(j : ℕ))) =
        (n : ℝ) * shortConditionalEvenWeight j h (2+h-gridPoint p i) := by
    rw [← hwidth, ← shortGridEvenSum_scaled, shortGridEvenSum, Finset.mul_sum]
    simp_rw [mul_pow]
  rw [abs_le]
  constructor
  · apply (mul_le_mul_iff_of_pos_left hn).mp
    rw [← hsum]
    apply le_trans (mul_nonpos_of_nonneg_of_nonpos hn.le (neg_nonpos.mpr (by positivity)))
    exact Finset.sum_nonneg fun m _ ↦ by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _
  · apply (mul_le_mul_iff_of_pos_left hn).mp
    rw [← hsum]
    calc
      _ ≤ ∑ _m ∈ Finset.range n, (3 : ℝ)^(2*(j : ℕ)) := by
        apply Finset.sum_le_sum
        intro m hm
        have hmN : m < n := Finset.mem_range.mp hm
        have hmR : (m : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hmN
        have hnR : (n : ℝ) ≤ (p : ℝ) + 1 := by
          exact_mod_cast (show n ≤ p+1 by dsimp [n]; omega)
        have habs : |(n : ℝ)-1-2*m| ≤ (p : ℝ) := abs_le.mpr
          ⟨by linarith, by linarith [Nat.cast_nonneg (α := ℝ) m]⟩
        have habsh : |h*((n : ℝ)-1-2*m)| ≤ 3 := by
          rw [abs_mul, abs_of_nonneg hh, ← htotal]
          exact mul_le_mul_of_nonneg_left habs hh
        simpa only [pow_abs_two_mul] using pow_le_pow_left₀ (abs_nonneg _) habsh (2*(j : ℕ))
      _ = _ := by simp [nsmul_eq_mul, mul_comm]

/-- Evaluate the midpoint Taylor polynomial with the collected rational spacing coefficients. -/
theorem shortMomentTaylor_eq_horner_sum (h : ℝ) (j : Fin 4) (k n : ℕ) (w : ℝ) :
    shortMomentTaylor h j k n w =
      ∑ m ∈ Finset.range n, momentHorner h (shortMomentTaylorCoefficients j k m) * w^m := by
  unfold shortMomentTaylor
  exact Finset.sum_congr rfl fun m _ ↦ by rw [shortMomentTaylorCoefficients_eval]; ring

private def shortMomentCenterCoefficients (j : Fin 4) (k terms : ℕ) (center : ℚ) : List ℚ :=
  coeffSum (fun n ↦ coeffScale (center ^ n) (shortMomentTaylorCoefficients j k n)) terms

private theorem shortMomentCenterCoefficients_eval (h : ℝ) (j : Fin 4) (k terms : ℕ)
    (center : ℚ) :
    momentHorner h (shortMomentCenterCoefficients j k terms center) =
      shortMomentTaylor h j k terms center := by
  rw [shortMomentCenterCoefficients, horner_sum, shortMomentTaylor_eq_horner_sum]
  simp only [horner_scale, Rat.cast_pow, mul_comm]

private noncomputable def shiftedShortMomentTaylor (p : ℕ) (j : Fin 4)
    (k terms : ℕ) (center offset : ℝ) : ℝ :=
  ∑ m ∈ Finset.range terms,
    shortMidpointMoment p j (k + m) center * offset ^ m / (m.factorial : ℝ)

private theorem shiftedShortMomentTaylor_eq {p : ℕ} (hp : 0 < p) (j : Fin 4)
    (k terms : ℕ) (center offset : ℝ) :
    let h := 3 / (p : ℝ)
    shiftedShortMomentTaylor p j k terms center offset = gridAverage p (fun z ↦
      shortConditionalEvenWeight j h (2 + h - z) * (-z) ^ k *
        Real.exp (-z * center) * expTaylor terms (-z * offset)) := by
  intro h
  have hpoint (z : ℝ) :
      shortConditionalEvenWeight j h (2 + h - z) * (-z) ^ k *
        Real.exp (-z * center) * expTaylor terms (-z * offset) =
        ∑ m ∈ Finset.range terms, (offset ^ m / (m.factorial : ℝ)) *
          (shortConditionalEvenWeight j h (2 + h - z) * (-z) ^ (k + m) *
            Real.exp (-z * center)) := by
    rw [expTaylor, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ ↦ by rw [pow_add, mul_pow]; ring
  simp_rw [hpoint, gridAverage_sum, gridAverage_const_mul]
  unfold shiftedShortMomentTaylor
  exact Finset.sum_congr rfl fun m _ ↦ by
    rw [shortMidpointMoment_eq_gridAverage hp]
    ring

private theorem shortMidpointMoment_sub_shiftedTaylor_le {p : ℕ} (hp : 11 ≤ p)
    (j : Fin 4) (k terms : ℕ) (hn : 2 ≤ terms) {center offset R B : ℝ}
    (hr : |offset| ≤ R) (hsmall : 2 * R / (terms.succ : ℝ) < 1)
    (hB : Real.exp (2 * |center|) ≤ B) :
    |shortMidpointMoment p j k (center + offset) -
        shiftedShortMomentTaylor p j k terms center offset| ≤
      (3 : ℝ) ^ (2 * (j : ℕ)) * 2 ^ k * B * (7 / 44) * (2 * R) ^ terms /
        (terms.factorial : ℝ) / (1 - 2 * R / (terms.succ : ℝ)) := by
  have hp₀ : 0 < p := by omega
  have hR₀ : 0 ≤ R := (abs_nonneg offset).trans hr
  have hden : 0 < 1 - 2 * R / (terms.succ : ℝ) := sub_pos.mpr hsmall
  have hB₀ := (Real.exp_pos _).le.trans hB
  let h := 3 / (p : ℝ)
  let W (z : ℝ) := shortConditionalEvenWeight j h (2 + h - z) * (-z) ^ k * Real.exp (-z * center)
  let C := (3 : ℝ) ^ (2 * (j : ℕ)) * 2 ^ k * B
  let E := (2 * R) ^ terms / (4 * (terms.factorial : ℝ)) / (1 - 2 * R / (terms.succ : ℝ))
  rw [shortMidpointMoment_eq_gridAverage hp₀, shiftedShortMomentTaylor_eq hp₀, ← gridAverage_sub]
  have hexp (z : ℝ) : Real.exp (-z * (center + offset)) =
      Real.exp (-z * center) * Real.exp (-z * offset) := by rw [mul_add, Real.exp_add]
  simp_rw [hexp, ← mul_assoc]
  change |gridAverage p (fun z ↦ W z * Real.exp (-z * offset) -
    W z * expTaylor terms (-z * offset))| ≤ _
  have htail := abs_gridAverage_le_square hp₀
    (fun z ↦ W z * Real.exp (-z * offset) - W z * expTaylor terms (-z * offset)) (C * E) (by
      intro i hi
      obtain ⟨hz₁, hz₂⟩ := gridPoint_bounds hp₀ hi
      have hz : |gridPoint p i| ≤ 2 := abs_le.mpr ⟨by linarith, hz₂⟩
      have hexpLe : Real.exp (-gridPoint p i * center) ≤ B := by
        refine (Real.exp_le_exp.mpr ?_).trans hB
        calc
          _ ≤ |-gridPoint p i * center| := le_abs_self _
          _ ≤ _ := by rw [abs_mul, abs_neg]; exact mul_le_mul_of_nonneg_right hz (abs_nonneg _)
      have hW : |W (gridPoint p i)| ≤ C := by
        unfold W C
        simp only [abs_mul, abs_pow, abs_neg, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul
          (mul_le_mul
            (shortConditionalEvenWeight_abs_le hp₀ (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) j)
            (pow_le_pow_left₀ (abs_nonneg _) hz _) (by positivity) (by positivity))
          hexpLe (Real.exp_pos _).le (by positivity)
      rw [← mul_sub, abs_mul]
      have herr := expTaylor_geometric_error (x := -gridPoint p i) (by simpa using hz) hr hn hsmall
      rw [neg_sq] at herr
      exact (mul_le_mul hW herr (abs_nonneg _) (by positivity)).trans_eq (by unfold E; ring))
  have hvar : (1 + 3 / (p : ℝ)) / 2 ≤ 7 / 11 := by linarith [spacing_le hp]
  exact (htail.trans (mul_le_mul_of_nonneg_left hvar (by dsimp [C, E]; positivity))).trans_eq
    (by unfold C E; ring)

private theorem shortMidpointMoment_sub_taylor_le {p : ℕ} (hp : 11 ≤ p)
    (j : Fin 4) (k n : ℕ) (hn : 2 ≤ n) {w R : ℝ} (hw : |w| ≤ R)
    (hR : 2 * R / (n.succ : ℝ) < 1) :
    |shortMidpointMoment p j k w - shortMomentTaylor (3 / (p : ℝ)) j k n w| ≤
      (3 : ℝ) ^ (2 * (j : ℕ)) * 2 ^ k * (7 / 44) * (2 * R) ^ n / (n.factorial : ℝ) /
        (1 - 2 * R / (n.succ : ℝ)) := by
  have hp₀ : 0 < p := by omega
  have hz : shiftedShortMomentTaylor p j k n 0 w = shortMomentTaylor (3 / (p : ℝ)) j k n w := by
    rw [shiftedShortMomentTaylor_eq hp₀, shortMomentTaylor_eq hp₀]
    simp [expTaylor]
  simpa only [zero_add, hz, mul_one] using
    (shortMidpointMoment_sub_shiftedTaylor_le hp j k n hn (center := 0) (B := 1)
      hw hR (by simp))

namespace CompactTaylorModel

/-- Recenter the short-gap moment before enclosing it. The center coefficients are evaluated
with a univariate polynomial in the spacing, and the box expansion uses small offsets. -/
def shiftedShortMidpointMomentModel (j : Fin 4) (k centerTerms offsetTerms : ℕ)
    (center r bound : ℚ) (Offset H : Model) : Model :=
  let mass := fun k ↦ (3 : ℚ) ^ (2 * (j : ℕ)) * 2 ^ k * (7 / 44)
  let tail := fun n (r : ℚ) ↦ (2 * r) ^ n / (n.factorial : ℚ) / (1 - 2 * r / (n.succ : ℚ))
  let approximation := Model.series offsetTerms (fun m ↦
    let c := Model.horner (shortMomentCenterCoefficients j (k + m) centerTerms center) H
    let enclosed := c.widen (mass (k + m) * tail centerTerms |center|)
    enclosed.mul (Model.ofRat (1 / (m.factorial : ℚ)))) Offset
  approximation.widen (mass k * bound * tail offsetTerms r)

theorem shiftedShortMidpointMomentModel_sound {p k centerTerms offsetTerms : ℕ} (hp : 11 ≤ p)
    (hcTerms : 2 ≤ centerTerms) (hoTerms : 2 ≤ offsetTerms) (j : Fin 4)
    {s t z offset : ℝ} {Offset H : Model} {center r bound : ℚ}
    (hb : InBox s t z) (hh : H.Encloses s t z (3 / (p : ℝ))) (hoff : Offset.Encloses s t z offset)
    (hr : |offset| ≤ (r : ℝ)) (hcenter : 2 * |(center : ℝ)| / (centerTerms.succ : ℝ) < 1)
    (hsmall : 2 * (r : ℝ) / (offsetTerms.succ : ℝ) < 1)
    (hbound : Real.exp (2 * |(center : ℝ)|) ≤ (bound : ℝ)) :
    (shiftedShortMidpointMomentModel j k centerTerms offsetTerms center r bound Offset H).Encloses
      s t z (shortMidpointMoment p j k (center + offset)) := by
  apply Model.widen_sound (g := shiftedShortMomentTaylor p j k offsetTerms center offset)
  · unfold shiftedShortMomentTaylor
    have he : ∀ m : ℕ, shortMidpointMoment p j (k + m) center * offset ^ m / (m.factorial : ℝ) =
        (shortMidpointMoment p j (k + m) center * (1 / (m.factorial : ℝ))) * offset ^ m :=
      fun _ ↦ by ring
    simp_rw [he]
    apply Model.series_sound hb hoff
    intro m _
    have hfact : (Model.ofRat (1 / (m.factorial : ℚ))).Encloses s t z
        (1 / (m.factorial : ℝ)) := by
      simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using
        Model.ofRat_sound (1 / (m.factorial : ℚ)) s t z
    apply Model.mul_sound hb _ hfact
    apply Model.widen_sound (g := shortMomentTaylor (3 / (p : ℝ)) j (k + m) centerTerms center)
    · rw [← shortMomentCenterCoefficients_eval]
      exact Model.horner_sound hb hh _
    · push_cast
      have htail := shortMidpointMoment_sub_taylor_le hp j (k + m) centerTerms hcTerms
        (w := (center : ℝ)) le_rfl hcenter
      exact htail.trans_eq (by
        rw [Nat.cast_succ, add_comm (centerTerms : ℝ) 1]
        ring)
  · push_cast
    have htail := shortMidpointMoment_sub_shiftedTaylor_le hp j k offsetTerms hoTerms hr hsmall hbound
    exact htail.trans_eq (by
      rw [Nat.cast_succ, add_comm (offsetTerms : ℝ) 1]
      ring)

end CompactTaylorModel

end RefinedBMV.PositiveCenter
