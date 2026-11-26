/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactPositiveMomentTails
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact coefficients and Taylor remainder for the compact positive moments. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactPositiveMoments
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MomentPolynomial
import Batteries.Tactic.OpenPrivate

/-! Taylor approximation of the weighted moments in the compact mixed-sign comparison. -/

open scoped BigOperators

namespace RefinedBMV.PositiveCenter

open DimThree (gaps gaps_cycle_all word_counts_all)
open SmallCorner (momentHorner normalizedMomentCoeffs normalized_moment_eval_marginal)

noncomputable section

private def gridPoint (p i : ℕ) : ℝ := 3 / (p : ℝ) * i - 1

private def gridAverage (p : ℕ) (f : ℝ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range (p + 1), ((p + 1 - i : ℕ) : ℝ) * f (gridPoint p i)) /
    ((gaps p).length : ℝ)

private theorem gaps_length_pos (p : ℕ) : (0 : ℝ) < (gaps p).length := by
  exact_mod_cast (word_counts_all p).2.1

private theorem gridAverage_eq_marginal (p : ℕ) (f : ℝ → ℝ) :
    gridAverage p f =
      ((gaps p).map fun g ↦ f (3 * (g.2.2 : ℝ) / (p : ℝ) - 1)).sum /
        ((gaps p).length : ℝ) := by
  let F (g : ℕ × ℕ × ℕ) := f (3 * (g.2.2 : ℝ) / (p : ℝ) - 1)
  change _ = ((gaps p).map F).sum / ((gaps p).length : ℝ)
  rw [← ((gaps_cycle_all p).map F).sum_eq]
  unfold gridAverage
  congr 1
  simp only [List.map_map, gaps, List.flatMap_def, List.map_flatten, List.sum_flatten,
    Function.comp_def, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  apply Finset.sum_congr rfl
  intro i _
  have hpoint : 3 * (i : ℝ) / (p : ℝ) - 1 = gridPoint p i := by
    unfold gridPoint
    ring
  simp [F, hpoint, nsmul_eq_mul]

private theorem gridAverage_sum {ι : Type*} (p : ℕ) (s : Finset ι) (f : ι → ℝ → ℝ) :
    gridAverage p (fun x ↦ ∑ i ∈ s, f i x) = ∑ i ∈ s, gridAverage p (f i) := by
  simp only [gridAverage, Finset.mul_sum, Finset.sum_div]
  exact Finset.sum_comm

private theorem gridAverage_const_mul (p : ℕ) (a : ℝ) (f : ℝ → ℝ) :
    gridAverage p (fun x ↦ a * f x) = a * gridAverage p f := by
  simp only [gridAverage, ← mul_div_assoc, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by ring

private theorem gridAverage_sub (p : ℕ) (f g : ℝ → ℝ) :
    gridAverage p (fun x ↦ f x - g x) = gridAverage p f - gridAverage p g := by
  simp only [gridAverage, mul_sub, Finset.sum_sub_distrib, sub_div]

private theorem centered_variance_eq {p : ℕ} (hp : 0 < p) :
    compositionMarginalVariance p = (1 + 3 / (p : ℝ)) / 2 := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [compositionMarginalVariance, (centered_marginal_sums hp).2]
  field_simp [(gaps_length_pos p).ne', hpR]

/-- The exact centered moments, as polynomials in the grid spacing. The stored
normalized coefficients for orders at least two include the Taylor factorial. -/
def compactCenteredMomentPolynomial (h : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 0
  | n + 2 =>
      ((1 + h) / 4) * ((n + 2).factorial : ℝ) * momentHorner h (normalizedMomentCoeffs 0 (n + 2))

private theorem gridAverage_pow_eq {p : ℕ} (hp : 0 < p) (n : ℕ) :
    gridAverage p (fun x ↦ x ^ n) = compactCenteredMomentPolynomial (3 / (p : ℝ)) n := by
  rw [gridAverage_eq_marginal]
  cases n with
  | zero => simp [compactCenteredMomentPolynomial, (gaps_length_pos p).ne']
  | succ n =>
    cases n with
    | zero => simpa [compactCenteredMomentPolynomial] using
        congrArg (· / ((gaps p).length : ℝ)) (centered_marginal_sums hp).1
    | succ n =>
      change ((gaps p).map fun g ↦ (3 * (g.2.2 : ℝ) / (p : ℝ) - 1) ^ (n + 2)).sum /
        ((gaps p).length : ℝ) = compactCenteredMomentPolynomial (3 / (p : ℝ)) (n + 2)
      rw [compactCenteredMomentPolynomial, normalized_moment_eval_marginal hp n,
        centered_variance_eq hp]
      have hfac : (0 : ℝ) < (n + 2).factorial := by positivity
      have hvar : (0 : ℝ) < 1 + 3 / (p : ℝ) := by positivity
      field_simp [(gaps_length_pos p).ne', hfac.ne', hvar.ne']
      norm_num

private theorem grid_second_difference_sum (p : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range (p + 1),
      ((p + 1 - i : ℕ) : ℝ) * (f i - 2 * f (i + 1) + f (i + 2))) =
      ((p : ℝ) + 1) * f 0 - ((p : ℝ) + 2) * f 1 + f (p + 2) := by
  let F (i : ℕ) := ((p : ℝ) + 1 - i) * (f i - f (i + 1)) - f (i + 1)
  calc
    _ = ∑ i ∈ Finset.range (p + 1), (F i - F (i + 1)) := by
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [Nat.cast_sub (Finset.mem_range.mp hi).le]
      simp only [F, Nat.cast_add, Nat.cast_one]
      ring
    _ = F 0 - F (p + 1) := Finset.sum_range_sub' F (p + 1)
    _ = _ := by
      simp only [F, Nat.cast_zero, Nat.cast_add, Nat.cast_one]
      ring

private theorem centered_second_difference (x h : ℝ) (m : ℕ) :
    x ^ (m + 2) - 2 * (x - h) ^ (m + 2) + (x - 2 * h) ^ (m + 2) =
      2 * h ^ 2 * ∑ j ∈ Finset.range (m + 1),
        ((m + 2).choose (j + 2) : ℝ) * (-h) ^ j * ((2 : ℝ) ^ (j + 1) - 1) *
          x ^ (m - j) := by
  have expand (a : ℝ) :
      (a + x) ^ (m + 2) = x ^ (m + 2) + a * x ^ (m + 1) * ((m + 2 : ℕ) : ℝ) +
        ∑ j ∈ Finset.range (m + 1),
          a ^ (j + 2) * x ^ (m - j) * ((m + 2).choose (j + 2) : ℝ) := by
    let f (k : ℕ) := a ^ k * x ^ (m + 2 - k) * ((m + 2).choose k : ℝ)
    rw [add_pow]
    change (∑ k ∈ Finset.range (m + 2 + 1), f k) = _
    rw [show m + 2 + 1 = 2 + (m + 1) by omega, Finset.sum_range_add f 2 (m + 1)]
    have hfirst : (∑ k ∈ Finset.range 2, f k) =
        x ^ (m + 2) + a * x ^ (m + 1) * ((m + 2 : ℕ) : ℝ) := by
      rw [Finset.sum_range_succ f 1, Finset.sum_range_one]
      simp [f, show m + 2 - 1 = m + 1 by omega]
    rw [hfirst]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [f, Nat.add_comm 2 j, show m + 2 - (j + 2) = m - j by omega]
  rw [show x - h = -h + x by ring, show x - 2 * h = 2 * (-h) + x by ring,
    expand (-h), expand (2 * (-h))]
  calc
    _ = (∑ j ∈ Finset.range (m + 1),
          (2 * (-h)) ^ (j + 2) * x ^ (m - j) * ((m + 2).choose (j + 2) : ℝ)) -
        2 * ∑ j ∈ Finset.range (m + 1),
          (-h) ^ (j + 2) * x ^ (m - j) * ((m + 2).choose (j + 2) : ℝ) := by ring
    _ = _ := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [mul_pow, pow_succ (2 : ℝ) (j + 1), pow_add (-h) j 2]
      ring

/-- The moments of the negated grid point satisfy a triangular recurrence at the grid spacing.
The cross-multiplied form allows checking integer polynomial coefficients by multiplication. -/
private theorem compact_centered_moment_recurrence {p : ℕ} (hp : 0 < p) (m : ℕ) :
    let h := 3 / (p : ℝ)
    let M (n : ℕ) := (-1 : ℝ) ^ n * compactCenteredMomentPolynomial h n
    h * (3 + h) * (3 + 2 * h) *
        (((m + 2).choose 2 : ℝ) * M m +
          ∑ j ∈ Finset.range m,
            ((m + 2).choose (j + 3) : ℝ) * (-h) ^ (j + 1) * ((2 : ℝ) ^ (j + 2) - 1) *
              M (m - (j + 1))) =
      (3 + h) - (3 + 2 * h) * (1 - h) ^ (m + 2) + h * (-2 - 2 * h) ^ (m + 2) := by
  intro h M
  let C (j : ℕ) := ((m + 2).choose (j + 2) : ℝ) * (-h) ^ j * ((2 : ℝ) ^ (j + 1) - 1)
  let F (x : ℝ) := (-x) ^ (m + 2) - 2 * (-x - h) ^ (m + 2) + (-x - 2 * h) ^ (m + 2)
  have hscale : h * (p : ℝ) = 3 :=
    div_mul_cancel₀ _ (by exact_mod_cast hp.ne')
  have hmoment (n : ℕ) : gridAverage p (fun x ↦ (-x) ^ n) = M n := by
    calc
      _ = gridAverage p (fun x ↦ (-1 : ℝ) ^ n * x ^ n) := by
        apply congrArg (gridAverage p)
        funext x
        rw [show -x = (-1) * x by ring, mul_pow]
      _ = _ := by simp only [gridAverage_const_mul, gridAverage_pow_eq hp, M, h]
  have havg : gridAverage p F =
      2 * h ^ 2 * ∑ j ∈ Finset.range (m + 1), C j * M (m - j) := by
    calc
      _ = gridAverage p (fun x ↦ 2 * h ^ 2 * ∑ j ∈ Finset.range (m + 1),
          C j * (-x) ^ (m - j)) :=
        congrArg (gridAverage p) (funext fun x ↦ centered_second_difference (-x) h m)
      _ = _ := by
        rw [gridAverage_const_mul, gridAverage_sum]
        apply congrArg (2 * h ^ 2 * ·)
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [gridAverage_const_mul, hmoment]
  have hshift (i k : ℕ) : -gridPoint p (i + k) = -gridPoint p i - h * k := by
    simp only [gridPoint, h, Nat.cast_add]
    ring
  have htel : ((gaps p).length : ℝ) * gridAverage p F =
      ((p : ℝ) + 1) - ((p : ℝ) + 2) * (1 - h) ^ (m + 2) + (-2 - 2 * h) ^ (m + 2) := by
    have hterm (i : ℕ) : F (gridPoint p i) =
        (-gridPoint p i) ^ (m + 2) - 2 * (-gridPoint p (i + 1)) ^ (m + 2) +
          (-gridPoint p (i + 2)) ^ (m + 2) := by
      simp only [F, hshift i 1, hshift i 2, Nat.cast_one, Nat.cast_ofNat, mul_one] <;> ring
    have hzero : -gridPoint p 0 = 1 := by simp [gridPoint]
    have hone : -gridPoint p 1 = 1 - h := by
      simp only [gridPoint, h, Nat.cast_one, mul_one]
      ring
    have hend : -gridPoint p (p + 2) = -2 - 2 * h := by
      simp only [gridPoint, Nat.cast_add, Nat.cast_ofNat]
      change -(h * ((p : ℝ) + 2) - 1) = _
      linear_combination -hscale
    rw [gridAverage, mul_div_cancel₀ _ (gaps_length_pos p).ne']
    simp_rw [hterm]
    rw [grid_second_difference_sum p (fun i ↦ (-gridPoint p i) ^ (m + 2)),
      hzero, hone, hend, one_pow, mul_one]
  have hcountNat : 2 * (gaps p).length = (p + 1) * (p + 2) := by
    rw [DimThree.gaps_length_eq_choose, Nat.mul_comm 2, Nat.mul_comm (p + 1) (p + 2)]
    simpa only [Nat.choose_one_right] using (Nat.add_one_mul_choose_eq (p + 1) 1).symm
  have hcount : 2 * ((gaps p).length : ℝ) = ((p : ℝ) + 1) * ((p : ℝ) + 2) := by
    exact_mod_cast hcountNat
  have hleft : ((p : ℝ) + 1) * h = 3 + h := by linear_combination hscale
  have hright : ((p : ℝ) + 2) * h = 3 + 2 * h := by linear_combination hscale
  have hnorm :
      h * (3 + h) * (3 + 2 * h) = h * (((gaps p).length : ℝ) * (2 * h ^ 2)) := by
    rw [← hleft, ← hright]
    calc
      _ = h ^ 3 * (((p : ℝ) + 1) * ((p : ℝ) + 2)) := by ring
      _ = _ := by rw [← hcount]; ring
  have hsplit : (∑ j ∈ Finset.range (m + 1), C j * M (m - j)) =
      ((m + 2).choose 2 : ℝ) * M m +
        ∑ j ∈ Finset.range m, C (j + 1) * M (m - (j + 1)) := by
    have hhead : C 0 * M (m - 0) = ((m + 2).choose 2 : ℝ) * M m := by norm_num [C]
    rw [Finset.sum_range_succ', hhead, add_comm]
  change h * (3 + h) * (3 + 2 * h) *
      (((m + 2).choose 2 : ℝ) * M m + ∑ j ∈ Finset.range m, C (j + 1) * M (m - (j + 1))) = _
  calc
    _ = h * (((gaps p).length : ℝ) * gridAverage p F) := by
      rw [← hsplit, havg, hnorm]
      ring
    _ = _ := by
      rw [htel]
      calc
        _ = ((p : ℝ) + 1) * h - ((p : ℝ) + 2) * h * (1 - h) ^ (m + 2) +
            h * (-2 - 2 * h) ^ (m + 2) := by ring
        _ = _ := by rw [hleft, hright]

/-- The unscaled Taylor coefficient of order `n`, before division by `n!`. -/
def compactPositiveMomentCoefficient (h : ℝ) (j n : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (j + 1),
    (-1 : ℝ) ^ l * (j.choose l : ℝ) * (2 + h) ^ (j - l) *
      compactCenteredMomentPolynomial h (n + l)

open private coeffScale coeffMul coeffSum horner_scale horner_mul horner_sum from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MomentPolynomial

private def compactCenteredMomentCoefficients : ℕ → List ℚ
  | 0 => [1]
  | 1 => []
  | n + 2 => coeffScale (((n + 2).factorial : ℚ) / 4)
      (coeffMul [1, 1] (normalizedMomentCoeffs 0 (n + 2)))

private theorem compactCenteredMomentCoefficients_eval (h : ℝ) (n : ℕ) :
    momentHorner h (compactCenteredMomentCoefficients n) = compactCenteredMomentPolynomial h n := by
  cases n with
  | zero => simp [compactCenteredMomentCoefficients, compactCenteredMomentPolynomial, momentHorner]
  | succ n =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [compactCenteredMomentCoefficients, compactCenteredMomentPolynomial,
        horner_scale, horner_mul, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
        momentHorner, Rat.cast_one, mul_zero, add_zero, mul_one]
      ring

private def tiltedPowerCoefficients : ℕ → List ℚ
  | 0 => [1]
  | n + 1 => coeffMul [2, 1] (tiltedPowerCoefficients n)

private theorem tiltedPowerCoefficients_eval (h : ℝ) (n : ℕ) :
    momentHorner h (tiltedPowerCoefficients n) = (2 + h) ^ n := by
  induction n with
  | zero => simp [tiltedPowerCoefficients, momentHorner]
  | succ n ih =>
    rw [tiltedPowerCoefficients, horner_mul, ih, pow_succ']
    simp [momentHorner]

/-- Collect all contributions to each spacing coefficient before interval evaluation. -/
def compactTiltedMomentCoefficients (j n : ℕ) : List ℚ :=
  coeffSum (fun l ↦ coeffScale ((-1 : ℚ) ^ l * (j.choose l : ℚ) / (n.factorial : ℚ))
    (coeffMul (tiltedPowerCoefficients (j - l)) (compactCenteredMomentCoefficients (n + l)))) (j + 1)

/-- The collected coefficients evaluate to the exact Taylor coefficient of the tilted moment. -/
theorem compactTiltedMomentCoefficients_eval (h : ℝ) (j n : ℕ) :
    momentHorner h (compactTiltedMomentCoefficients j n) =
      compactPositiveMomentCoefficient h j n / (n.factorial : ℝ) := by
  simp only [compactTiltedMomentCoefficients, compactPositiveMomentCoefficient, horner_sum,
    horner_scale, horner_mul, tiltedPowerCoefficients_eval, compactCenteredMomentCoefficients_eval,
    Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_pow, Rat.cast_neg, Rat.cast_one,
    Finset.sum_div]
  exact Finset.sum_congr rfl fun l _ ↦ by ring

/-- The Taylor polynomial for a prescribed number of terms of the positive moment. -/
def compactPositiveMomentTaylorUpTo (h : ℝ) (j order : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range order,
    compactPositiveMomentCoefficient h j n / (n.factorial : ℝ) * t ^ n

/-- Taylor polynomial through degree `24 - j` for the weighted exponential moment. -/
def compactPositiveMomentTaylor (h : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  compactPositiveMomentTaylorUpTo h j (25 - j) t

private theorem gridAverage_weighted_pow_eq {p : ℕ} (hp : 0 < p) (j n : ℕ) :
    gridAverage p (fun x ↦ (2 + 3 / (p : ℝ) - x) ^ j * x ^ n) =
      compactPositiveMomentCoefficient (3 / (p : ℝ)) j n := by
  let c : ℝ := 2 + 3 / (p : ℝ)
  have hbinom (x : ℝ) : (c - x) ^ j * x ^ n = ∑ l ∈ Finset.range (j + 1),
      ((-1 : ℝ) ^ l * (j.choose l : ℝ) * c ^ (j - l)) * x ^ (n + l) := by
    rw [sub_eq_add_neg, add_comm c, add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [show -x = (-1) * x by ring, mul_pow, pow_add]
    ring
  change gridAverage p (fun x ↦ (c - x) ^ j * x ^ n) = _
  simp_rw [hbinom, gridAverage_sum, gridAverage_const_mul, gridAverage_pow_eq hp]
  rfl

private def expTaylor (m : ℕ) (z : ℝ) : ℝ :=
  ∑ n ∈ Finset.range m, z ^ n / (n.factorial : ℝ)

private theorem gridAverage_expTaylor_eq {p : ℕ} (hp : 0 < p) (j m : ℕ) (t : ℝ) :
    gridAverage p (fun x ↦ (2 + 3 / (p : ℝ) - x) ^ j * expTaylor m (x * t)) =
      compactPositiveMomentTaylorUpTo (3 / (p : ℝ)) j m t := by
  let c : ℝ := 2 + 3 / (p : ℝ)
  have hterm (x : ℝ) :
      (c - x) ^ j * expTaylor m (x * t) =
        ∑ n ∈ Finset.range m,
          (t ^ n / (n.factorial : ℝ)) * ((c - x) ^ j * x ^ n) := by
    rw [expTaylor, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ ↦ by rw [mul_pow]; ring
  change gridAverage p (fun x ↦ (c - x) ^ j * expTaylor m (x * t)) = _
  simp_rw [hterm, gridAverage_sum, gridAverage_const_mul]
  unfold c
  simp_rw [gridAverage_weighted_pow_eq hp]
  unfold compactPositiveMomentTaylorUpTo
  exact Finset.sum_congr rfl fun n _ ↦ by ring

private theorem gridPoint_bounds {p i : ℕ} (hp : 0 < p)
    (hi : i ∈ Finset.range (p + 1)) : -1 ≤ gridPoint p i ∧ gridPoint p i ≤ 2 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hiR : (i : ℝ) ≤ p := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hnonneg : 0 ≤ 3 / (p : ℝ) * i := by positivity
  have hupper : 3 / (p : ℝ) * i ≤ 3 := calc
    _ ≤ 3 / (p : ℝ) * p := mul_le_mul_of_nonneg_left hiR (by positivity)
    _ = 3 := div_mul_cancel₀ _ hpR.ne'
  unfold gridPoint
  constructor <;> linarith

private theorem spacing_le {p : ℕ} (hp : 11 ≤ p) : 3 / (p : ℝ) ≤ 3 / 11 := by
  have hpR : (11 : ℝ) ≤ p := by exact_mod_cast hp
  exact (div_le_iff₀ (by linarith)).2 (by linarith)

private theorem weight_abs_le {p : ℕ} (hp : 11 ≤ p) {x : ℝ}
    (hx₁ : -1 ≤ x) (hx₂ : x ≤ 2) :
    |2 + 3 / (p : ℝ) - x| ≤ 36 / 11 := by
  rw [abs_of_nonneg (by linarith [show 0 ≤ 3 / (p : ℝ) by positivity])]
  linarith [spacing_le hp]

private theorem abs_pow_le_square_mul {x : ℝ} (hx : |x| ≤ 2) {m : ℕ} (hm : 2 ≤ m) :
    |x| ^ m ≤ x ^ 2 * (2 : ℝ) ^ (m - 2) := by
  calc
    _ = x ^ 2 * |x| ^ (m - 2) := by rw [← sq_abs, ← pow_add, Nat.add_sub_of_le hm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hx _) (sq_nonneg _)

private theorem abs_gridAverage_le_square {p : ℕ} (hp : 0 < p) (f : ℝ → ℝ) (K : ℝ)
    (hf : ∀ i ∈ Finset.range (p + 1), |f (gridPoint p i)| ≤ K * gridPoint p i ^ 2) :
    |gridAverage p f| ≤ K * ((1 + 3 / (p : ℝ)) / 2) := by
  have hsquare : gridAverage p (fun x ↦ x ^ 2) = (1 + 3 / (p : ℝ)) / 2 := by
    rw [gridAverage_eq_marginal]
    exact centered_variance_eq hp
  rw [← hsquare, ← gridAverage_const_mul]
  unfold gridAverage
  rw [abs_div, abs_of_pos (gaps_length_pos p)]
  apply div_le_div_of_nonneg_right _ (gaps_length_pos p).le
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi ↦ ?_)
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  exact mul_le_mul_of_nonneg_left (hf i hi) (Nat.cast_nonneg _)

/-- Absolute bound for each unscaled coefficient of order at least two. -/
theorem compactPositiveMomentCoefficient_abs_le {p j n : ℕ} (hp : 11 ≤ p) (hn : 2 ≤ n) :
    |compactPositiveMomentCoefficient (3 / (p : ℝ)) j n| ≤
      (36 / 11 : ℝ) ^ j * (7 / 11) * 2 ^ (n - 2) := by
  have hp₀ : 0 < p := by omega
  rw [← gridAverage_weighted_pow_eq hp₀]
  let K : ℝ := (36 / 11 : ℝ) ^ j * 2 ^ (n - 2)
  have h := abs_gridAverage_le_square hp₀
    (fun x ↦ (2 + 3 / (p : ℝ) - x) ^ j * x ^ n) K (by
    intro i hi
    obtain ⟨hx₁, hx₂⟩ := gridPoint_bounds hp₀ hi
    have hx : |gridPoint p i| ≤ 2 := abs_le.mpr ⟨by linarith, hx₂⟩
    rw [abs_mul, abs_pow, abs_pow]
    calc
      _ ≤ (36 / 11 : ℝ) ^ j * (gridPoint p i ^ 2 * 2 ^ (n - 2)) :=
        mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (weight_abs_le hp hx₁ hx₂) _)
          (abs_pow_le_square_mul hx hn) (by positivity) (by positivity)
      _ = _ := by unfold K; ring)
  have hvar : (1 + 3 / (p : ℝ)) / 2 ≤ 7 / 11 := by linarith [spacing_le hp]
  exact h.trans ((mul_le_mul_of_nonneg_left hvar (by dsimp [K]; positivity)).trans_eq
    (by unfold K; ring))

private theorem expTaylor_geometric_error {x t R : ℝ} (hx : |x| ≤ 2) (ht : |t| ≤ R)
    {m : ℕ} (hm : 2 ≤ m) (hR : 2 * R / (m.succ : ℝ) < 1) :
    |Real.exp (x * t) - expTaylor m (x * t)| ≤
      x ^ 2 * ((2 * R) ^ m / (4 * (m.factorial : ℝ)) / (1 - 2 * R / (m.succ : ℝ))) := by
  have hR₀ := (abs_nonneg t).trans ht
  have harg : |x * t| ≤ 2 * R := by
    rw [abs_mul]
    exact mul_le_mul hx ht (abs_nonneg _) (by norm_num)
  have hpow : |x * t| ^ m ≤ x ^ 2 * ((2 * R) ^ m / 4) := by
    rw [abs_mul, mul_pow]
    calc
      _ ≤ (x ^ 2 * (2 : ℝ) ^ (m - 2)) * R ^ m :=
        mul_le_mul (abs_pow_le_square_mul hx hm) (pow_le_pow_left₀ (abs_nonneg _) ht _)
          (by positivity) (by positivity)
      _ = _ := by
        rw [show (2 : ℝ) ^ (m - 2) = 2 ^ m / 4 by
          have h := pow_add (2 : ℝ) 2 (m - 2)
          rw [Nat.add_sub_of_le hm] at h
          linarith only [h, show (2 : ℝ) ^ 2 = 4 by norm_num]]
        rw [mul_pow]
        ring
  let ratio := 2 * R / (m.succ : ℝ)
  let leading := x ^ 2 * ((2 * R) ^ m / (4 * (m.factorial : ℝ)))
  have hleading : 0 ≤ leading := by dsimp [leading]; positivity
  have hratio : 0 ≤ ratio := by dsimp [ratio]; positivity
  have hexp : HasSum (fun n : ℕ ↦ (x * t) ^ n / (n.factorial : ℝ)) (Real.exp (x * t)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (x * t)
  have htail := (hasSum_nat_add_iff' m).2 hexp
  have hmajorant := (hasSum_geometric_of_lt_one hratio hR).mul_left leading
  have hnorm := htail.norm_le_of_bounded hmajorant (fun n ↦ by
    have hfactabs : |((n + m).factorial : ℝ)| = ((n + m).factorial : ℝ) :=
      abs_of_nonneg (Nat.cast_nonneg _)
    rw [Real.norm_eq_abs, abs_div, hfactabs, abs_pow]
    have hf : (m.factorial : ℝ) * (m.succ : ℝ) ^ n ≤ ((n + m).factorial : ℝ) := by
      have h : m.factorial * m.succ ^ n ≤ (n + m).factorial := by
        rw [Nat.add_comm n m]
        exact Nat.factorial_mul_pow_le_factorial
      exact_mod_cast h
    calc
      _ ≤ |x * t| ^ (n + m) / ((m.factorial : ℝ) * (m.succ : ℝ) ^ n) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hf
      _ = (|x * t| ^ m / (m.factorial : ℝ)) * (|x * t| / (m.succ : ℝ)) ^ n := by
        rw [pow_add, div_pow, div_mul_div_comm]
        ring
      _ ≤ leading * ratio ^ n := by
        apply mul_le_mul _ (pow_le_pow_left₀ (by positivity) _ _) (by positivity) hleading
        · dsimp [leading]
          exact (div_le_div_of_nonneg_right hpow (by positivity)).trans_eq (by ring)
        · exact div_le_div_of_nonneg_right harg (by positivity))
  rw [Real.norm_eq_abs] at hnorm
  simpa [expTaylor, leading, ratio, div_eq_mul_inv, mul_assoc] using hnorm

/-- Taylor remainder used for centered exponential offsets and their halved centers. -/
theorem compactExp_sub_truncation_geometric_le {z R : ℝ} {m : ℕ} (hm : 2 ≤ m)
    (hz : |z| ≤ R) (hR : R / (m.succ : ℝ) < 1) :
    |Real.exp z - ∑ n ∈ Finset.range m, z ^ n / (n.factorial : ℝ)| ≤
      R ^ m / (m.factorial : ℝ) / (1 - R / (m.succ : ℝ)) := by
  have ht : |z / 2| ≤ R / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right hz (by norm_num)
  have eZ : 2 * (z / 2) = z := by ring
  have eR : 2 * (R / 2) = R := by ring
  have h := expTaylor_geometric_error (x := 2) (t := z / 2) (R := R / 2)
    (by norm_num) ht hm (by rwa [eR])
  rw [eZ, eR, expTaylor] at h
  exact h.trans_eq (by ring)

/-- The degree cutoff for the positive moments with the exact geometric remainder
at the first omitted index on the current coordinate interval. -/
theorem compactPositiveMoment_sub_taylorUpTo_le {p j m : ℕ} (hp : 11 ≤ p) (hm : 2 ≤ m)
    {t R : ℝ} (ht : |t| ≤ R) (hR : 2 * R / (m.succ : ℝ) < 1) :
    |compactPositiveMoment p j t - compactPositiveMomentTaylorUpTo (3 / (p : ℝ)) j m t| ≤
      (36 / 11 : ℝ) ^ j * (7 / 44) * (2 * R) ^ m / (m.factorial : ℝ) /
        (1 - 2 * R / (m.succ : ℝ)) := by
  have hp₀ : 0 < p := by omega
  have hR₀ := (abs_nonneg t).trans ht
  let h : ℝ := 3 / (p : ℝ)
  let c := 2 + h
  let K : ℝ := (36 / 11 : ℝ) ^ j *
    ((2 * R) ^ m / (4 * (m.factorial : ℝ)) / (1 - 2 * R / (m.succ : ℝ)))
  have hratio : 0 ≤ 1 - 2 * R / (m.succ : ℝ) := (sub_pos.mpr hR).le
  have hexp : compactPositiveMoment p j t =
      gridAverage p (fun x ↦ (c - x) ^ j * Real.exp (x * t)) := by
    simp only [compactPositiveMoment, gridAverage, c, h, gridPoint, mul_assoc]
    congr 1
    exact Finset.sum_congr rfl fun _ _ ↦ congrArg (_ * ·) (mul_comm _ _)
  rw [hexp, ← gridAverage_expTaylor_eq hp₀, ← gridAverage_sub]
  have htail := abs_gridAverage_le_square hp₀ (fun x ↦
    (c - x) ^ j * Real.exp (x * t) - (c - x) ^ j * expTaylor m (x * t)) K (by
    intro i hi
    obtain ⟨hx₁, hx₂⟩ := gridPoint_bounds hp₀ hi
    have hx : |gridPoint p i| ≤ 2 := abs_le.mpr ⟨by linarith, hx₂⟩
    change |(c - gridPoint p i) ^ j * Real.exp (gridPoint p i * t) -
      (c - gridPoint p i) ^ j * expTaylor m (gridPoint p i * t)| ≤ K * gridPoint p i ^ 2
    rw [← mul_sub, abs_mul, abs_pow]
    calc
      _ ≤ (36 / 11 : ℝ) ^ j *
          (gridPoint p i ^ 2 * ((2 * R) ^ m / (4 * (m.factorial : ℝ)) /
            (1 - 2 * R / (m.succ : ℝ)))) :=
        mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (weight_abs_le hp hx₁ hx₂) _)
          (expTaylor_geometric_error hx ht hm hR) (abs_nonneg _) (by positivity)
      _ = _ := by unfold K; ring)
  have hvar : (1 + 3 / (p : ℝ)) / 2 ≤ 7 / 11 := by linarith [spacing_le hp]
  exact htail.trans ((mul_le_mul_of_nonneg_left hvar (by dsimp [K]; positivity)).trans_eq
    (by unfold K; ring))

/-- The degree cutoff used for the degree-six comparison. -/
theorem compactPositiveMoment_sub_taylor_geometric_le {p j : ℕ} (hp : 11 ≤ p) (hj : j ≤ 6)
    {t R : ℝ} (ht : |t| ≤ R) (hR : 2 * R / ((25 - j : ℕ).succ : ℝ) < 1) :
    |compactPositiveMoment p j t - compactPositiveMomentTaylor (3 / (p : ℝ)) j t| ≤
      (36 / 11 : ℝ) ^ j * (7 / 44) * (2 * R) ^ (25 - j) / ((25 - j).factorial : ℝ) /
        (1 - 2 * R / ((25 - j : ℕ).succ : ℝ)) :=
  compactPositiveMoment_sub_taylorUpTo_le hp (by omega) ht hR

/-- Uniform absolute error of the compact positive moment polynomial on the small square. -/
theorem compactPositiveMoment_sub_taylor_abs_le {p j : ℕ} (hp : 11 ≤ p) (hj : j ≤ 6)
    {t : ℝ} (ht : |t| ≤ 3 / 2) :
    |compactPositiveMoment p j t - compactPositiveMomentTaylor (3 / (p : ℝ)) j t| ≤
      (36 / 11 : ℝ) ^ j * (7 / 22) * 3 ^ (25 - j) / ((25 - j).factorial : ℝ) := by
  have hm : (20 : ℝ) ≤ ((25 - j : ℕ).succ : ℝ) := by
    exact_mod_cast (by omega : 20 ≤ (25 - j : ℕ).succ)
  have hhalf : 2 * (3 / 2 : ℝ) / ((25 - j : ℕ).succ : ℝ) ≤ 1 / 2 :=
    (div_le_iff₀ (by positivity)).2 (by linarith)
  refine (compactPositiveMoment_sub_taylor_geometric_le hp hj ht
    (hhalf.trans_lt (by norm_num))).trans ?_
  rw [show 2 * (3 / 2 : ℝ) = 3 by norm_num]
  apply (div_le_iff₀ (by linarith : 0 < 1 - 3 / ((25 - j : ℕ).succ : ℝ))).2
  calc
    _ = ((36 / 11 : ℝ) ^ j * (7 / 22) * 3 ^ (25 - j) / ((25 - j).factorial : ℝ)) *
        (1 / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

#print axioms compactPositiveMomentCoefficient_abs_le
#print axioms compactPositiveMoment_sub_taylor_geometric_le
#print axioms compactPositiveMoment_sub_taylor_abs_le

end

end RefinedBMV.PositiveCenter
