/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactPositiveMomentTails
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact coefficients and Taylor remainder for the compact positive moments. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactPositiveMoments
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterMomentPolynomial

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

/-- The unscaled Taylor coefficient of order `n`, before division by `n!`. -/
def compactPositiveMomentCoefficient (h : ℝ) (j n : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (j + 1),
    (-1 : ℝ) ^ l * (j.choose l : ℝ) * (2 + h) ^ (j - l) *
      compactCenteredMomentPolynomial h (n + l)

/-- Taylor polynomial through degree `24 - j` for the weighted exponential moment. -/
def compactPositiveMomentTaylor (h : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (25 - j),
    compactPositiveMomentCoefficient h j n / (n.factorial : ℝ) * t ^ n

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

private theorem gridAverage_expTaylor_eq {p : ℕ} (hp : 0 < p) (j : ℕ) (t : ℝ) :
    gridAverage p (fun x ↦ (2 + 3 / (p : ℝ) - x) ^ j * expTaylor (25 - j) (x * t)) =
      compactPositiveMomentTaylor (3 / (p : ℝ)) j t := by
  let c : ℝ := 2 + 3 / (p : ℝ)
  have hterm (x : ℝ) :
      (c - x) ^ j * expTaylor (25 - j) (x * t) =
        ∑ n ∈ Finset.range (25 - j),
          (t ^ n / (n.factorial : ℝ)) * ((c - x) ^ j * x ^ n) := by
    rw [expTaylor, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ ↦ by rw [mul_pow]; ring
  change gridAverage p (fun x ↦ (c - x) ^ j * expTaylor (25 - j) (x * t)) = _
  simp_rw [hterm, gridAverage_sum, gridAverage_const_mul]
  unfold c
  simp_rw [gridAverage_weighted_pow_eq hp]
  unfold compactPositiveMomentTaylor
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

private theorem expTaylor_error {x t : ℝ} (hx : |x| ≤ 2) (ht : |t| ≤ 3 / 2)
    {m : ℕ} (hm : 19 ≤ m) :
    |Real.exp (x * t) - expTaylor m (x * t)| ≤
      x ^ 2 * ((3 : ℝ) ^ m / (2 * (m.factorial : ℝ))) := by
  have harg : |x * t| ≤ 3 := by
    rw [abs_mul]
    calc
      _ ≤ 2 * (3 / 2) := mul_le_mul hx ht (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hratio : ‖((x * t : ℝ) : ℂ)‖ / (m.succ : ℝ) ≤ 1 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, Nat.cast_succ]
    have hmR : (19 : ℝ) ≤ m := by exact_mod_cast hm
    exact (div_le_iff₀ (by positivity)).2 (by linarith)
  have htail : |Real.exp (x * t) - expTaylor m (x * t)| ≤
      |x * t| ^ m / (m.factorial : ℝ) * 2 := by
    unfold expTaylor
    exact_mod_cast Complex.exp_bound' hratio
  have hpow : |x * t| ^ m ≤ x ^ 2 * ((3 : ℝ) ^ m / 4) := by
    rw [abs_mul, mul_pow]
    calc
      _ ≤ (x ^ 2 * (2 : ℝ) ^ (m - 2)) * (3 / 2 : ℝ) ^ m :=
        mul_le_mul (abs_pow_le_square_mul hx (by omega)) (pow_le_pow_left₀ (abs_nonneg _) ht _)
          (by positivity) (by positivity)
      _ = _ := by
        rw [show (2 : ℝ) ^ (m - 2) = 2 ^ m / 4 by
          have h := pow_add (2 : ℝ) 2 (m - 2)
          rw [Nat.add_sub_of_le (by omega : 2 ≤ m)] at h
          linarith only [h, show (2 : ℝ) ^ 2 = 4 by norm_num]]
        rw [div_pow]
        have htwo : (2 : ℝ) ^ m ≠ 0 := by positivity
        field_simp
  calc
    _ ≤ |x * t| ^ m / (m.factorial : ℝ) * 2 := htail
    _ ≤ (x ^ 2 * ((3 : ℝ) ^ m / 4)) / (m.factorial : ℝ) * 2 :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hpow (by positivity)) (by norm_num)
    _ = _ := by ring

/-- Uniform absolute error of the compact positive moment polynomial for `p ≥ 11`. -/
theorem compactPositiveMoment_sub_taylor_abs_le {p j : ℕ} (hp : 11 ≤ p) (hj : j ≤ 6)
    {t : ℝ} (ht : |t| ≤ 3 / 2) :
    |compactPositiveMoment p j t - compactPositiveMomentTaylor (3 / (p : ℝ)) j t| ≤
      (36 / 11 : ℝ) ^ j * (7 / 22) * 3 ^ (25 - j) / ((25 - j).factorial : ℝ) := by
  have hp₀ : 0 < p := by omega
  let m := 25 - j
  let h : ℝ := 3 / (p : ℝ)
  let c := 2 + h
  let K : ℝ := (36 / 11 : ℝ) ^ j * (3 ^ m / (2 * (m.factorial : ℝ)))
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
          (gridPoint p i ^ 2 * (3 ^ m / (2 * (m.factorial : ℝ)))) :=
        mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (weight_abs_le hp hx₁ hx₂) _)
          (expTaylor_error hx ht (by dsimp [m]; omega)) (abs_nonneg _) (by positivity)
      _ = _ := by unfold K; ring)
  have hvar : (1 + 3 / (p : ℝ)) / 2 ≤ 7 / 11 := by linarith [spacing_le hp]
  exact htail.trans ((mul_le_mul_of_nonneg_left hvar (by dsimp [K]; positivity)).trans_eq
    (by unfold K m; ring))

#print axioms compactPositiveMomentCoefficient_abs_le
#print axioms compactPositiveMoment_sub_taylor_abs_le

end

end RefinedBMV.PositiveCenter
