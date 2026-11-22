/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/LeftStripLowSign
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pointwise sign of the regularized left-strip integrand. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterLeftStripKernel
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterSixBoxes
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMarginalTails

/-! Short Taylor enclosures for the regularized left-strip integrand. -/

open scoped BigOperators
open Set

namespace RefinedBMV.PositiveCenter

open SmallCorner
open DimThree (gaps mem_gaps_iff_total word_counts_all)

open private leftStripX leftStripY leftStripRoot leftStripRootOne leftStripRootTwo
  leftStripRootThree leftStripRegularizedSlope from
  D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterLeftStripKernel
open private sum_first_square_eq jointAverage gapExponent jointAverage_finsetSum jointAverage_mul
  abs_sum_map_sub_le
  from D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterJointTaylor
open private abs_centered_gap_le from
  D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterMomentPolynomial

noncomputable section

private def jointPolynomial (p b : ℕ) (a v : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (11 - b), ∑ i ∈ Finset.range (m + 1),
    jointTaylorMoment p i (b + (m - i)) *
      (a ^ i * v ^ (m - i) / ((i.factorial : ℝ) * ((m - i).factorial : ℝ)))

private theorem jointPolynomial_eq_average (p b : ℕ) (a v : ℝ) :
    jointPolynomial p b a v =
      jointAverage p (fun x y ↦ y ^ b *
        ∑ m ∈ Finset.range (11 - b), (x * a + y * v) ^ m / (m.factorial : ℝ)) := by
  have hexpand (m : ℕ) (x y : ℝ) :
      y ^ b * ((x * a + y * v) ^ m / (m.factorial : ℝ)) =
        ∑ i ∈ Finset.range (m + 1), x ^ i * y ^ (b + (m - i)) *
          (a ^ i * v ^ (m - i) / ((i.factorial : ℝ) * ((m - i).factorial : ℝ))) := by
    rw [add_pow, Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have him : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hchoose : (m.choose i : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos him).ne'
    have hfac : (m.choose i : ℝ) * (i.factorial : ℝ) * ((m - i).factorial : ℝ) =
        (m.factorial : ℝ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial him
    rw [← hfac]
    simp only [mul_pow, pow_add]
    field_simp [hchoose]
  simp only [Finset.mul_sum, hexpand, jointAverage_finsetSum, jointAverage_mul,
    jointPolynomial, jointTaylorMoment]

private theorem centered_argument_abs_le {p : ℕ} (hp : 0 < p) {g : ℕ × ℕ × ℕ}
    (hg : g ∈ gaps p) {a v : ℝ} (ha : 0 ≤ a) (hav : a ≤ v) :
    |leftStripX p g * a + leftStripY p g * v| ≤ 2 * v := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  let x : ℝ := 3 * (g.2.1 : ℝ) / p
  let y : ℝ := 3 * (g.2.2 : ℝ) / p
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hnat : g.2.1 + g.2.2 ≤ p := by
    have h := (mem_gaps_iff_total p g).mp hg
    omega
  have hreal : (g.2.1 : ℝ) + (g.2.2 : ℝ) ≤ p := by exact_mod_cast hnat
  have ht : x + y ≤ 3 := by
    dsimp [x, y]
    rw [← add_div, ← mul_add]
    exact (div_le_iff₀ hpR).mpr (mul_le_mul_of_nonneg_left hreal (by norm_num))
  have hs := mul_le_mul_of_nonneg_right ht (ha.trans hav)
  rw [add_mul] at hs
  change |(x - 1) * a + (y - 1) * v| ≤ 2 * v
  exact abs_le.mpr ⟨by linarith [mul_nonneg hx ha, mul_nonneg hy (ha.trans hav)],
    by linarith [mul_le_mul_of_nonneg_left hav hx]⟩

private theorem jointTaylor_error {p b : ℕ} (hp : 0 < p) (hb : b ≤ 1) {a v : ℝ}
    (ha : 0 ≤ a) (hav : a ≤ v) (hv : v ≤ 3 / 2) :
    |leftStripExpMoment p 2 b a v / (compositionMarginalVariance p / 2) -
      jointPolynomial p b a v| ≤
      (2 : ℝ) ^ (b + 2) * (2 * v) ^ (11 - b) / ((11 - b).factorial : ℝ) := by
  let n := 11 - b
  let c : ℝ := (2 : ℝ) ^ (b + 1) * (2 * v) ^ n / (n.factorial : ℝ)
  let x := leftStripX p
  let y := leftStripY p
  have hden : 0 < ((gaps p).length : ℝ) * (compositionMarginalVariance p / 2) :=
    mul_pos (by exact_mod_cast (word_counts_all p).2.1)
      (half_pos (compositionMarginalVariance_pos p))
  have hn : 10 ≤ n := by dsimp [n]; omega
  have hloc (g : ℕ × ℕ × ℕ) (hg : g ∈ gaps p) :
      |x g ^ 2 * y g ^ b * Real.exp (x g * a + y g * v) -
        x g ^ 2 * (y g ^ b *
          ∑ m ∈ Finset.range n, (x g * a + y g * v) ^ m / (m.factorial : ℝ))| ≤
        x g ^ 2 * c := by
    let z := x g * a + y g * v
    have hz : |z| ≤ 2 * v := centered_argument_abs_le hp hg ha hav
    have hratio : ‖(z : ℂ)‖ / (n.succ : ℝ) ≤ 1 / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, Nat.cast_succ]
      apply (div_le_iff₀ (by positivity)).2
      have hnr : (10 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have ht : |Real.exp z - ∑ m ∈ Finset.range n, z ^ m / (m.factorial : ℝ)| ≤
        |z| ^ n / (n.factorial : ℝ) * 2 := by
      exact_mod_cast Complex.exp_bound' hratio
    have hy : |y g| ≤ 2 := abs_centered_gap_le hp (show g.2.2 ≤ p by
      have h := (mem_gaps_iff_total p g).mp hg
      omega)
    change |x g ^ 2 * y g ^ b * Real.exp z -
      x g ^ 2 * (y g ^ b * ∑ m ∈ Finset.range n, z ^ m / (m.factorial : ℝ))| ≤ _
    rw [mul_assoc, ← mul_sub, ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _),
      abs_mul, abs_pow]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    calc
      _ ≤ 2 ^ b * ((2 * v) ^ n / (n.factorial : ℝ) * 2) := by
        gcongr
        exact ht.trans (by gcongr)
      _ = c := by dsimp [c]; rw [pow_succ]; ring
  rw [jointPolynomial_eq_average, leftStripExpMoment, jointAverage, div_div]
  change |(_ : ℝ) / _ - (_ : ℝ) / _| ≤ _
  rw [← sub_div, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  refine (abs_sum_map_sub_le _ _ _ _ hloc).trans_eq ?_
  change ((gaps p).map fun g ↦ x g ^ 2 * c).sum = _
  rw [List.sum_map_mul_right, show ((gaps p).map fun g ↦ x g ^ 2).sum = _ from
    sum_first_square_eq p]
  dsimp [c, n]
  rw [show b + 2 = (b + 1) + 1 by omega, pow_succ]
  ring

open private leftStripZ from D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterLeftStripKernel

private def marginalCoefficient (p k i : ℕ) : ℝ :=
  momentHorner (3 / (p : ℝ)) (normalizedMomentCoeffs 0 (k + i + 2)) *
    ((k + i).factorial : ℝ) / (i.factorial : ℝ)

private theorem marginalTaylor_eq_coefficients {p : ℕ} (hp : 0 < p) (k : ℕ) (x : ℝ) :
    marginalTaylorPolynomial p k x =
      ∑ i ∈ Finset.range (23 - k), marginalCoefficient p k i * x ^ i := by
  unfold marginalTaylorPolynomial
  apply Finset.sum_congr rfl
  intro i _
  rw [marginalCoefficient, normalized_moment_eval_swap 0 (k + i + 2) (by omega),
    normalized_moment_eval_joint hp]
  simp only [Nat.factorial_zero, Nat.cast_one, mul_one]
  rw [Nat.factorial_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_mul,
    Nat.cast_succ, Nat.cast_succ]
  field_simp [show (0 : ℝ) < (k + i).factorial by positivity,
    show (0 : ℝ) < (↑(k + i) : ℝ) + 1 by positivity,
    show (0 : ℝ) < (↑(k + i) : ℝ) + 1 + 1 by positivity]
  <;> ring

private theorem marginalCoefficient_abs_le {p : ℕ} (hp : 0 < p) (k i : ℕ) :
    |marginalCoefficient p k i| ≤
      (2 : ℝ) ^ (k + i + 1) /
        ((i.factorial : ℝ) * ((k + i : ℕ) + 1 : ℝ) * ((k + i : ℕ) + 2 : ℝ)) := by
  unfold marginalCoefficient
  rw [abs_div, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k + i).factorial),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ i.factorial)]
  calc
    _ ≤ ((2 : ℝ) ^ (k + i + 1) / ((k + i + 2).factorial : ℝ)) *
        ((k + i).factorial : ℝ) / (i.factorial : ℝ) := by
      gcongr
      exact normalized_moment_abs_bound_marginal hp (k + i)
    _ = _ := by
      rw [Nat.factorial_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_mul,
        Nat.cast_succ, Nat.cast_succ]
      push_cast
      field_simp [show (0 : ℝ) < (k + i).factorial by positivity,
        show (0 : ℝ) < (↑k + ↑i + 1 : ℝ) by positivity,
        show (0 : ℝ) < (↑k + ↑i + 1 + 1 : ℝ) by positivity]
      <;> ring

private def marginalPolynomial (p k : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (11 - k), marginalCoefficient p k i * x ^ i

private theorem marginalTaylor_error {p k : ℕ} (hp : 0 < p) (hk : k ≤ 3) {t : ℝ}
    (ht : |t| ≤ if k ≤ 1 then 3 / 2 else 1) :
    |leftStripZ p k t - marginalPolynomial p k t| ≤ 1 / 500 := by
  have hlong : |leftStripZ p k t - marginalTaylorPolynomial p k t| ≤ 1 / 1000 := by
    by_cases hk₁ : k ≤ 1
    · have ht' : |t| ≤ 2 := (by simpa [hk₁] using ht : |t| ≤ 3 / 2).trans (by norm_num)
      have h := iteratedDeriv_compactZ_sub_taylor_le_two hp (show k ≤ 2 by omega) ht'
      rw [iteratedDeriv_compactZ_eq_integral hp, compactKappa, ← joint_normalization_eq hp] at h
      refine h.trans ?_
      interval_cases k <;> norm_num [Nat.factorial]
    · have ht' : |t| ≤ 1 := by simpa [hk₁] using ht
      exact (integralMarginalDerivative_sub_taylor_le hp (show k ≤ 4 by omega) ht').trans
        (by norm_num)
  have hcut : 23 - k = (11 - k) + 12 := by omega
  have hshort : |marginalTaylorPolynomial p k t - marginalPolynomial p k t| ≤ 1 / 1000 := by
    rw [marginalTaylor_eq_coefficients hp, marginalPolynomial, hcut, Finset.sum_range_add,
      add_sub_cancel_left]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    let bound (k i : ℕ) : ℝ :=
      (2 : ℝ) ^ (k + (11 - k + i) + 1) * (if k ≤ 1 then 3 / 2 else (1 : ℝ)) ^ (11 - k + i) /
        (((11 - k + i).factorial : ℝ) * ((k + (11 - k + i) : ℕ) + 1 : ℝ) *
          ((k + (11 - k + i) : ℕ) + 2 : ℝ))
    calc
      _ ≤ ∑ i ∈ Finset.range 12, bound k i := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        rw [abs_mul, abs_pow]
        dsimp only [bound]
        rw [mul_div_right_comm]
        gcongr
        exact marginalCoefficient_abs_le hp k (11-k+i)
      _ ≤ _ := by
        interval_cases k <;> norm_num [bound, Finset.sum_range_succ, Nat.factorial]
  calc
    _ ≤ |leftStripZ p k t - marginalTaylorPolynomial p k t| +
        |marginalTaylorPolynomial p k t - marginalPolynomial p k t| := by
      simpa only [sub_add_sub_cancel] using
        abs_add_le (leftStripZ p k t - marginalTaylorPolynomial p k t)
          (marginalTaylorPolynomial p k t - marginalPolynomial p k t)
    _ ≤ _ := by linarith

open private sum_triangle from D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterJointTaylorReplay
open private dyadicHorner dyadicHorner_encloses inv encloses_inv root encloses_root from
  D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterSixBoxes

private abbrev Interval := RoundedInterval
private abbrev point := RoundedInterval.point
private abbrev box := RoundedInterval.interval

private def series : ℕ → (ℕ → Interval) → Interval → Interval
  | 0, _, _ => 0
  | n+1, f, x => f 0 + x * series n (fun i ↦ f (i+1)) x

set_option maxHeartbeats 1000000 in
private theorem series_encloses (n : ℕ) {X : Interval} {x : ℝ} (hx : X.encloses x)
    {F : ℕ → Interval} {f : ℕ → ℝ} (hf : ∀ i < n, (F i).encloses (f i)) :
    (series n F X).encloses (∑ i ∈ Finset.range n, f i * x ^ i) := by
  induction n generalizing F f with
  | zero =>
    rw [series, Finset.range_zero, Finset.sum_empty]
    change (point 0).encloses (0 : ℝ)
    simpa only [Rat.cast_zero] using (RoundedInterval.encloses_point 0)
  | succ n ih =>
    have hi := ih (F := fun i ↦ F (i+1)) (f := fun i ↦ f (i+1))
      (fun i hi ↦ hf (i+1) (by omega))
    rw [Finset.sum_range_succ', pow_zero, mul_one]
    have hs : (∑ i ∈ Finset.range n, f (i+1) * x^(i+1)) =
        x * (∑ i ∈ Finset.range n, f (i+1) * x^i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [pow_succ]; ring
    rw [hs, add_comm _ (f 0)]
    change (F 0 + X * series n (fun i ↦ F (i+1)) X).encloses _
    exact RoundedInterval.encloses_add (hf 0 (by omega)) (RoundedInterval.encloses_mul hx hi)

private def momentBox (H : Interval) (a b : ℕ) : Interval :=
  ⟨dyadicHorner H.endpoints (certifiedMomentDenominator a b) (stagedNumerators a b)⟩

private theorem momentBox_encloses (a b : ℕ) {H : Interval} {h : ℝ}
    (hh : H.encloses h) (hdegree : a+b ≤ 12) (hlow : 2 ≤ a+b) (ha : a = 0 ∨ 2 ≤ a) :
    (momentBox H a b).encloses (momentHorner h (normalizedMomentCoeffs a b)) := by
  rw [← certifiedMomentCoeffs_eq, certifiedMomentCoeffs, ← stagedNumerators_eq hdegree hlow ha]
  exact dyadicHorner_encloses hh _ _

private def zBox (H T : Interval) (k : ℕ) : Interval :=
  series (11-k) (fun i ↦ point ((k+i).factorial / (i.factorial : ℚ)) *
    momentBox H 0 (k+i+2)) T + box (-1/500) (1/500)

private theorem zBox_encloses {p : ℕ} (hp : 0 < p) {k : ℕ} (hk : k ≤ 3) {H T : Interval}
    {t : ℝ} (hh : H.encloses (3 / (p : ℝ))) (ht : T.encloses t)
    (htop : |t| ≤ if k ≤ 1 then 3/2 else 1) : (zBox H T k).encloses (leftStripZ p k t) := by
  have hz := abs_le.mp (marginalTaylor_error hp hk htop)
  have hp' : (series (11-k) (fun i ↦ point ((k+i).factorial / (i.factorial : ℚ)) *
      momentBox H 0 (k+i+2)) T).encloses (marginalPolynomial p k t) := by
    apply series_encloses _ ht
    intro i hi
    have h := RoundedInterval.encloses_mul
      (RoundedInterval.encloses_point ((k+i).factorial / (i.factorial : ℚ)))
      (momentBox_encloses 0 (k+i+2) hh (by omega) (by omega) (Or.inl rfl))
    convert h using 2
    simp only [Rat.cast_div, Rat.cast_natCast, marginalCoefficient]
    ring
  convert RoundedInterval.encloses_add hp'
    (RoundedInterval.encloses_interval (x := leftStripZ p k t - marginalPolynomial p k t)
      (lo := -1/500) (hi := 1/500) (by push_cast; linarith only [hz.1]) (by push_cast; exact hz.2)) using 1 <;> first | rfl | ring

private def jointCoefficient (H : Interval) (b i j : ℕ) : Interval :=
  point ((((i+1)*(i+2)*(if b = 0 then 1 else j+1) : ℕ) : ℚ)) * momentBox H (i+2) (b+j)

private theorem jointCoefficient_encloses {p b i j : ℕ} (hp : 0 < p) (hb : b ≤ 1)
    (hdegree : i+2+(b+j) ≤ 12) {H : Interval} (hh : H.encloses (3 / (p : ℝ))) :
    (jointCoefficient H b i j).encloses
      (jointTaylorMoment p i (b+j) / ((i.factorial : ℝ) * (j.factorial : ℝ))) := by
  have h := RoundedInterval.encloses_mul
    (RoundedInterval.encloses_point ((((i+1)*(i+2)*(if b = 0 then 1 else j+1) : ℕ) : ℚ)))
    (momentBox_encloses (i+2) (b+j) hh hdegree (by omega) (Or.inr (by omega)))
  convert h using 2
  · rfl
  rw [normalized_moment_eval_joint hp, Nat.factorial_succ, Nat.factorial_succ]
  have hj : (0 : ℝ) < j.factorial := by positivity
  have hi : (0 : ℝ) < i.factorial := by positivity
  have hi₁ : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have hi₂ : (0 : ℝ) < (i : ℝ) + 1 + 1 := by positivity
  have hj₁ : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  interval_cases b <;> simp only [Nat.zero_add, Nat.reduceEqDiff, if_true, if_false,
    mul_one, Rat.cast_natCast, Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.cast_succ]
  · field_simp <;> ring
  · rw [Nat.add_comm 1 j, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    field_simp <;> ring

private def jointBox (H A V : Interval) (b : ℕ) : Interval :=
  let error : ℚ := if b = 0 then 1/50 else 2/15
  series (11-b) (fun i ↦ series (11-b-i) (jointCoefficient H b i) V) A +
    box (-error) error

set_option maxHeartbeats 1000000 in
private theorem jointBox_encloses {p b : ℕ} (hp : 0 < p) (hb : b ≤ 1) {H A V : Interval}
    {a v : ℝ} (hh : H.encloses (3 / (p : ℝ))) (ha : A.encloses a) (hv : V.encloses v)
    (ha₀ : 0 ≤ a) (hav : a ≤ v) (hvtop : v ≤ 3/2) :
    (jointBox H A V b).encloses (leftStripExpMoment p 2 b a v / (compositionMarginalVariance p / 2)) := by
  let error (b : ℕ) : ℚ := if b = 0 then 1/50 else 2/15
  have hpoly :
      (series (11-b) (fun i ↦ series (11-b-i) (jointCoefficient H b i) V) A).encloses
        (jointPolynomial p b a v) := by
    unfold jointPolynomial
    rw [sum_triangle (11 - b) (fun i j ↦
      jointTaylorMoment p i (b+j) * (a^i * v^j / ((i.factorial : ℝ) * (j.factorial : ℝ))))]
    have hrow (i : ℕ) (hi : i < 11-b) :=
      series_encloses (11-b-i) hv (fun j hj ↦ jointCoefficient_encloses (i := i) (j := j) hp hb (by omega) hh)
    convert series_encloses (11-b) ha hrow using 2
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hf : (2 : ℝ) ^ (b+2) * (2*v) ^ (11-b) / ((11-b).factorial : ℝ) ≤ (error b : ℝ) := by
    calc
      _ ≤ (2 : ℝ) ^ (b+2) * 3 ^ (11-b) / ((11-b).factorial : ℝ) := by
        gcongr
        · linarith [ha₀.trans hav]
        · linarith
      _ ≤ _ := by interval_cases b <;> norm_num [error, Nat.factorial]
  have he := abs_le.mp ((jointTaylor_error hp hb ha₀ hav hvtop).trans hf)
  convert RoundedInterval.encloses_add hpoly
    (RoundedInterval.encloses_interval (lo := -error b) (hi := error b)
      (by simpa only [Rat.cast_neg] using he.1) he.2) using 1 <;> first | rfl | ring

open private dyadicBounds from D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterSixBoxes

private def reciprocalBox (A : Interval) : Interval :=
  let B := inv (dyadicBounds A.endpoints)
  box B.1 B.2

private theorem reciprocalBox_encloses {A : Interval} {x : ℝ} (h : A.encloses x)
    (hx : 1/64 ≤ x) : (reciprocalBox A).encloses (1/x) :=
  let h' := encloses_inv h hx
  RoundedInterval.encloses_interval h'.1 h'.2

private def sqrtBox (A : Interval) : Interval :=
  let B := root (dyadicBounds A.endpoints)
  box B.1 B.2

private theorem sqrtBox_encloses {A : Interval} {x : ℝ} (h : A.encloses x)
    (hl : 1/8 ≤ x) (hu : x ≤ 8) : (sqrtBox A).encloses (Real.sqrt x) :=
  let h' := encloses_root h hl hu
  RoundedInterval.encloses_interval h'.1 h'.2

private def validZ (A : Interval) : Prop := 1/8 ≤ A.lower ∧ A.upper ≤ 8

private instance (A : Interval) : Decidable (validZ A) :=
  inferInstanceAs (Decidable (_ ≤ _ ∧ _ ≤ _))

private theorem validZ_bounds {A : Interval} {x : ℝ} (hA : validZ A) (h : A.encloses x) :
    1/8 ≤ x ∧ x ≤ 8 := by
  have hl := Rat.cast_le (K := ℝ).mpr hA.1
  have hu := Rat.cast_le (K := ℝ).mpr hA.2
  norm_num at hl hu
  exact ⟨hl.trans h.1, h.2.trans hu⟩

private def integrandBox (H A D V Zd Zv Zn : Interval) : Interval :=
  let r := sqrtBox Zd
  let q := reciprocalBox (point 2 * r)
  let r1 := zBox H D 1 * q
  let r2 := (zBox H D 2 - point 2 * (r1 * r1)) * q
  let r3 := (zBox H D 3 - point 6 * (r1 * r2)) * q
  let b := zBox H (0 - V) 1 * reciprocalBox (point 2 * Zn)
  let s := zBox H V 1 * reciprocalBox (point 2 * Zv)
  let rad := V * sqrtBox Zv * (point 3 * r2 + D * r3 +
    (s + b) * (point 2 * r1 + D * r2))
  V * (rad - jointBox H A V 1) + (point 1 - V * b) * jointBox H A V 0

set_option maxHeartbeats 1000000 in
private theorem integrandBox_sound {p : ℕ} (hp : 0 < p) {a v : ℝ} {H A D V : Interval}
    (hh : H.encloses (3 / (p : ℝ))) (ha : A.encloses a) (hd : D.encloses (v-a))
    (hv : V.encloses v) (ha₀ : 0 ≤ a) (hd₀ : 0 ≤ v-a)
    (hd₁ : v-a ≤ 1) (hv₁ : v ≤ 3/2)
    (hZd : validZ (zBox H D 0)) (hZv : validZ (zBox H V 0)) (hZn : validZ (zBox H (0-V) 0))
    (hcheck : 0 < (integrandBox H A D V (zBox H D 0) (zBox H V 0) (zBox H (0-V) 0)).lower) :
    0 < leftStripRegularizedIntegrand p a v := by
  let d := v-a
  let c := compositionMarginalVariance p / 2
  have hc : 0 < c := half_pos (compositionMarginalVariance_pos p)
  have hav : a ≤ v := by linarith
  have hv₀ := ha₀.trans hav
  have hAbsD : |d| ≤ 1 := by rwa [abs_of_nonneg hd₀]
  have hAbsV : |v| ≤ 3/2 := by rwa [abs_of_nonneg hv₀]
  have hNegV : (0 - V).encloses (-v) := by
    change (point 0 - V).encloses (-v)
    simpa only [Rat.cast_zero, zero_sub] using
      RoundedInterval.encloses_sub (RoundedInterval.encloses_point 0) hv
  have zd (k : ℕ) (hk : k ≤ 3) :
      (zBox H D k).encloses (leftStripZ p k d) :=
    zBox_encloses hp hk hh hd (by split <;> linarith)
  have zv (k : ℕ) (hk : k ≤ 1) :
      (zBox H V k).encloses (leftStripZ p k v) :=
    zBox_encloses hp (by omega) hh hv (by simpa only [if_pos hk] using hAbsV)
  have zn (k : ℕ) (hk : k ≤ 1) :
      (zBox H (0-V) k).encloses (leftStripZ p k (-v)) :=
    zBox_encloses hp (by omega) hh hNegV (by simpa only [if_pos hk, abs_neg] using hAbsV)
  have hdZ := validZ_bounds hZd (zd 0 (by decide))
  have hvZ := validZ_bounds hZv (zv 0 (by decide))
  have hnZ := validZ_bounds hZn (zn 0 (by decide))
  have rd : (sqrtBox (zBox H D 0)).encloses (leftStripRoot p d) :=
    sqrtBox_encloses (zd 0 (by decide)) hdZ.1 hdZ.2
  have rv : (sqrtBox (zBox H V 0)).encloses (leftStripRoot p v) :=
    sqrtBox_encloses (zv 0 (by decide)) hvZ.1 hvZ.2
  have hr : 1/4 ≤ leftStripRoot p d := by
    unfold leftStripRoot
    exact (Real.le_sqrt (by norm_num) (by linarith [hdZ.1])).2 (by linarith [hdZ.1])
  have C (q : ℚ) := RoundedInterval.encloses_point q
  have M := @RoundedInterval.encloses_mul
  have S := @RoundedInterval.encloses_sub
  have P := @RoundedInterval.encloses_add
  have q := reciprocalBox_encloses (RoundedInterval.encloses_mul (C 2) rd)
    (by push_cast; linarith)
  have r1 := M (zd 1 (by decide)) q
  simp only [Rat.cast_ofNat, ← div_eq_mul_one_div] at r1
  rw [← leftStripRootOne] at r1
  have r2 := M (S (zd 2 (by decide)) (M (C 2) (M r1 r1))) q
  simp only [Rat.cast_ofNat, ← pow_two, ← div_eq_mul_one_div] at r2
  rw [← leftStripRootTwo] at r2
  have r3 := M (S (zd 3 (by decide)) (M (C 6) (M r1 r2))) q
  simp only [Rat.cast_ofNat, ← mul_assoc, ← div_eq_mul_one_div] at r3
  rw [← leftStripRootThree] at r3
  have b := M (zn 1 (by decide)) (reciprocalBox_encloses (M (C 2) (zn 0 (by decide)))
    (by push_cast; linarith [hnZ.1]))
  have s := M (zv 1 (by decide)) (reciprocalBox_encloses (M (C 2) (zv 0 (by decide)))
    (by push_cast; linarith [hvZ.1]))
  simp only [Rat.cast_ofNat, ← div_eq_mul_one_div] at b s
  rw [← leftStripRegularizedSlope] at b s
  have rad := M (M hv rv) (P (P (M (C 3) r2) (M hd r3))
    (M (P s b) (P (M (C 2) r1) (M hd r2))))
  have J (k : ℕ) (hk : k ≤ 1) := jointBox_encloses hp hk hh ha hv ha₀ hav hv₁
  have result := P (M hv (S rad (J 1 (by decide))))
    (M (S (C 1) (M hv b)) (J 0 (by decide)))
  have pos := (Rat.cast_lt (K := ℝ).mpr hcheck).trans_le result.1
  simp only [Rat.cast_zero, Rat.cast_one, Rat.cast_ofNat] at pos
  unfold leftStripRegularizedIntegrand
  rw [← joint_normalization_eq hp]
  have he (t : ℝ) : c * (t/c) = t := by rw [mul_comm, div_mul_cancel₀ _ hc.ne']
  convert mul_pos hc pos using 1
  simp only [Rat.cast_ofNat, Rat.cast_one]
  rw [show
      c * (v * (v * leftStripRoot p v *
        (3 * leftStripRootTwo p d + d * leftStripRootThree p d +
          (leftStripRegularizedSlope p v + leftStripRegularizedSlope p (-v)) *
            (2 * leftStripRootOne p d + d * leftStripRootTwo p d)) -
            leftStripExpMoment p 2 1 a v / c) +
        (1-v * leftStripRegularizedSlope p (-v)) * (leftStripExpMoment p 2 0 a v / c)) =
      v * (c * v * leftStripRoot p v *
        (3 * leftStripRootTwo p d + d * leftStripRootThree p d +
          (leftStripRegularizedSlope p v + leftStripRegularizedSlope p (-v)) *
            (2 * leftStripRootOne p d + d * leftStripRootTwo p d)) -
            c * (leftStripExpMoment p 2 1 a v / c)) +
        (1-v * leftStripRegularizedSlope p (-v)) * (c * (leftStripExpMoment p 2 0 a v / c)) by ring,
    he, he]

private def checkBox (H A D : Interval) : Bool :=
  let V := A + D
  let Zd := zBox H D 0
  let Zv := zBox H V 0
  let Zn := zBox H (0-V) 0
  decide (validZ Zd ∧ validZ Zv ∧ validZ Zn ∧ 0 < (integrandBox H A D V Zd Zv Zn).lower)

private theorem checkBox_sound {p : ℕ} (hp : 0 < p) {a v : ℝ} {H A D : Interval}
    (hh : H.encloses (3 / (p : ℝ))) (ha : A.encloses a) (hd : D.encloses (v-a))
    (ha₀ : 0 ≤ a) (hd₀ : 0 ≤ v-a) (hd₁ : v-a ≤ 1) (hv₁ : v ≤ 3/2)
    (hc : checkBox H A D = true) : 0 < leftStripRegularizedIntegrand p a v := by
  have hv : (A+D).encloses v := by
    convert RoundedInterval.encloses_add ha hd using 1
    ring
  obtain ⟨hZd, hZv, hZn, hpos⟩ := of_decide_eq_true hc
  exact integrandBox_sound hp hh ha hd hv ha₀ hd₀ hd₁ hv₁ hZd hZv hZn hpos

private abbrev Endpoints := ℚ × ℚ
private def intervalOf (A : Endpoints) : Interval := box A.1 A.2
private def InInterval (A : Endpoints) (x : ℝ) : Prop := (A.1 : ℝ) ≤ x ∧ x ≤ (A.2 : ℝ)
private def midpoint (A : Endpoints) : ℚ := (A.1 + A.2)/2
private def lowerHalf (A : Endpoints) : Endpoints := (A.1, midpoint A)
private def upperHalf (A : Endpoints) : Endpoints := (midpoint A, A.2)

private theorem in_half {A : Endpoints} {x : ℝ} (hx : InInterval A x) :
    InInterval (lowerHalf A) x ∨ InInterval (upperHalf A) x := by
  rcases le_total x (midpoint A : ℝ) with h | h
  · exact Or.inl ⟨hx.1, h⟩
  · exact Or.inr ⟨h, hx.2⟩

private def checkCover (depth : ℕ) (H A D : Endpoints) : Bool :=
  if checkBox (intervalOf H) (intervalOf A) (intervalOf D) then true else
    match depth with
    | 0 => false
    | n + 1 =>
      if (n+1) % 3 = 0 then
        checkCover n H (lowerHalf A) D && checkCover n H (upperHalf A) D
      else if (n+1) % 3 = 2 then
        checkCover n H A (lowerHalf D) && checkCover n H A (upperHalf D)
      else
        checkCover n (lowerHalf H) A D && checkCover n (upperHalf H) A D

private theorem checkCover_sound {p : ℕ} (hp : 0 < p) {a v : ℝ}
    (ha₀ : 0 ≤ a) (hd₀ : 0 ≤ v-a) (hd₁ : v-a ≤ 1) (hv₁ : v ≤ 3/2)
    (n : ℕ) (H A D : Endpoints) (hh : InInterval H (3 / (p : ℝ)))
    (ha : InInterval A a) (hd : InInterval D (v-a))
    (hc : checkCover n H A D = true) : 0 < leftStripRegularizedIntegrand p a v := by
  have localSound {H A D : Endpoints} (hh : InInterval H (3 / (p : ℝ)))
      (ha : InInterval A a) (hd : InInterval D (v-a))
      (hb : checkBox (intervalOf H) (intervalOf A) (intervalOf D) = true) :
      0 < leftStripRegularizedIntegrand p a v :=
    checkBox_sound hp (RoundedInterval.encloses_interval hh.1 hh.2)
      (RoundedInterval.encloses_interval ha.1 ha.2)
      (RoundedInterval.encloses_interval hd.1 hd.2) ha₀ hd₀ hd₁ hv₁ hb
  induction n generalizing H A D with
  | zero =>
    rw [checkCover] at hc
    split at hc
    · exact localSound hh ha hd (by assumption)
    · contradiction
  | succ n ih =>
    rw [checkCover] at hc
    split at hc
    · exact localSound hh ha hd (by assumption)
    · split at hc
      · obtain ⟨hlo, hhi⟩ := Bool.and_eq_true_iff.mp hc
        rcases in_half ha with ha | ha
        · exact ih _ _ _ hh ha hd hlo
        · exact ih _ _ _ hh ha hd hhi
      · split at hc
        · obtain ⟨hlo, hhi⟩ := Bool.and_eq_true_iff.mp hc
          rcases in_half hd with hd | hd
          · exact ih _ _ _ hh ha hd hlo
          · exact ih _ _ _ hh ha hd hhi
        · obtain ⟨hlo, hhi⟩ := Bool.and_eq_true_iff.mp hc
          rcases in_half hh with hh | hh
          · exact ih _ _ _ hh ha hd hlo
          · exact ih _ _ _ hh ha hd hhi

set_option maxHeartbeats 0 in
-- The kernel reduces the closed interval check without generating a large replay term.
set_option maxRecDepth 20000 in
private theorem check_origin : checkCover 12 (0, 3/11) (0, 1/2) (0, 1/2) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- The kernel reduces the closed interval check without generating a large replay term.
set_option maxRecDepth 20000 in
private theorem check_adjacent : checkCover 12 (0, 3/11) (0, 1/2) (1/2, 1) = true := by
  decide +kernel

/-- The regularized integrand is positive at every integration point of the low left strip. -/
theorem leftStripRegularizedIntegrand_pos {p : ℕ} (hp : 11 ≤ p)
    {a v : ℝ} (ha : 0 ≤ a) (ha₁ : a ≤ 1 / 2) (hd : 0 < v-a) (hd₁ : v-a ≤ 1) :
    0 < leftStripRegularizedIntegrand p a v := by
  have hp₀ : 0 < p := by omega
  have hh : InInterval (0, 3/11) (3 / (p : ℝ)) := by
    constructor
    · push_cast
      positivity
    · norm_num
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by exact_mod_cast hp)
  have ha' : InInterval (0, 1/2) a := by exact ⟨by simpa using ha, by simpa using ha₁⟩
  have hv₁ : v ≤ 3/2 := by linarith
  rcases le_total (v-a) (1/2) with h | h
  · exact checkCover_sound hp₀ ha hd.le hd₁ hv₁ 12 _ _ _ hh ha'
      ⟨by simpa using hd.le, by simpa using h⟩ check_origin
  · exact checkCover_sound hp₀ ha hd.le hd₁ hv₁ 12 _ _ _ hh ha'
      ⟨by simpa using h, by simpa using hd₁⟩ check_adjacent

/-- The low left strip of the exact logarithmic kernel has strictly negative mixed derivative. -/
theorem leftStrip_logKernel_mixed_lt_low {p : ℕ} (hp : 11 ≤ p)
    {u v : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1 / 2) (huv : u < v) (hd : v-u ≤ 1 / 2) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  apply leftStrip_logKernel_mixed_lt_of_low_integrand hp hu hu₁ huv hd
  · intro a y ha ha₁ hgap hgap₁
    exact leftStripRegularizedIntegrand_pos hp ha ha₁ hgap (by linarith)
  · intro a y ha ha₁ hgap hgap₁
    exact div_pos (leftStripRegularizedIntegrand_pos hp ha ha₁ (by linarith) hgap₁) (by linarith)

#print axioms leftStripRegularizedIntegrand_pos
#print axioms leftStrip_logKernel_mixed_lt_low

end

end RefinedBMV.PositiveCenter
