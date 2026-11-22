/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/LeftStripWideBounds
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Taylor and rounded interval bounds for the extended left strip. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripLowSign

/-! Interval enclosures for the extended left strip with both marginal and joint arguments
of absolute value at most `3/2`. -/

open MeasureTheory Set
open scoped BigOperators

namespace RefinedBMV.PositiveCenter

open SmallCorner
open DimThree (gaps mem_gaps_iff_total word_counts_all)

open private leftStripX leftStripY leftStripRoot leftStripRootOne leftStripRootTwo
  leftStripRootThree leftStripRegularizedSlope leftStripZ leftStripExpMoment
  leftStripRegularizedIntegrand from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripCollision
open private sum_first_square_eq jointAverage jointAverage_finsetSum jointAverage_mul
  abs_sum_map_sub_le from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.JointTaylor
open private abs_centered_gap_le from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MomentPolynomial
open private Gap exponent denominator denominator_pos exponent_abs_le sum_marginal_square
  list_sum_map_finsetSum marginal_power_sum_eq from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MarginalTaylor
open private scalarPolynomial from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripTaylor
open private series series_encloses momentBox momentBox_encloses jointCoefficient
  jointCoefficient_encloses marginalCoefficient sum_triangle centered_argument_abs_le
  reciprocalBox reciprocalBox_encloses sqrtBox sqrtBox_encloses validZ validZ_bounds
  Endpoints InInterval intervalOf lowerHalf upperHalf in_half
  from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripLowSign

noncomputable section

private abbrev Interval := RoundedInterval
private abbrev point := RoundedInterval.point
private abbrev box := RoundedInterval.interval

private def wideJointPolynomial (p b : ℕ) (a v : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (15 - b), ∑ i ∈ Finset.range (m + 1),
    jointTaylorMoment p i (b + (m - i)) *
      (a ^ i * v ^ (m - i) / ((i.factorial : ℝ) * ((m - i).factorial : ℝ)))

private theorem wideJointPolynomial_eq_average (p b : ℕ) (a v : ℝ) :
    wideJointPolynomial p b a v =
      jointAverage p (fun x y ↦ y ^ b *
        ∑ m ∈ Finset.range (15 - b), (x * a + y * v) ^ m / (m.factorial : ℝ)) := by
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
    wideJointPolynomial, jointTaylorMoment]

private theorem wideJointTaylor_error {p b : ℕ} (hp : 0 < p) (hb : b ≤ 1) {a v : ℝ}
    (ha : 0 ≤ a) (hav : a ≤ v) (hv : v ≤ 3 / 2) :
    |leftStripExpMoment p 2 b a v / (compositionMarginalVariance p / 2) -
      wideJointPolynomial p b a v| ≤
      (2 : ℝ) ^ (b + 2) * (2 * v) ^ (15 - b) / ((15 - b).factorial : ℝ) := by
  let n := 15 - b
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
  rw [wideJointPolynomial_eq_average, leftStripExpMoment, jointAverage, div_div]
  change |(_ : ℝ) / _ - (_ : ℝ) / _| ≤ _
  rw [← sub_div, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  refine (abs_sum_map_sub_le _ _ _ _ hloc).trans_eq ?_
  change ((gaps p).map fun g ↦ x g ^ 2 * c).sum = _
  rw [List.sum_map_mul_right, show ((gaps p).map fun g ↦ x g ^ 2).sum = _ from
    sum_first_square_eq p]
  dsimp [c, n]
  rw [show b + 2 = (b + 1) + 1 by omega, pow_succ]
  ring

private theorem wideWeighted_error {b t : ℝ} (hb : |b| ≤ 2) (ht : |t| ≤ 3 / 2)
    {k n : ℕ} (hk : k ≤ 3) (hn : n + k = 15) :
    |(∫ s in (0 : ℝ)..1, (1 - s) * (b * s) ^ k * Real.exp (t * (b * s))) -
        scalarPolynomial b t k n| ≤ (2 : ℝ) ^ (k + 1) * 3 ^ n / (n.factorial * 16 * 17) := by
  let w (s : ℝ) := (1 - s) * (b * s) ^ k
  let z (s : ℝ) := t * (b * s)
  let pol (s : ℝ) := ∑ i ∈ Finset.range n, z s ^ i / (i.factorial : ℝ)
  have hpol : (∫ s in (0 : ℝ)..1, w s * pol s) = scalarPolynomial b t k n := by
    simp only [pol, scalarPolynomial, Finset.mul_sum]
    refine (intervalIntegral.integral_finsetSum (fun i _ ↦ ?_)).trans ?_
    · apply Continuous.intervalIntegrable
      dsimp only [w, z]
      fun_prop
    apply Finset.sum_congr rfl
    intro i _
    have heq (s : ℝ) :
        w s * (z s ^ i / (i.factorial : ℝ)) =
          (b ^ (k + i) * t ^ i / (i.factorial : ℝ)) * ((1 - s) * s ^ (k + i)) := by
      simp only [w, z, mul_pow, pow_add]
      ring
    simp_rw [heq]
    rw [intervalIntegral.integral_const_mul, unit_weight_moment]
    simp only [div_eq_mul_inv, one_mul, mul_inv_rev, mul_assoc]
    ac_rfl
  have hv : Continuous (fun s ↦ w s * Real.exp (z s)) := by
    dsimp only [w, z]
    fun_prop
  have hP : Continuous (fun s ↦ w s * pol s) := by
    dsimp only [w, pol, z]
    fun_prop
  let C : ℝ := (2 : ℝ) ^ (k + 1) * 3 ^ n / n.factorial
  have hC : Continuous (fun s : ℝ ↦ C * ((1 - s) * s ^ (n + k))) := by fun_prop
  have hbound (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
      ‖w s * Real.exp (z s) - w s * pol s‖ ≤ C * ((1 - s) * s ^ (n + k)) := by
    have hs₀ : 0 ≤ s := hs.1.le
    have hbs : |b * s| ≤ 2 * s := by
      rw [abs_mul, abs_of_nonneg hs₀]
      exact mul_le_mul_of_nonneg_right hb hs₀
    have hz : |z s| ≤ 3 * s := by
      rw [show z s = t * (b * s) from rfl, abs_mul]
      calc
        _ ≤ (3 / 2) * (2 * s) := mul_le_mul ht hbs (abs_nonneg _) (by norm_num)
        _ = _ := by ring
    have hratio : ‖(z s : ℂ)‖ / (n.succ : ℝ) ≤ 1 / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, Nat.cast_succ]
      have hnR : (12 : ℝ) ≤ n := by exact_mod_cast (show 12 ≤ n by omega)
      exact (div_le_iff₀ (by positivity)).2 (by linarith [hs.2])
    have htail : |Real.exp (z s) - pol s| ≤ |z s| ^ n / (n.factorial : ℝ) * 2 := by
      dsimp only [pol]
      exact_mod_cast Complex.exp_bound' hratio
    have htail' : |Real.exp (z s) - pol s| ≤ (3 * s) ^ n / (n.factorial : ℝ) * 2 :=
      htail.trans (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hz _) (by positivity))
        (by norm_num))
    rw [← mul_sub, Real.norm_eq_abs, abs_mul]
    dsimp only [w]
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hs.2), abs_pow, mul_assoc]
    calc
      _ ≤ (1 - s) * ((2 * s) ^ k * ((3 * s) ^ n / (n.factorial : ℝ) * 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hbs _) htail' (abs_nonneg _) (by positivity))
          (sub_nonneg.mpr hs.2)
      _ = _ := by simp only [C, mul_pow, pow_add, pow_one]; ring
  have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) zero_le_one
    (Filter.Eventually.of_forall hbound) (hC.intervalIntegrable 0 1)
  change |(∫ s in (0 : ℝ)..1, w s * Real.exp (z s)) - scalarPolynomial b t k n| ≤ _
  rw [← hpol, ← intervalIntegral.integral_sub (μ := volume) (hv.intervalIntegrable 0 1)
    (hP.intervalIntegrable 0 1)]
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul, unit_weight_moment, hn] at h
  refine h.trans_eq ?_
  norm_num [C, div_eq_mul_inv, mul_inv_rev]
  ring

private def wideMarginalPolynomial (p k : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (15 - k), marginalCoefficient p k i * t ^ i

private theorem wideMarginalPolynomial_eq_average {p : ℕ} (hp : 0 < p) (k : ℕ) (t : ℝ) :
    wideMarginalPolynomial p k t =
      ((gaps p).map fun g ↦ exponent p g.2.2 ^ 2 *
        scalarPolynomial (exponent p g.2.2) t k (15 - k)).sum / denominator p := by
  simp only [wideMarginalPolynomial, scalarPolynomial, Finset.mul_sum, list_sum_map_finsetSum,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  have hc := normalized_moment_eval_marginal (k := k + i) hp
  unfold marginalCoefficient
  rw [hc, ← marginal_power_sum_eq]
  simp_rw [show ∀ (x : ℝ), x ^ 2 * (x ^ (k + i) * t ^ i /
      ((i.factorial : ℝ) * (↑(k + i) + 1) * (↑(k + i) + 2))) =
      (x ^ 2 * x ^ (k + i)) * (t ^ i /
      ((i.factorial : ℝ) * (↑(k + i) + 1) * (↑(k + i) + 2))) by
    intro x
    ring]
  rw [List.sum_map_mul_right]
  push_cast
  field_simp [show (0 : ℝ) < (k + i).factorial by positivity,
    show (0 : ℝ) < (↑k + ↑i + 1 : ℝ) by positivity,
    show (0 : ℝ) < (↑k + ↑i + 2 : ℝ) by positivity, (denominator_pos p).ne']
  <;> ring

private def wideMarginalError (k : ℕ) : ℚ :=
  2 ^ (k + 2) * 3 ^ (15 - k) / ((Nat.factorial (15 - k) : ℚ) * 16 * 17)

private theorem wideMarginalTaylor_error {p k : ℕ} (hp : 0 < p) (hk : k ≤ 3)
    {t : ℝ} (ht : |t| ≤ 3 / 2) :
    |leftStripZ p k t - wideMarginalPolynomial p k t| ≤ (wideMarginalError k : ℝ) := by
  let n := 15 - k
  let ε : ℝ := (2 : ℝ) ^ (k + 1) * 3 ^ n / (n.factorial * 16 * 17)
  rw [wideMarginalPolynomial_eq_average hp]
  let f (g : Gap) := exponent p g.2.2 ^ 2 *
    (∫ s in (0 : ℝ)..1, (1 - s) * (exponent p g.2.2 * s) ^ k *
      Real.exp (t * (exponent p g.2.2 * s)))
  let pol (g : Gap) := exponent p g.2.2 ^ 2 * scalarPolynomial (exponent p g.2.2) t k n
  let weight (g : Gap) := exponent p g.2.2 ^ 2 * ε
  change |((gaps p).map f).sum / denominator p - ((gaps p).map pol).sum / denominator p| ≤ _
  have hden := denominator_pos p
  have hlocal (g : Gap) (hg : g ∈ gaps p) : |f g - pol g| ≤ weight g := by
    dsimp only [f, pol, weight]
    rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left
      (wideWeighted_error (exponent_abs_le hp hg) ht hk (n := n) (by dsimp only [n]; omega))
      (sq_nonneg _)
  rw [← sub_div, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  refine (abs_sum_map_sub_le (gaps p) f pol weight hlocal).trans_eq ?_
  dsimp only [weight]
  rw [List.sum_map_mul_right, sum_marginal_square]
  simp only [ε, n, wideMarginalError, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat,
    Rat.cast_natCast, show k + 2 = (k + 1) + 1 by omega, pow_succ]
  ring

private def wideZBox (H T : Interval) (k : ℕ) : Interval :=
  series (15-k) (fun i ↦ point ((k+i).factorial / (i.factorial : ℚ)) *
    momentBox H 0 (k+i+2)) T + box (-wideMarginalError k) (wideMarginalError k)

private theorem wideZBox_encloses {p : ℕ} (hp : 0 < p) {k : ℕ} (hk : k ≤ 3) {H T : Interval}
    {t : ℝ} (hh : H.encloses (3 / (p : ℝ))) (ht : T.encloses t)
    (htop : |t| ≤ 3 / 2) : (wideZBox H T k).encloses (leftStripZ p k t) := by
  have hz := abs_le.mp (wideMarginalTaylor_error hp hk htop)
  have hp' : (series (15-k) (fun i ↦ point ((k+i).factorial / (i.factorial : ℚ)) *
      momentBox H 0 (k+i+2)) T).encloses (wideMarginalPolynomial p k t) := by
    apply series_encloses _ ht
    intro i hi
    have h := RoundedInterval.encloses_mul
      (RoundedInterval.encloses_point ((k+i).factorial / (i.factorial : ℚ)))
      (momentBox_encloses 0 (k+i+2) hh)
    convert h using 2
    simp only [Rat.cast_div, Rat.cast_natCast, marginalCoefficient]
    ring
  convert RoundedInterval.encloses_add hp'
    (RoundedInterval.encloses_interval (x := leftStripZ p k t - wideMarginalPolynomial p k t)
      (lo := -wideMarginalError k) (hi := wideMarginalError k)
      (by simpa only [Rat.cast_neg] using hz.1) hz.2) using 1 <;> first | rfl | ring

private def wideJointBox (H A V : Interval) (b : ℕ) : Interval :=
  let error : ℚ := 2 ^ (b+2) * 3 ^ (15-b) / (Nat.factorial (15-b) : ℚ)
  series (15-b) (fun i ↦ series (15-b-i) (jointCoefficient H b i) V) A +
    box (-error) error

set_option maxHeartbeats 1000000 in
private theorem wideJointBox_encloses {p b : ℕ} (hp : 0 < p) (hb : b ≤ 1) {H A V : Interval}
    {a v : ℝ} (hh : H.encloses (3 / (p : ℝ))) (ha : A.encloses a) (hv : V.encloses v)
    (ha₀ : 0 ≤ a) (hav : a ≤ v) (hvtop : v ≤ 3/2) :
    (wideJointBox H A V b).encloses (leftStripExpMoment p 2 b a v / (compositionMarginalVariance p / 2)) := by
  let error (b : ℕ) : ℚ := 2 ^ (b+2) * 3 ^ (15-b) / (Nat.factorial (15-b) : ℚ)
  have hpoly :
      (series (15-b) (fun i ↦ series (15-b-i) (jointCoefficient H b i) V) A).encloses
        (wideJointPolynomial p b a v) := by
    unfold wideJointPolynomial
    rw [sum_triangle (11 - b) (fun i j ↦
      jointTaylorMoment p i (b+j) * (a^i * v^j / ((i.factorial : ℝ) * (j.factorial : ℝ))))]
    have hrow (i : ℕ) (hi : i < 15-b) :=
      series_encloses (15-b-i) hv (fun j hj ↦ jointCoefficient_encloses (i := i) (j := j) hp hb hh)
    convert series_encloses (15-b) ha hrow using 2
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hf : (2 : ℝ) ^ (b+2) * (2*v) ^ (15-b) / ((15-b).factorial : ℝ) ≤ (error b : ℝ) := by
    calc
      _ ≤ (2 : ℝ) ^ (b+2) * 3 ^ (15-b) / ((15-b).factorial : ℝ) := by
        gcongr
        · linarith [ha₀.trans hav]
        · linarith
      _ ≤ _ := by interval_cases b <;> norm_num [error, Nat.factorial]
  have he := abs_le.mp ((wideJointTaylor_error hp hb ha₀ hav hvtop).trans hf)
  convert RoundedInterval.encloses_add hpoly
    (RoundedInterval.encloses_interval (lo := -error b) (hi := error b)
      (by simpa only [Rat.cast_neg] using he.1) he.2) using 1 <;> first | rfl | ring

private def wideIntegrandBox (H A D V Zd Zv Zn : Interval) : Interval :=
  let r := sqrtBox Zd
  let q := reciprocalBox (point 2 * r)
  let r1 := wideZBox H D 1 * q
  let r2 := (wideZBox H D 2 - point 2 * (r1 * r1)) * q
  let r3 := (wideZBox H D 3 - point 6 * (r1 * r2)) * q
  let b := wideZBox H (0 - V) 1 * reciprocalBox (point 2 * Zn)
  let s := wideZBox H V 1 * reciprocalBox (point 2 * Zv)
  let rad := V * sqrtBox Zv * (point 3 * r2 + D * r3 +
    (s + b) * (point 2 * r1 + D * r2))
  V * (rad - wideJointBox H A V 1) + (point 1 - V * b) * wideJointBox H A V 0

set_option maxHeartbeats 1000000 in
private theorem wideIntegrandBox_sound {p : ℕ} (hp : 0 < p) {a v : ℝ} {H A D V : Interval}
    (hh : H.encloses (3 / (p : ℝ))) (ha : A.encloses a) (hd : D.encloses (v-a))
    (hv : V.encloses v) (ha₀ : 0 ≤ a) (hd₀ : 0 ≤ v-a)
    (hd₁ : v-a ≤ 3/2) (hv₁ : v ≤ 3/2)
    (hZd : validZ (wideZBox H D 0)) (hZv : validZ (wideZBox H V 0)) (hZn : validZ (wideZBox H (0-V) 0))
    (hcheck : 0 < (wideIntegrandBox H A D V (wideZBox H D 0) (wideZBox H V 0) (wideZBox H (0-V) 0)).lower) :
    0 < leftStripRegularizedIntegrand p a v := by
  let d := v-a
  let c := compositionMarginalVariance p / 2
  have hc : 0 < c := half_pos (compositionMarginalVariance_pos p)
  have hav : a ≤ v := by linarith
  have hv₀ := ha₀.trans hav
  have hAbsD : |d| ≤ 3/2 := by rwa [abs_of_nonneg hd₀]
  have hAbsV : |v| ≤ 3/2 := by rwa [abs_of_nonneg hv₀]
  have hNegV : (0 - V).encloses (-v) := by
    change (point 0 - V).encloses (-v)
    simpa only [Rat.cast_zero, zero_sub] using
      RoundedInterval.encloses_sub (RoundedInterval.encloses_point 0) hv
  have zd (k : ℕ) (hk : k ≤ 3) :
      (wideZBox H D k).encloses (leftStripZ p k d) :=
    wideZBox_encloses hp hk hh hd hAbsD
  have zv (k : ℕ) (hk : k ≤ 1) :
      (wideZBox H V k).encloses (leftStripZ p k v) :=
    wideZBox_encloses hp (by omega) hh hv hAbsV
  have zn (k : ℕ) (hk : k ≤ 1) :
      (wideZBox H (0-V) k).encloses (leftStripZ p k (-v)) :=
    wideZBox_encloses hp (by omega) hh hNegV (by simpa only [abs_neg] using hAbsV)
  have hdZ := validZ_bounds hZd (zd 0 (by decide))
  have hvZ := validZ_bounds hZv (zv 0 (by decide))
  have hnZ := validZ_bounds hZn (zn 0 (by decide))
  have rd : (sqrtBox (wideZBox H D 0)).encloses (leftStripRoot p d) :=
    sqrtBox_encloses (zd 0 (by decide)) hdZ.1 hdZ.2
  have rv : (sqrtBox (wideZBox H V 0)).encloses (leftStripRoot p v) :=
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
  have J (k : ℕ) (hk : k ≤ 1) := wideJointBox_encloses hp hk hh ha hv ha₀ hav hv₁
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

-- Intersect the sum interval with the range still needed after the low-strip result.
private def wideRange (V : Interval) : Interval :=
  box (max V.lower 1) (min V.upper (3 / 2))

private def wideCheckBox (H A D : Interval) : Bool :=
  if (A + D).upper < 1 ∨ 3 / 2 < (A + D).lower then true else
    let V := wideRange (A + D)
    let Zd := wideZBox H D 0
    let Zv := wideZBox H V 0
    let Zn := wideZBox H (0 - V) 0
    decide (validZ Zd ∧ validZ Zv ∧ validZ Zn ∧ 0 < (wideIntegrandBox H A D V Zd Zv Zn).lower)

private theorem wideCheckBox_sound {p : ℕ} (hp : 0 < p) {a v : ℝ} {H A D : Interval}
    (hh : H.encloses (3 / (p : ℝ))) (ha : A.encloses a) (hd : D.encloses (v-a))
    (ha₀ : 0 ≤ a) (hd₀ : 0 ≤ v-a) (hv₀ : 1 ≤ v) (hv₁ : v ≤ 3/2)
    (hc : wideCheckBox H A D = true) : 0 < leftStripRegularizedIntegrand p a v := by
  have hV : (A + D).encloses v := by
    convert RoundedInterval.encloses_add ha hd using 1
    ring
  unfold wideCheckBox at hc
  split at hc
  · rename_i h
    rcases h with h | h
    · exact False.elim ((show (((A + D).upper : ℚ) : ℝ) < 1 by exact_mod_cast h).not_ge
        (hv₀.trans hV.2))
    · exact False.elim ((show (3 / 2 : ℝ) < (A + D).lower by exact_mod_cast h).not_ge
        (hV.1.trans hv₁))
  · have hv : (wideRange (A + D)).encloses v := by
      apply RoundedInterval.encloses_interval
      · rw [Rat.cast_max, Rat.cast_one]
        exact max_le hV.1 hv₀
      · rw [Rat.cast_min, Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofNat]
        exact le_min hV.2 hv₁
    obtain ⟨hZd, hZv, hZn, hpos⟩ := of_decide_eq_true hc
    exact wideIntegrandBox_sound hp hh ha hd hv ha₀ hd₀ (by linarith) hv₁ hZd hZv hZn hpos

private def wideCheckCover (depth : ℕ) (H A D : Endpoints) : Bool :=
  if wideCheckBox (intervalOf H) (intervalOf A) (intervalOf D) then true else
    match depth with
    | 0 => false
    | n + 1 =>
      if (n+1) % 3 = 0 then
        wideCheckCover n H (lowerHalf A) D && wideCheckCover n H (upperHalf A) D
      else if (n+1) % 3 = 2 then
        wideCheckCover n H A (lowerHalf D) && wideCheckCover n H A (upperHalf D)
      else
        wideCheckCover n (lowerHalf H) A D && wideCheckCover n (upperHalf H) A D

private theorem wideCheckCover_sound {p : ℕ} (hp : 0 < p) {a v : ℝ}
    (ha₀ : 0 ≤ a) (hd₀ : 0 ≤ v-a) (hv₀ : 1 ≤ v) (hv₁ : v ≤ 3/2)
    (n : ℕ) (H A D : Endpoints) (hh : InInterval H (3 / (p : ℝ)))
    (ha : InInterval A a) (hd : InInterval D (v-a))
    (hc : wideCheckCover n H A D = true) : 0 < leftStripRegularizedIntegrand p a v := by
  have localSound {H A D : Endpoints} (hh : InInterval H (3 / (p : ℝ)))
      (ha : InInterval A a) (hd : InInterval D (v-a))
      (hb : wideCheckBox (intervalOf H) (intervalOf A) (intervalOf D) = true) :
      0 < leftStripRegularizedIntegrand p a v :=
    wideCheckBox_sound hp (RoundedInterval.encloses_interval hh.1 hh.2)
      (RoundedInterval.encloses_interval ha.1 ha.2)
      (RoundedInterval.encloses_interval hd.1 hd.2) ha₀ hd₀ hv₀ hv₁ hb
  induction n generalizing H A D with
  | zero =>
    rw [wideCheckCover] at hc
    split at hc
    · exact localSound hh ha hd (by assumption)
    · contradiction
  | succ n ih =>
    rw [wideCheckCover] at hc
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

end

end RefinedBMV.PositiveCenter
