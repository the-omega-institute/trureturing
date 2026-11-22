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

-- The original replay uses cutoff 11. The larger arguments need four more terms.
private def taylorCutoff (wide : Bool) : ℕ := if wide then 15 else 11

private def marginalLimit (wide : Bool) (k : ℕ) : ℚ :=
  if k ≤ 1 then (if wide then 2 else 3/2) else (if wide then 3/2 else 1)

private def marginalError (wide : Bool) (k : ℕ) : ℚ :=
  if wide then
    match k with
    | 0 => 1/100000
    | 1 => 1/16000
    | 2 => 1/100000
    | _ => 1/12000
  else 1/500

private def jointLimit (wide : Bool) : ℚ := if wide then 2 else 3/2

private def jointError (wide : Bool) (b : ℕ) : ℚ :=
  if wide then
    2 ^ (b+2) * 4 ^ (taylorCutoff wide-b) / (Nat.factorial (taylorCutoff wide-b) : ℚ)
  else if b = 0 then 1/50 else 2/15

private def jointPolynomial (wide : Bool) (p b : ℕ) (a v : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (taylorCutoff wide - b), ∑ i ∈ Finset.range (m + 1),
    jointTaylorMoment p i (b + (m - i)) *
      (a ^ i * v ^ (m - i) / ((i.factorial : ℝ) * ((m - i).factorial : ℝ)))

private theorem jointPolynomial_eq_average (wide : Bool) (p b : ℕ) (a v : ℝ) :
    jointPolynomial wide p b a v =
      jointAverage p (fun x y ↦ y ^ b *
        ∑ m ∈ Finset.range (taylorCutoff wide - b), (x * a + y * v) ^ m / (m.factorial : ℝ)) := by
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

private theorem jointTaylor_error (wide : Bool) {p b : ℕ} (hp : 0 < p) (hb : b ≤ 1) {a v : ℝ}
    (ha : 0 ≤ a) (hav : a ≤ v) (hv : v ≤ (jointLimit wide : ℝ)) :
    |leftStripExpMoment p 2 b a v / (compositionMarginalVariance p / 2) -
      jointPolynomial wide p b a v| ≤
      (2 : ℝ) ^ (b + 2) * (2 * v) ^ (taylorCutoff wide - b) / ((taylorCutoff wide - b).factorial : ℝ) := by
  let n := taylorCutoff wide - b
  let c : ℝ := (2 : ℝ) ^ (b + 1) * (2 * v) ^ n / (n.factorial : ℝ)
  let x := leftStripX p
  let y := leftStripY p
  have hden : 0 < ((gaps p).length : ℝ) * (compositionMarginalVariance p / 2) :=
    mul_pos (by exact_mod_cast (word_counts_all p).2.1)
      (half_pos (compositionMarginalVariance_pos p))
  have hn : 10 ≤ n := by cases wide <;> simp [n, taylorCutoff] <;> omega
  have hv₂ : v ≤ 2 := hv.trans (by cases wide <;> norm_num [jointLimit])
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

private def marginalPolynomial (wide : Bool) (p k : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (taylorCutoff wide - k), marginalCoefficient p k i * x ^ i

private def marginalLongError (wide : Bool) : ℚ :=
  if wide then 1/10000000 else 1/1000

set_option maxHeartbeats 1000000 in
private theorem marginalTaylor_error (wide : Bool) {p k : ℕ} (hp : 0 < p) (hk : k ≤ 3)
    {t : ℝ} (ht : |t| ≤ (marginalLimit wide k : ℝ)) :
    |leftStripZ p k t - marginalPolynomial wide p k t| ≤ (marginalError wide k : ℝ) := by
  have hlong : |leftStripZ p k t - marginalTaylorPolynomial p k t| ≤
      (marginalLongError wide : ℝ) := by
    cases wide
    · by_cases hk₁ : k ≤ 1
      · have ht' : |t| ≤ 2 := ht.trans (by norm_num [marginalLimit, hk₁])
        have h := iteratedDeriv_compactZ_sub_taylor_le_two hp (show k ≤ 2 by omega) ht'
        rw [iteratedDeriv_compactZ_eq_integral hp, compactKappa, ← joint_normalization_eq hp] at h
        refine h.trans ?_
        interval_cases k <;> norm_num [marginalLongError, Nat.factorial]
      · have ht' : |t| ≤ 1 := by simpa [marginalLimit, hk₁] using ht
        exact (integralMarginalDerivative_sub_taylor_le hp (show k ≤ 4 by omega) ht').trans
          (by norm_num [marginalLongError])
    · have ht' : |t| ≤ 2 := ht.trans (by unfold marginalLimit; split <;> norm_num)
      have h := iteratedDeriv_compactZ_sub_taylor_le_two_of_le_three hp hk ht'
      rw [iteratedDeriv_compactZ_eq_integral hp, compactKappa, ← joint_normalization_eq hp] at h
      refine h.trans ?_
      interval_cases k <;> norm_num [marginalLongError, Nat.factorial]
  have hcut : 23 - k = (taylorCutoff wide - k) + (23 - taylorCutoff wide) := by
    cases wide <;> simp [taylorCutoff] <;> omega
  have hshort : |marginalTaylorPolynomial p k t - marginalPolynomial wide p k t| ≤
      (marginalError wide k : ℝ) - (marginalLongError wide : ℝ) := by
    rw [marginalTaylor_eq_coefficients hp, marginalPolynomial, hcut, Finset.sum_range_add,
      add_sub_cancel_left]
    let bound (wide : Bool) (k i : ℕ) : ℝ :=
      (2 : ℝ) ^ (k + (taylorCutoff wide - k + i) + 1) *
        (marginalLimit wide k : ℝ) ^ (taylorCutoff wide - k + i) /
        (((taylorCutoff wide - k + i).factorial : ℝ) *
          ((k + (taylorCutoff wide - k + i) : ℕ) + 1 : ℝ) *
          ((k + (taylorCutoff wide - k + i) : ℕ) + 2 : ℝ))
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ i ∈ Finset.range (23 - taylorCutoff wide), bound wide k i := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        rw [abs_mul, abs_pow]
        dsimp only [bound]
        rw [mul_div_right_comm]
        gcongr
        exact marginalCoefficient_abs_le hp k (taylorCutoff wide - k + i)
      _ ≤ _ := by
        cases wide <;> interval_cases k <;>
          norm_num [bound, taylorCutoff, marginalLimit, marginalLongError, marginalError,
            Finset.sum_range_succ, Nat.factorial]
  calc
    _ ≤ |leftStripZ p k t - marginalTaylorPolynomial p k t| +
        |marginalTaylorPolynomial p k t - marginalPolynomial wide p k t| := by
      simpa only [sub_add_sub_cancel] using
        abs_add_le (leftStripZ p k t - marginalTaylorPolynomial p k t)
          (marginalTaylorPolynomial p k t - marginalPolynomial wide p k t)
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

-- These are the additional diagonals of the same normalized moment table.
private def extraNumerators : Array (Array (List ℤ)) :=
  #[
    #[
      [181131581030400, 996223695667200, 1749294683136000, 400148356608000, -1603283499417600, -505285375795200, 1171526785228800, 144591422976000, -511711661260800, 62768369664000, 74873698099200, -18307441152000, 0, 0],
      [],
      [45662264524800, 251142454886400, 438890006016000, 91436615424000, -413081399808000, -114491920435200, 312833070950400, 25952306688000, -140852336486400, 21279167078400, 20986018099200, -5440500172800, 0, 0],
      [-23210501529600, -127657758412800, -221011338240000, -37117833984000, 218801224857600, 45416536704000, -176367910118400, -2780604288000, 83350589414400, -16226658201600, -12760602624000, 3583889971200, 0, 0],
      [11600547840000, 63803013120000, 109173173760000, 12756683520000, -114821908992000, -14786779392000, 98890751232000, -5055644160000, -48935238912000, 11459460096000, 7673605632000, -2297901312000, 0, 0],
      [-5411498803200, -29763243417600, -50355260928000, -3374348544000, 55993022668800, 3379835289600, -50907593318400, 5224165632000, 26063086694400, -6834917376000, -4155817881600, 1297223424000, 0, 0],
      [1545694617600, 8501320396800, 14260313088000, 411505920000, -16514320435200, -211239705600, 15564721536000, -2106518400000, -8138019456000, 2271512678400, 1310548377600, -418821580800, 0, 0],
      [1545694617600, 8501320396800, 14260313088000, 411505920000, -16514320435200, -211239705600, 15564721536000, -2106518400000, -8138019456000, 2271512678400, 1310548377600, -418821580800, 0, 0],
      [-5411498803200, -29763243417600, -50355260928000, -3374348544000, 55993022668800, 3379835289600, -50907593318400, 5224165632000, 26063086694400, -6834917376000, -4155817881600, 1297223424000, 0, 0],
      [11600547840000, 63803013120000, 109173173760000, 12756683520000, -114821908992000, -14786779392000, 98890751232000, -5055644160000, -48935238912000, 11459460096000, 7673605632000, -2297901312000, 0, 0],
      [-23210501529600, -127657758412800, -221011338240000, -37117833984000, 218801224857600, 45416536704000, -176367910118400, -2780604288000, 83350589414400, -16226658201600, -12760602624000, 3583889971200, 0, 0],
      [45662264524800, 251142454886400, 438890006016000, 91436615424000, -413081399808000, -114491920435200, 312833070950400, 25952306688000, -140852336486400, 21279167078400, 20986018099200, -5440500172800, 0, 0],
      [-90565790515200, -498111847833600, -874647341568000, -200074178304000, 801641749708800, 252642687897600, -585763392614400, -72295711488000, 255855830630400, -31384184832000, -37436849049600, 9153720576000, 0, 0],
      [181131581030400, 996223695667200, 1749294683136000, 400148356608000, -1603283499417600, -505285375795200, 1171526785228800, 144591422976000, -511711661260800, 62768369664000, 74873698099200, -18307441152000, 0, 0]
    ],
    #[
      [5082145663795200, 30492873982771200, 59841271358668800, 19688345284608000, -61707584216678400, -29538794763878400, 54991368662630400, 15629324046336000, -33363480755404800, 1096354190131200, 9302272384204800, -3222109642752000, 292919058432000, 0, 0],
      [],
      [1287487324569600, 7724923947417600, 15082181594726400, 4599105122304000, -16049182360780800, -6817196755353600, 14982809838796800, 3150696252211200, -9516604524134400, 1051105782988800, 2724699053260800, -1197243423129600, 146459529216000, 0, 0],
      [-660694570905600, -3964167425433600, -7662954552422400, -1976571362304000, 8646877487001600, 2841096442060800, -8726372592537600, -818713366732800, 5934036597350400, -1302570126950400, -1761480483840000, 990337724006400, -146459529216000, 0, 0],
      [347868031795200, 2087208190771200, 3971151791308800, 723017207808000, -4887749744640000, -929812126924800, 5457179879424000, -296735743180800, -4021211813068800, 1400965764710400, 1241779075891200, -875626072473600, 146459529216000, 0, 0],
      [-192024599961600, -1152147599769600, -2143061170790400, -153952856064000, 2950210567987200, 50935810867200, -3681609432883200, 803917965312000, 2943258600038400, -1422827049369600, -943836248678400, 807011444736000, -146459529216000, 0, 0],
      [121462961356800, 728777768140800, 1320746408755200, -76730830848000, -2041401703219200, 311333621760000, 2806180883251200, -1009949965516800, -2394350983987200, 1419509919744000, 789938782617600, -770364164505600, 146459529216000, 0, 0],
      [-100332458956800, -601994753740800, -1075239364147200, 142088421888000, 1764894023424000, -414896728780800, -2534154045696000, 1068390076723200, 2221575977779200, -1416692345241600, -741230067916800, 758619393638400, -146459529216000, 0, 0],
      [121462961356800, 728777768140800, 1320746408755200, -76730830848000, -2041401703219200, 311333621760000, 2806180883251200, -1009949965516800, -2394350983987200, 1419509919744000, 789938782617600, -770364164505600, 146459529216000, 0, 0],
      [-192024599961600, -1152147599769600, -2143061170790400, -153952856064000, 2950210567987200, 50935810867200, -3681609432883200, 803917965312000, 2943258600038400, -1422827049369600, -943836248678400, 807011444736000, -146459529216000, 0, 0],
      [347868031795200, 2087208190771200, 3971151791308800, 723017207808000, -4887749744640000, -929812126924800, 5457179879424000, -296735743180800, -4021211813068800, 1400965764710400, 1241779075891200, -875626072473600, 146459529216000, 0, 0],
      [-660694570905600, -3964167425433600, -7662954552422400, -1976571362304000, 8646877487001600, 2841096442060800, -8726372592537600, -818713366732800, 5934036597350400, -1302570126950400, -1761480483840000, 990337724006400, -146459529216000, 0, 0],
      [1287487324569600, 7724923947417600, 15082181594726400, 4599105122304000, -16049182360780800, -6817196755353600, 14982809838796800, 3150696252211200, -9516604524134400, 1051105782988800, 2724699053260800, -1197243423129600, 146459529216000, 0, 0],
      [-2541072831897600, -15246436991385600, -29920635679334400, -9844172642304000, 30853792108339200, 14769397381939200, -27495684331315200, -7814662023168000, 16681740377702400, -548177095065600, -4651136192102400, 1611054821376000, -146459529216000, 0, 0],
      [5082145663795200, 30492873982771200, 59841271358668800, 19688345284608000, -61707584216678400, -29538794763878400, 54991368662630400, 15629324046336000, -33363480755404800, 1096354190131200, 9302272384204800, -3222109642752000, 292919058432000, 0, 0]
    ],
    #[
      [152296987594752000, 989930419365888000, 2149356359614464000, 932225364854784000, -2441271124131840000, -1643558375467008000, 2543374338785280000, 1318857599195136000, -1973207391547392000, -392406924349440000, 879175631093760000, -85009295314944000, -129143828304691200, 30271092409958400, 0, 0],
      [],
      [38389433783500800, 249531319592755200, 539882105566003200, 224507065092710400, -628948628737228800, -396805044232396800, 680272830126489600, 314572203135590400, -546244725970944000, -83189311491686400, 249718877459251200, -31305574921420800, -37238381442662400, 9260426804428800, 0, 0],
      [-19509903776563200, -126814374547660800, -272484068445388800, -103704256425369600, 333105162072883200, 184317972481843200, -384565660493414400, -142143904904601600, 326065241069568000, 26682236150169600, -154784408415436800, 25706038553395200, 23571615087820800, -6322867104153600, 0, 0],
      [9927633881088000, 64529620227072000, 137344550289408000, 45569204093952000, -178815543150182400, -81700241133772800, 222631819812864000, 59811944964710400, -199688417239449600, -2492088212275200, 98275723628544000, -20015821434470400, -15256484528947200, 4358332094054400, 0, 0],
      [-4993994041344000, -32460961268736000, -68334291615744000, -18768029930496000, 95302848098304000, 34017179986944000, -127584643608576000, -22528154170368000, 120212923944960000, -5539596023808000, -60979930970112000, 14280263940096000, 9617171868057600, -2880309429043200, 0, 0],
      [2310275229696000, 15016788993024000, 31286196781056000, 6889403372544000, -46383383841177600, -12618734194483200, 65775921426432000, 6959616994713600, -64302856689254400, 5730104191795200, 33359590914048000, -8548259766681600, -5323079636582400, 1646872296652800, 0, 0],
      [-677122932326400, -4401299060121600, -9116717963673600, -1727659138867200, 13965303840768000, 3179876332953600, -20381548039372800, -1439875674316800, 20290263223910400, -2238080108544000, -10645983697305600, 2844255762432000, 1708909100236800, -537057290649600, 0, 0],
      [-677122932326400, -4401299060121600, -9116717963673600, -1727659138867200, 13965303840768000, 3179876332953600, -20381548039372800, -1439875674316800, 20290263223910400, -2238080108544000, -10645983697305600, 2844255762432000, 1708909100236800, -537057290649600, 0, 0],
      [2310275229696000, 15016788993024000, 31286196781056000, 6889403372544000, -46383383841177600, -12618734194483200, 65775921426432000, 6959616994713600, -64302856689254400, 5730104191795200, 33359590914048000, -8548259766681600, -5323079636582400, 1646872296652800, 0, 0],
      [-4993994041344000, -32460961268736000, -68334291615744000, -18768029930496000, 95302848098304000, 34017179986944000, -127584643608576000, -22528154170368000, 120212923944960000, -5539596023808000, -60979930970112000, 14280263940096000, 9617171868057600, -2880309429043200, 0, 0],
      [9927633881088000, 64529620227072000, 137344550289408000, 45569204093952000, -178815543150182400, -81700241133772800, 222631819812864000, 59811944964710400, -199688417239449600, -2492088212275200, 98275723628544000, -20015821434470400, -15256484528947200, 4358332094054400, 0, 0],
      [-19509903776563200, -126814374547660800, -272484068445388800, -103704256425369600, 333105162072883200, 184317972481843200, -384565660493414400, -142143904904601600, 326065241069568000, 26682236150169600, -154784408415436800, 25706038553395200, 23571615087820800, -6322867104153600, 0, 0],
      [38389433783500800, 249531319592755200, 539882105566003200, 224507065092710400, -628948628737228800, -396805044232396800, 680272830126489600, 314572203135590400, -546244725970944000, -83189311491686400, 249718877459251200, -31305574921420800, -37238381442662400, 9260426804428800, 0, 0],
      [-76148493797376000, -494965209682944000, -1074678179807232000, -466112682427392000, 1220635562065920000, 821779187733504000, -1271687169392640000, -659428799597568000, 986603695773696000, 196203462174720000, -439587815546880000, 42504647657472000, 64571914152345600, -15135546204979200, 0, 0],
      [152296987594752000, 989930419365888000, 2149356359614464000, 932225364854784000, -2441271124131840000, -1643558375467008000, 2543374338785280000, 1318857599195136000, -1973207391547392000, -392406924349440000, 879175631093760000, -85009295314944000, -129143828304691200, 30271092409958400, 0, 0]
    ],
    #[
      [4876349102456832000, 34134443717197824000, 81199422658658304000, 43448767628378112000, -100570745830883328000, -87596523821334528000, 120442207372591104000, 90648573027876864000, -115595083223049830400, -45529463760696115200, 72184880480993280000, 590524821798912000, -20302152986994278400, 6538555960551014400, -544879663379251200, 0, 0],
      [],
      [1230046632957542400, 8610326430702796800, 20414627628595200000, 10553522172434841600, -25958593664472268800, -21320808304597401600, 32413994088892416000, 21876233054080204800, -32457906840309350400, -10193671109151129600, 21024453724065792000, -1310452914497126400, -6036270912825753600, 2415201327931392000, -272439831689625600, 0, 0],
      [-625982673822105600, -4381878716754739200, -10322085778228224000, -4968091351557734400, 13795204038987571200, 10082081501562470400, -18510439290190848000, -10152206324151091200, 19788089454701568000, 3908140723552665600, -13490460465850368000, 2113310577195417600, 3978868122490060800, -1988163001759334400, 272439831689625600, 0, 0],
      [322562926986854400, 2257940488907980800, 5265819938598912000, 2241693275789721600, -7565548435122585600, -4562348884711833600, 11141442589726310400, 4345492582622822400, -12874079200528465920, -786306016089538560, 9309819487430246400, -2468142792002764800, -2829220611339386880, 1742468041235496960, -272439831689625600, 0, 0],
      [-169465286301696000, -1186257004111872000, -2727692104338432000, -944811572576256000, 4302759842067456000, 1902113360953344000, -7039724938380288000, -1497435335294976000, 8837972512072704000, -753680852305920000, -6805854648907776000, 2598962282864640000, 2133450739781222400, -1587444763535769600, 272439831689625600, 0, 0],
      [93648965308416000, 655542757158912000, 1478961400154112000, 351712557858816000, -2612468424480768000, -662604857155584000, 4769305548908544000, 138085396807680000, -6497786437141708800, 1494347545364889600, 5319801990623232000, -2633673253994496000, -1716744156232089600, 1491308741099520000, -272439831689625600, 0, 0],
      [-58593570777907200, -410154995445350400, -905257388399616000, -99529389608140800, 1797489264691814400, 124438336752844800, -3612194027688960000, 467531825519001600, 5262529499639193600, -1826957894952960000, -4522279532746752000, 2636227807499059200, 1491693684900249600, -1438167760146432000, 272439831689625600, 0, 0],
      [48647505611980800, 340532539283865600, 743278452940800000, 32747706954547200, -1559028826556006400, 20694073068748800, 3260680206026342400, -634405442833612800, -4878919638381035520, 1919196400441098240, 4272123569636966400, -2634033987138355200, -1420839107589242880, 1421210871913512960, -272439831689625600, 0, 0],
      [-58593570777907200, -410154995445350400, -905257388399616000, -99529389608140800, 1797489264691814400, 124438336752844800, -3612194027688960000, 467531825519001600, 5262529499639193600, -1826957894952960000, -4522279532746752000, 2636227807499059200, 1491693684900249600, -1438167760146432000, 272439831689625600, 0, 0],
      [93648965308416000, 655542757158912000, 1478961400154112000, 351712557858816000, -2612468424480768000, -662604857155584000, 4769305548908544000, 138085396807680000, -6497786437141708800, 1494347545364889600, 5319801990623232000, -2633673253994496000, -1716744156232089600, 1491308741099520000, -272439831689625600, 0, 0],
      [-169465286301696000, -1186257004111872000, -2727692104338432000, -944811572576256000, 4302759842067456000, 1902113360953344000, -7039724938380288000, -1497435335294976000, 8837972512072704000, -753680852305920000, -6805854648907776000, 2598962282864640000, 2133450739781222400, -1587444763535769600, 272439831689625600, 0, 0],
      [322562926986854400, 2257940488907980800, 5265819938598912000, 2241693275789721600, -7565548435122585600, -4562348884711833600, 11141442589726310400, 4345492582622822400, -12874079200528465920, -786306016089538560, 9309819487430246400, -2468142792002764800, -2829220611339386880, 1742468041235496960, -272439831689625600, 0, 0],
      [-625982673822105600, -4381878716754739200, -10322085778228224000, -4968091351557734400, 13795204038987571200, 10082081501562470400, -18510439290190848000, -10152206324151091200, 19788089454701568000, 3908140723552665600, -13490460465850368000, 2113310577195417600, 3978868122490060800, -1988163001759334400, 272439831689625600, 0, 0],
      [1230046632957542400, 8610326430702796800, 20414627628595200000, 10553522172434841600, -25958593664472268800, -21320808304597401600, 32413994088892416000, 21876233054080204800, -32457906840309350400, -10193671109151129600, 21024453724065792000, -1310452914497126400, -6036270912825753600, 2415201327931392000, -272439831689625600, 0, 0],
      [-2438174551228416000, -17067221858598912000, -40599711329329152000, -21724383814189056000, 50285372915441664000, 43798261910667264000, -60221103686295552000, -45324286513938432000, 57797541611524915200, 22764731880348057600, -36092440240496640000, -295262410899456000, 10151076493497139200, -3269277980275507200, 272439831689625600, 0, 0],
      [4876349102456832000, 34134443717197824000, 81199422658658304000, 43448767628378112000, -100570745830883328000, -87596523821334528000, 120442207372591104000, 90648573027876864000, -115595083223049830400, -45529463760696115200, 72184880480993280000, 590524821798912000, -20302152986994278400, 6538555960551014400, -544879663379251200, 0, 0]
    ]
  ]

private def localMomentNumerators (a b : ℕ) : List ℤ :=
  if a+b ≤ 12 then stagedNumerators a b else (extraNumerators.getD (a+b-13) #[]).getD a []

private def checkExtraDiagonal (n : ℕ) : Bool :=
  (List.range (n+1)).all fun a ↦
    if a = 1 then true else
      decide (localMomentNumerators a (n-a) = certifiedMomentNumerators a (n-a))

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private theorem extraDiagonals_checked (n : Fin 4) :
    checkExtraDiagonal (13+n.val) = true := by
  fin_cases n <;> decide +kernel

private theorem localMomentNumerators_eq {a b : ℕ}
    (hdegree : a+b ≤ 16) (hlow : 2 ≤ a+b) (ha : a = 0 ∨ 2 ≤ a) :
    localMomentNumerators a b = certifiedMomentNumerators a b := by
  by_cases h : a+b ≤ 12
  · simpa only [localMomentNumerators, if_pos h] using stagedNumerators_eq h hlow ha
  · have hn : 13 + (a+b-13) = a+b := by omega
    have hc := extraDiagonals_checked ⟨a+b-13, by omega⟩
    change checkExtraDiagonal (13+(a+b-13)) = true at hc
    rw [hn] at hc
    have he := List.all_eq_true.mp hc a (List.mem_range.mpr (by omega))
    simpa [show a ≠ 1 by omega, show a+b-a = b by omega] using he

private def momentBox (H : Interval) (a b : ℕ) : Interval :=
  ⟨dyadicHorner H.endpoints (certifiedMomentDenominator a b) (localMomentNumerators a b)⟩

private theorem momentBox_encloses (a b : ℕ) {H : Interval} {h : ℝ}
    (hh : H.encloses h) (hdegree : a+b ≤ 16) (hlow : 2 ≤ a+b) (ha : a = 0 ∨ 2 ≤ a) :
    (momentBox H a b).encloses (momentHorner h (normalizedMomentCoeffs a b)) := by
  rw [← certifiedMomentCoeffs_eq, certifiedMomentCoeffs, ← localMomentNumerators_eq hdegree hlow ha]
  exact dyadicHorner_encloses hh _ _

private def zBox (wide : Bool) (H T : Interval) (k : ℕ) : Interval :=
  series (taylorCutoff wide-k) (fun i ↦ point ((k+i).factorial / (i.factorial : ℚ)) *
    momentBox H 0 (k+i+2)) T + box (-marginalError wide k) (marginalError wide k)

private theorem zBox_encloses (wide : Bool) {p : ℕ} (hp : 0 < p) {k : ℕ} (hk : k ≤ 3) {H T : Interval}
    {t : ℝ} (hh : H.encloses (3 / (p : ℝ))) (ht : T.encloses t)
    (htop : |t| ≤ (marginalLimit wide k : ℝ)) : (zBox wide H T k).encloses (leftStripZ p k t) := by
  have hz := abs_le.mp (marginalTaylor_error wide hp hk htop)
  have hp' : (series (taylorCutoff wide-k) (fun i ↦ point ((k+i).factorial / (i.factorial : ℚ)) *
      momentBox H 0 (k+i+2)) T).encloses (marginalPolynomial wide p k t) := by
    apply series_encloses _ ht
    intro i hi
    have h := RoundedInterval.encloses_mul
      (RoundedInterval.encloses_point ((k+i).factorial / (i.factorial : ℚ)))
      (momentBox_encloses 0 (k+i+2) hh (by cases wide <;> simp [taylorCutoff] at hi <;> omega) (by omega) (Or.inl rfl))
    convert h using 2
    simp only [Rat.cast_div, Rat.cast_natCast, marginalCoefficient]
    ring
  convert RoundedInterval.encloses_add hp'
    (RoundedInterval.encloses_interval (x := leftStripZ p k t - marginalPolynomial wide p k t)
      (lo := -marginalError wide k) (hi := marginalError wide k)
      (by simpa only [Rat.cast_neg] using hz.1) hz.2) using 1 <;> first | rfl | ring

private def jointCoefficient (H : Interval) (b i j : ℕ) : Interval :=
  point ((((i+1)*(i+2)*(if b = 0 then 1 else j+1) : ℕ) : ℚ)) * momentBox H (i+2) (b+j)

private theorem jointCoefficient_encloses {p b i j : ℕ} (hp : 0 < p) (hb : b ≤ 1)
    (hdegree : i+2+(b+j) ≤ 16) {H : Interval} (hh : H.encloses (3 / (p : ℝ))) :
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

private def jointBox (wide : Bool) (H A V : Interval) (b : ℕ) : Interval :=
  let error := jointError wide b
  series (taylorCutoff wide-b) (fun i ↦ series (taylorCutoff wide-b-i) (jointCoefficient H b i) V) A +
    box (-error) error

set_option maxHeartbeats 1000000 in
private theorem jointBox_encloses (wide : Bool) {p b : ℕ} (hp : 0 < p) (hb : b ≤ 1) {H A V : Interval}
    {a v : ℝ} (hh : H.encloses (3 / (p : ℝ))) (ha : A.encloses a) (hv : V.encloses v)
    (ha₀ : 0 ≤ a) (hav : a ≤ v) (hvtop : v ≤ (jointLimit wide : ℝ)) :
    (jointBox wide H A V b).encloses (leftStripExpMoment p 2 b a v / (compositionMarginalVariance p / 2)) := by
  have hpoly :
      (series (taylorCutoff wide-b) (fun i ↦ series (taylorCutoff wide-b-i) (jointCoefficient H b i) V) A).encloses
        (jointPolynomial wide p b a v) := by
    unfold jointPolynomial
    rw [sum_triangle (taylorCutoff wide - b) (fun i j ↦
      jointTaylorMoment p i (b+j) * (a^i * v^j / ((i.factorial : ℝ) * (j.factorial : ℝ))))]
    have hrow (i : ℕ) (hi : i < taylorCutoff wide-b) :=
      series_encloses (taylorCutoff wide-b-i) hv (fun j hj ↦ jointCoefficient_encloses (i := i) (j := j) hp hb
        (by cases wide <;> simp [taylorCutoff] at hi hj <;> omega) hh)
    convert series_encloses (taylorCutoff wide-b) ha hrow using 2
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hf : (2 : ℝ) ^ (b+2) * (2*v) ^ (taylorCutoff wide-b) / ((taylorCutoff wide-b).factorial : ℝ) ≤ (jointError wide b : ℝ) := by
    calc
      _ ≤ (2 : ℝ) ^ (b+2) * (2 * (jointLimit wide : ℝ)) ^ (taylorCutoff wide-b) / ((taylorCutoff wide-b).factorial : ℝ) := by
        gcongr
        exact mul_nonneg (by norm_num) (ha₀.trans hav)
      _ ≤ _ := by cases wide <;> interval_cases b <;> norm_num [jointLimit, jointError, taylorCutoff, Nat.factorial]
  have he := abs_le.mp ((jointTaylor_error wide hp hb ha₀ hav hvtop).trans hf)
  convert RoundedInterval.encloses_add hpoly
    (RoundedInterval.encloses_interval (lo := -jointError wide b) (hi := jointError wide b)
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

private def integrandBox (wide : Bool) (H A D V Zd Zv Zn : Interval) : Interval :=
  let r := sqrtBox Zd
  let q := reciprocalBox (point 2 * r)
  let r1 := zBox wide H D 1 * q
  let r2 := (zBox wide H D 2 - point 2 * (r1 * r1)) * q
  let r3 := (zBox wide H D 3 - point 6 * (r1 * r2)) * q
  let b := zBox wide H (0 - V) 1 * reciprocalBox (point 2 * Zn)
  let s := zBox wide H V 1 * reciprocalBox (point 2 * Zv)
  let rad := V * sqrtBox Zv * (point 3 * r2 + D * r3 +
    (s + b) * (point 2 * r1 + D * r2))
  V * (rad - jointBox wide H A V 1) + (point 1 - V * b) * jointBox wide H A V 0

set_option maxHeartbeats 1000000 in
private theorem integrandBox_sound (wide : Bool) {p : ℕ} (hp : 0 < p) {a v : ℝ} {H A D V : Interval}
    (hh : H.encloses (3 / (p : ℝ))) (ha : A.encloses a) (hd : D.encloses (v-a))
    (hv : V.encloses v) (ha₀ : 0 ≤ a) (hd₀ : 0 ≤ v-a)

    (hd₁ : v-a ≤ (marginalLimit wide 2 : ℝ)) (hv₁ : v ≤ (jointLimit wide : ℝ))
    (hZd : validZ (zBox wide H D 0)) (hZv : validZ (zBox wide H V 0)) (hZn : validZ (zBox wide H (0-V) 0))
    (hcheck : 0 < (integrandBox wide H A D V (zBox wide H D 0) (zBox wide H V 0) (zBox wide H (0-V) 0)).lower) :
    0 < leftStripRegularizedIntegrand p a v := by
  let d := v-a
  let c := compositionMarginalVariance p / 2
  have hc : 0 < c := half_pos (compositionMarginalVariance_pos p)
  have hav : a ≤ v := by linarith
  have hv₀ := ha₀.trans hav
  have hAbsD : |d| ≤ (marginalLimit wide 2 : ℝ) := by rwa [abs_of_nonneg hd₀]
  have hAbsV : |v| ≤ (jointLimit wide : ℝ) := by rwa [abs_of_nonneg hv₀]
  have hNegV : (0 - V).encloses (-v) := by
    change (point 0 - V).encloses (-v)
    simpa only [Rat.cast_zero, zero_sub] using
      RoundedInterval.encloses_sub (RoundedInterval.encloses_point 0) hv
  have zd (k : ℕ) (hk : k ≤ 3) :
      (zBox wide H D k).encloses (leftStripZ p k d) :=
    zBox_encloses wide hp hk hh hd (hAbsD.trans (by
      by_cases h : k ≤ 1 <;> cases wide <;> norm_num [marginalLimit, h]))
  have zv (k : ℕ) (hk : k ≤ 1) :
      (zBox wide H V k).encloses (leftStripZ p k v) :=
    zBox_encloses wide hp (by omega) hh hv (by cases wide <;> simpa [marginalLimit, jointLimit, hk] using hAbsV)
  have zn (k : ℕ) (hk : k ≤ 1) :
      (zBox wide H (0-V) k).encloses (leftStripZ p k (-v)) :=
    zBox_encloses wide hp (by omega) hh hNegV (by cases wide <;> simpa [marginalLimit, jointLimit, hk, abs_neg] using hAbsV)
  have hdZ := validZ_bounds hZd (zd 0 (by decide))
  have hvZ := validZ_bounds hZv (zv 0 (by decide))
  have hnZ := validZ_bounds hZn (zn 0 (by decide))
  have rd : (sqrtBox (zBox wide H D 0)).encloses (leftStripRoot p d) :=
    sqrtBox_encloses (zd 0 (by decide)) hdZ.1 hdZ.2
  have rv : (sqrtBox (zBox wide H V 0)).encloses (leftStripRoot p v) :=
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
  have J (k : ℕ) (hk : k ≤ 1) := jointBox_encloses wide hp hk hh ha hv ha₀ hav hv₁
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

private def checkBox (wide : Bool) (H A D : Interval) : Bool :=
  let V := A + D
  let Zd := zBox wide H D 0
  let Zv := zBox wide H V 0
  let Zn := zBox wide H (0-V) 0
  decide (validZ Zd ∧ validZ Zv ∧ validZ Zn ∧ 0 < (integrandBox wide H A D V Zd Zv Zn).lower)

private theorem checkBox_sound (wide : Bool) {p : ℕ} (hp : 0 < p) {a v : ℝ} {H A D : Interval}
    (hh : H.encloses (3 / (p : ℝ))) (ha : A.encloses a) (hd : D.encloses (v-a))
    (ha₀ : 0 ≤ a) (hd₀ : 0 ≤ v-a)
    (hd₁ : v-a ≤ (marginalLimit wide 2 : ℝ)) (hv₁ : v ≤ (jointLimit wide : ℝ))
    (hc : checkBox wide H A D = true) : 0 < leftStripRegularizedIntegrand p a v := by
  have hv : (A+D).encloses v := by
    convert RoundedInterval.encloses_add ha hd using 1
    ring
  obtain ⟨hZd, hZv, hZn, hpos⟩ := of_decide_eq_true hc
  exact integrandBox_sound wide hp hh ha hd hv ha₀ hd₀ hd₁ hv₁ hZd hZv hZn hpos

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

private def checkCover (wide : Bool) (depth : ℕ) (H A D : Endpoints) : Bool :=
  if checkBox wide (intervalOf H) (intervalOf A) (intervalOf D) then true else
    match depth with
    | 0 => false
    | n + 1 =>
      if (n+1) % 3 = 0 then
        checkCover wide n H (lowerHalf A) D && checkCover wide n H (upperHalf A) D
      else if (n+1) % 3 = 2 then
        checkCover wide n H A (lowerHalf D) && checkCover wide n H A (upperHalf D)
      else
        checkCover wide n (lowerHalf H) A D && checkCover wide n (upperHalf H) A D

private theorem checkCover_sound (wide : Bool) {p : ℕ} (hp : 0 < p) {a v : ℝ}
    (ha₀ : 0 ≤ a) (hd₀ : 0 ≤ v-a)
    (hd₁ : v-a ≤ (marginalLimit wide 2 : ℝ)) (hv₁ : v ≤ (jointLimit wide : ℝ))
    (n : ℕ) (H A D : Endpoints) (hh : InInterval H (3 / (p : ℝ)))
    (ha : InInterval A a) (hd : InInterval D (v-a))
    (hc : checkCover wide n H A D = true) : 0 < leftStripRegularizedIntegrand p a v := by
  have localSound {H A D : Endpoints} (hh : InInterval H (3 / (p : ℝ)))
      (ha : InInterval A a) (hd : InInterval D (v-a))
      (hb : checkBox wide (intervalOf H) (intervalOf A) (intervalOf D) = true) :
      0 < leftStripRegularizedIntegrand p a v :=
    checkBox_sound wide hp (RoundedInterval.encloses_interval hh.1 hh.2)
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
private theorem check_origin : checkCover false 12 (0, 3/11) (0, 1/2) (0, 1/2) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- The kernel reduces the closed interval check without generating a large replay term.
set_option maxRecDepth 20000 in
private theorem check_adjacent : checkCover false 12 (0, 3/11) (0, 1/2) (1/2, 1) = true := by
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
  · exact checkCover_sound false hp₀ ha hd.le (by simpa [marginalLimit] using hd₁)
      (by simpa [jointLimit] using hv₁) 12 _ _ _ hh ha'
      ⟨by simpa using hd.le, by simpa using h⟩ check_origin
  · exact checkCover_sound false hp₀ ha hd.le (by simpa [marginalLimit] using hd₁)
      (by simpa [jointLimit] using hv₁) 12 _ _ _ hh ha'
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
