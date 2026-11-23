/- GID: D5/S3/Fourier/Concentration/FiniteTailMomentMissingWindow
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/FiniteTailMomentMissingWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Short integer relations control the tail moment and the closed-window grid. -/

import D5.S3.Analytic.Asymptotics.DirichletPolynomialMeanSquare
import D5.S3.Fourier.Concentration.FiniteSineMissingWindow
import Mathlib.Data.Nat.Choose.Multinomial

/-! Finite moments of the real-time tail orbit under bounded-degree exclusion of exact relations. -/

set_option autoImplicit false

noncomputable section

open Filter Finset MeasureTheory Set
open scoped Topology NNReal

namespace D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow

open D5.S3.Weil.DirichletPolynomialMeanSquare (phase phaseIntegral norm_phaseIntegral_le)

private theorem average_character (rate start : ℝ) :
    Tendsto (fun length : ℝ =>
      (length⁻¹ : ℂ) * ∫ t in start..start + length, phase rate t)
      atTop (𝓝 (if rate = 0 then 1 else 0)) := by
  by_cases hrate : rate = 0
  · subst rate
    simp only [ite_true]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with length hlength
    simp [phase, hlength.ne']
  · simp only [hrate, ite_false]
    have hlimit :
        Tendsto (fun length : ℝ => (2 / |rate|) * length⁻¹) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_inv_atTop_zero.const_mul (2 / |rate|)
    refine squeeze_zero_norm' ?_ hlimit
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with length hlength
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlength, mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_phaseIntegral_le start (start + length) hrate)
      (inv_nonneg.mpr hlength.le)

private theorem short_difference {J : Type*} [Fintype J] [DecidableEq J] {p : ℕ}
    {m n : J → ℕ} (hm : m ∈ piAntidiag univ p) (hn : n ∈ piAntidiag univ p) :
    ∑ j, |(m j : ℤ) - (n j : ℤ)| ≤ (2 * p : ℤ) := by
  classical
  have hms : ∑ j, m j = p := (mem_piAntidiag.mp hm).1
  have hns : ∑ j, n j = p := (mem_piAntidiag.mp hn).1
  calc
    _ ≤ ∑ j, ((m j : ℤ) + (n j : ℤ)) := by
      apply sum_le_sum
      intro j _
      exact abs_le.mpr ⟨by omega, by omega⟩
    _ = _ := by
      rw [sum_add_distrib, ← Nat.cast_sum, ← Nat.cast_sum, hms, hns]
      ring

private theorem character_add (x y t : ℝ) :
    phase (x + y) t = phase x t * phase y t := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem character_nat_mul (n : ℕ) (x t : ℝ) :
    phase ((n : ℝ) * x) t = phase x t ^ n := by
  unfold phase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem character_sum {J : Type*} (s : Finset J) (f : J → ℝ) (t : ℝ) :
    phase (∑ j ∈ s, f j) t = ∏ j ∈ s, phase (f j) t := by
  unfold phase
  push_cast
  simp only [Finset.sum_mul, Complex.exp_sum]

private def complexScore {J : Type*} [Fintype J] (g w : J → ℝ) (t : ℝ) : ℂ :=
  ∑ j, (w j : ℂ) * phase (g j) t

private def monomialWeight {J : Type*} [Fintype J] (w : J → ℝ) (m : J → ℕ) : ℝ :=
  (Nat.multinomial univ m : ℝ) * ∏ j, w j ^ m j

private def monomialFrequency {J : Type*} [Fintype J] (g : J → ℝ) (m : J → ℕ) : ℝ :=
  ∑ j, (m j : ℝ) * g j

private theorem score_pow {J : Type*} [Fintype J] [DecidableEq J]
    (g w : J → ℝ) (t : ℝ) (p : ℕ) :
    complexScore g w t ^ p =
      ∑ m ∈ piAntidiag univ p, (monomialWeight w m : ℂ) * phase (monomialFrequency g m) t := by
  rw [complexScore, sum_pow_eq_sum_piAntidiag]
  apply sum_congr rfl
  intro m _
  unfold monomialWeight monomialFrequency
  push_cast
  rw [mul_assoc, character_sum]
  simp_rw [mul_pow, character_nat_mul, prod_mul_distrib]

private theorem score_conj {J : Type*} [Fintype J] (g w : J → ℝ) (t : ℝ) :
    star (complexScore g w t) = complexScore (fun j => -g j) w t := by
  unfold complexScore
  change starRingEnd ℂ (∑ j, (w j : ℂ) * phase (g j) t) = _
  rw [map_sum]
  apply sum_congr rfl
  intro j _
  rw [map_mul, Complex.conj_ofReal]
  congr 1
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp

private theorem mode_zero_iff {J : Type*} [Fintype J] [DecidableEq J] (g : J → ℝ)
    {p : ℕ} {m n : J → ℕ} (hm : m ∈ piAntidiag univ p) (hn : n ∈ piAntidiag univ p)
    (hshort : ∀ k : J → ℤ, (∑ j, |k j|) ≤ (2 * p : ℤ) →
      (∑ j, (k j : ℝ) * g j) = 0 → k = 0) :
    monomialFrequency g m + monomialFrequency (fun j => -g j) n = 0 ↔ m = n := by
  have hdiff : (∑ j, (((m j : ℤ) - (n j : ℤ) : ℤ) : ℝ) * g j) =
      monomialFrequency g m + monomialFrequency (fun j => -g j) n := by
    unfold monomialFrequency
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    push_cast
    ring
  constructor
  · intro h
    have hrel := hshort (fun j => (m j : ℤ) - (n j : ℤ)) (short_difference hm hn) (hdiff.trans h)
    funext j
    have hj : (m j : ℤ) - (n j : ℤ) = 0 := congrFun hrel j
    exact_mod_cast sub_eq_zero.mp hj
  · rintro rfl
    rw [← hdiff]
    simp

private def diagonal {J : Type*} [Fintype J] [DecidableEq J] (w : J → ℝ) (p : ℕ) : ℝ :=
  ∑ m ∈ piAntidiag univ p, monomialWeight w m ^ 2

private theorem score_even_expansion {J : Type*} [Fintype J] [DecidableEq J]
    (g w : J → ℝ) (t : ℝ) (p : ℕ) :
    (↑(‖complexScore g w t‖ ^ (2 * p)) : ℂ) =
      ∑ m ∈ piAntidiag univ p, ∑ n ∈ piAntidiag univ p,
        ((monomialWeight w m * monomialWeight w n : ℝ) : ℂ) *
          phase (monomialFrequency g m + monomialFrequency (fun j => -g j) n) t := by
  rw [pow_mul, Complex.ofReal_pow, Complex.ofReal_pow, ← Complex.mul_conj', mul_pow]
  change complexScore g w t ^ p * (starRingEnd ℂ (complexScore g w t)) ^ p = _
  rw [← map_pow]
  change complexScore g w t ^ p * star (complexScore g w t ^ p) = _
  rw [star_pow, score_conj]
  rw [score_pow, score_pow, sum_mul]
  apply sum_congr rfl
  intro m _
  rw [mul_sum]
  apply sum_congr rfl
  intro n _
  rw [character_add]
  push_cast
  ring

private theorem score_average_complex {J : Type*} [Fintype J] [DecidableEq J]
    (g w : J → ℝ) (p : ℕ) (start shift : ℝ)
    (hshort : ∀ k : J → ℤ, (∑ j, |k j|) ≤ (2 * p : ℤ) →
      (∑ j, (k j : ℝ) * g j) = 0 → k = 0) :
    Tendsto (fun length : ℝ =>
      (length⁻¹ : ℂ) * ∫ t in start..start + length,
        (↑(‖complexScore g w (t + shift)‖ ^ (2 * p)) : ℂ))
      atTop (𝓝 (diagonal w p : ℂ)) := by
  let S : Finset (J → ℕ) := piAntidiag univ p
  let rate (m n : J → ℕ) := monomialFrequency g m + monomialFrequency (fun j => -g j) n
  let c (m n : J → ℕ) : ℂ := (monomialWeight w m * monomialWeight w n : ℝ)
  let f (m n : J → ℕ) (t : ℝ) := c m n * phase (rate m n) (t + shift)
  have integrate (m n : J → ℕ) (L : ℝ) : IntervalIntegrable (f m n) volume start (start + L) := by
    apply Continuous.intervalIntegrable
    change Continuous (fun t : ℝ => c m n * Complex.exp (↑(rate m n) * Complex.I * ↑(t + shift)))
    fun_prop
  have average (m n : J → ℕ) :
      Tendsto (fun L : ℝ => (L⁻¹ : ℂ) * ∫ t in start..start + L, f m n t)
        atTop (𝓝 (if rate m n = 0 then c m n else 0)) := by
    have hfun (t : ℝ) : f m n t = (c m n * phase (rate m n) shift) * phase (rate m n) t := by
      unfold f phase
      rw [mul_assoc (c m n), ← Complex.exp_add]
      congr 2
      push_cast
      ring
    have he (L : ℝ) : (L⁻¹ : ℂ) * (∫ t in start..start + L, f m n t) =
        (c m n * phase (rate m n) shift) *
          ((L⁻¹ : ℂ) * ∫ t in start..start + L, phase (rate m n) t) := by
      simp_rw [hfun, intervalIntegral.integral_const_mul]
      ring
    simp_rw [he]
    convert (average_character (rate m n) start).const_mul (c m n * phase (rate m n) shift) using 2
    split_ifs with h
    · simp [h, phase]
    · simp
  have hlim := tendsto_finsetSum S (fun m _ =>
    tendsto_finsetSum S (fun n _ => average m n))
  have hvalue : (∑ m ∈ S, ∑ n ∈ S, if rate m n = 0 then c m n else 0) = (diagonal w p : ℂ) := by
    unfold diagonal
    push_cast
    apply sum_congr rfl
    intro m hm
    rw [sum_eq_single_of_mem m hm]
    · simp [rate, mode_zero_iff g hm hm hshort, c, pow_two]
    · intro n hn hnm
      simp [rate, mode_zero_iff g hm hn hshort, Ne.symm hnm]
  rw [hvalue] at hlim
  convert hlim using 1
  funext L
  rw [show (fun t : ℝ => (↑(‖complexScore g w (t + shift)‖ ^ (2 * p)) : ℂ)) =
      fun t => ∑ m ∈ S, ∑ n ∈ S, f m n t from funext (fun t => score_even_expansion g w (t + shift) p)]
  rw [intervalIntegral.integral_finsetSum (s := S)]
  · simp_rw [intervalIntegral.integral_finsetSum (s := S) (fun n _ => integrate _ n L), mul_sum]
  · intro m _
    apply Continuous.intervalIntegrable
    apply continuous_finsetSum
    intro n _
    change Continuous (fun t : ℝ => c m n * Complex.exp (↑(rate m n) * Complex.I * ↑(t + shift)))
    fun_prop

private theorem diagonal_bound {J : Type*} [Fintype J] [DecidableEq J]
    (w : J → ℝ) (p : ℕ) :
    diagonal w p ≤ (p : ℝ) ^ p * (∑ j, w j ^ 2) ^ p := by
  have hcoeff (m : J → ℕ) (hm : m ∈ piAntidiag univ p) :
      (Nat.multinomial univ m : ℝ) ≤ (p : ℝ) ^ p := by
    have hnat : Nat.multinomial univ m ≤ p.factorial := by
      unfold Nat.multinomial
      rw [(mem_piAntidiag.mp hm).1]
      exact Nat.div_le_self _ _
    exact_mod_cast hnat.trans (Nat.factorial_le_pow p)
  unfold diagonal
  rw [sum_pow_eq_sum_piAntidiag, mul_sum]
  apply sum_le_sum
  intro m hm
  unfold monomialWeight
  rw [mul_pow, ← Finset.prod_pow]
  have hprod : (∏ j, (w j ^ m j) ^ 2) = ∏ j, (w j ^ 2) ^ m j := by
    apply prod_congr rfl
    intro j _
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [hprod, ← mul_assoc, pow_two]
  apply mul_le_mul_of_nonneg_right _ (prod_nonneg (fun j _ => pow_nonneg (sq_nonneg (w j)) _))
  exact mul_le_mul_of_nonneg_right (hcoeff m hm) (by positivity)

private theorem score_average {J : Type*} [Fintype J] [DecidableEq J]
    (g w : J → ℝ) (p : ℕ) (start shift : ℝ)
    (hshort : ∀ k : J → ℤ, (∑ j, |k j|) ≤ (2 * p : ℤ) →
      (∑ j, (k j : ℝ) * g j) = 0 → k = 0) :
    Tendsto (fun length : ℝ =>
      length⁻¹ * ∫ t in start..start + length, ‖complexScore g w (t + shift)‖ ^ (2 * p))
      atTop (𝓝 (diagonal w p)) := by
  have h := (Complex.continuous_re.tendsto (diagonal w p : ℂ)).comp
    (score_average_complex g w p start shift hshort)
  simpa only [Function.comp_def, Complex.ofReal_re, ← Complex.ofReal_inv, Complex.re_ofReal_mul,
    intervalIntegral.integral_ofReal] using h

private theorem complexScore_continuous {J : Type*} [Fintype J] (g w : J → ℝ) :
    Continuous (complexScore g w) := by
  unfold complexScore
  apply continuous_finsetSum
  intro j _
  unfold phase
  fun_prop

private theorem exists_grid_lt {J K : Type*} [Fintype J] [DecidableEq J] [Fintype K]
    (g w : J → ℝ) (grid : K → ℝ) (p : ℕ) (A δ : ℝ) (hδ : 0 < δ)
    (hshort : ∀ k : J → ℤ, (∑ j, |k j|) ≤ (2 * p : ℤ) →
      (∑ j, (k j : ℝ) * g j) = 0 → k = 0)
    (hbudget : (Fintype.card K : ℝ) * ((p : ℝ) ^ p * (∑ j, w j ^ 2) ^ p) < δ ^ (2 * p)) :
    ∃ a > A, ∀ k, ‖complexScore g w (a + grid k)‖ < δ := by
  let start := A + 1
  let F (t : ℝ) := ∑ k, ‖complexScore g w (t + grid k)‖ ^ (2 * p)
  have hF : Continuous F := by
    apply continuous_finsetSum
    intro k _
    exact (((complexScore_continuous g w).comp (continuous_id.add continuous_const)).norm).pow _
  have hsum := tendsto_finsetSum (univ : Finset K) (fun k _ =>
    score_average g w p start (grid k) hshort)
  have havg : Tendsto (fun length => length⁻¹ * ∫ t in start..start + length, F t)
      atTop (𝓝 ((Fintype.card K : ℝ) * diagonal w p)) := by
    simp only [sum_const, card_univ, nsmul_eq_mul] at hsum
    convert hsum using 1
    funext L
    unfold F
    rw [intervalIntegral.integral_finsetSum (s := (univ : Finset K)), mul_sum]
    intro k _
    exact ((((complexScore_continuous g w).comp
      (continuous_id.add (continuous_const (y := grid k)))).norm).pow (2 * p)).intervalIntegrable _ _
  have hlim := (mul_le_mul_of_nonneg_left (diagonal_bound w p)
    (Nat.cast_nonneg (Fintype.card K))).trans_lt hbudget
  obtain ⟨L, hsmall, hL⟩ := ((havg.eventually_lt_const hlim).and
    (eventually_gt_atTop (0 : ℝ))).exists
  by_contra! h
  have hpoint (t : ℝ) (ht : t ∈ Icc start (start + L)) : δ ^ (2 * p) ≤ F t := by
    obtain ⟨k, hk⟩ := h t (by dsimp [start] at ht; linarith [ht.1])
    have hpow := pow_le_pow_left₀ hδ.le hk (2 * p)
    exact hpow.trans (Finset.single_le_sum
      (f := fun i => ‖complexScore g w (t + grid i)‖ ^ (2 * p))
      (fun i _ => by positivity) (mem_univ k))
  have hmono : (∫ _ : ℝ in start..start + L, δ ^ (2 * p)) ≤ ∫ t in start..start + L, F t :=
    intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      (hF.intervalIntegrable _ _) hpoint
  have hlarge := mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr hL.le)
  rw [intervalIntegral.integral_const, show start + L - start = L by ring,
    smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hL.ne', one_mul] at hlarge
  exact (not_lt_of_ge hlarge) hsmall

open D5.S3.Fourier.Concentration.FiniteSineMissingWindow (floor_grid_cover sine_score_change)

private theorem im_complexScore {J : Type*} [Fintype J] (g w : J → ℝ) (t : ℝ) :
    (complexScore g w t).im = ∑ j, w j * Real.sin (g j * t) := by
  unfold complexScore
  rw [Complex.im_sum]
  apply sum_congr rfl
  intro j _
  rw [Complex.im_ofReal_mul]
  unfold phase
  rw [show (g j : ℂ) * Complex.I * (t : ℂ) = ((g j * t : ℝ) : ℂ) * Complex.I by
    push_cast
    ring, Complex.exp_ofReal_mul_I_im]

/-- Absence of short exact integer relations among the tail frequencies suffices for
arbitrarily late closed windows with the stated power-moment grid budget. -/
theorem exists_arbitrarily_late_tail_window {J : Type*} [Fintype J]
    (g w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (p : ℕ) (hp : 0 < p)
    (hshort : ∀ k : J → ℤ, (∑ j, |k j|) ≤ (2 * p : ℤ) →
      (∑ j, (k j : ℝ) * g j) = 0 → k = 0)
    {H h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) :
    let V := ∑ j, w j ^ 2
    V = 0 ∨ ((⌊H / h⌋₊ : ℝ) + 1) * (2 * (p : ℝ) * V / δ ^ 2) ^ p < 1 →
    ∀ A : ℝ, ∃ a > A, ∀ t ∈ Icc a (a + H),
      ∑ j, w j * Real.sin (g j * t) < δ + h * ∑ j, w j * |g j| := by
  classical
  intro V hbudget A
  rcases hbudget with hzero | hbudget
  · have hz (j : J) : w j = 0 := sq_eq_zero_iff.mp <|
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (w j))).mp hzero j (mem_univ j)
    refine ⟨A + 1, by linarith, ?_⟩
    intro t _
    simpa only [hz, zero_mul, sum_const_zero, mul_zero, add_zero] using hδ
  · let K := Fin (⌊H / h⌋₊ + 1)
    let grid (k : K) : ℝ := (k : ℕ) * h
    have hV : 0 ≤ V := sum_nonneg (fun j _ => sq_nonneg (w j))
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
    have hpow : 0 < (δ ^ 2) ^ p := by positivity
    have hcard : (Fintype.card K : ℝ) = (⌊H / h⌋₊ : ℝ) + 1 := by simp [K]
    have hbig : (Fintype.card K : ℝ) * (2 * (p : ℝ) * V) ^ p < δ ^ (2 * p) := by
      rw [div_pow, ← mul_div_assoc, div_lt_one hpow, ← pow_mul] at hbudget
      simpa only [hcard] using hbudget
    have hsmall : (Fintype.card K : ℝ) * ((p : ℝ) ^ p * V ^ p) < δ ^ (2 * p) := by
      rw [← mul_pow]
      exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hpR.le hV)
        (by nlinarith only [mul_nonneg hpR.le hV] : (p : ℝ) * V ≤ 2 * (p : ℝ) * V) p)
        (Nat.cast_nonneg _)).trans_lt hbig
    obtain ⟨a, ha, hgrid⟩ := exists_grid_lt g w grid p A δ hδ hshort hsmall
    refine ⟨a, ha, fun t ht => ?_⟩
    have ht' : t - a ∈ Icc (0 : ℝ) H :=
      ⟨sub_nonneg.mpr ht.1, (sub_le_iff_le_add).mpr (by linarith [ht.2])⟩
    obtain ⟨k, hk⟩ := floor_grid_cover hh ht'
    have hk' : |t - (a + grid k)| ≤ h := by
      simpa only [grid, sub_sub] using hk
    let weight (j : J) : ℝ≥0 := ⟨w j, hw j⟩
    have hchange := sine_score_change univ g (fun _ : J => 0) weight t (a + grid k)
    simp only [zero_add] at hchange
    change (∑ j, w j * Real.sin (g j * t)) -
        (∑ j, w j * Real.sin (g j * (a + grid k))) ≤
          (∑ j, w j * |g j|) * |t - (a + grid k)| at hchange
    have hstep := hchange.trans (mul_le_mul_of_nonneg_left hk'
      (sum_nonneg (fun j _ => mul_nonneg (hw j) (abs_nonneg _))))
    have hnode : (∑ j, w j * Real.sin (g j * (a + grid k))) < δ := by
      rw [← im_complexScore]
      exact (Complex.im_le_norm _).trans_lt (hgrid k)
    linarith only [hstep, hnode, mul_comm h (∑ j, w j * |g j|)]

#print axioms exists_arbitrarily_late_tail_window

end D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
