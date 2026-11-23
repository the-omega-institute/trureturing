/- GID: D5/S3/Fourier/WeightedPhaseRecurrence
   generality: G
   mirror-B: D5/B/S3/Fourier/WeightedPhaseRecurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A Fejer product gives finite interval recurrence for normalized weighted phase loss. -/

import D5.S3.Zeros.Repulsion.FejerNearCollisionBound
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-! Finite-time recurrence from the nonnegative Fourier expansion of a weighted Fejér product. -/

set_option autoImplicit false

open MeasureTheory Set
open scoped BigOperators

namespace D5.S3.Fourier.WeightedPhaseRecurrence

open D5.S3.Zeros.Repulsion.FejerNearCollisionBound
  (fejerKernel fejer_square fejer_nonnegative fejer_zero)

noncomputable section

/-- Weighted cosine loss at a real time relative to a family of target angles. -/
def phaseLoss {J : Type*} [Fintype J] (g θ p : J → ℝ) (t : ℝ) : ℝ :=
  ∑ j, p j * (1 - Real.cos (g j * t - θ j))

private def modes (N : ℕ) : Finset ℤ :=
  Finset.Icc (-(N : ℤ)) (N : ℤ)

private theorem mem_modes {N : ℕ} {k : ℤ} : k ∈ modes N ↔ |k| ≤ (N : ℤ) :=
  Finset.mem_Icc.trans abs_le.symm

private def triangle (N : ℕ) (k : ℤ) : ℝ :=
  1 - ((|k| : ℤ) : ℝ) / (N : ℝ)

private def edge (N : ℕ) (k : ℤ) : ℝ :=
  (if k = (N : ℤ) then 1 / 2 else 0) + (if k = -(N : ℤ) then 1 / 2 else 0)

private def expI (x : ℝ) : ℂ :=
  Complex.exp ((x : ℂ) * Complex.I)

private theorem fourier_fejer {N : ℕ} (hN : 0 < N) (x : ℝ) :
    (∑ k ∈ modes N, (triangle N k : ℂ) * expI ((k : ℝ) * x)) =
      (fejerKernel N x : ℂ) := by
  have hN' : (N : ℝ) ≠ 0 := by positivity
  apply Complex.ext
  · simp only [Complex.ofReal_re, Complex.re_sum, Complex.mul_re, Complex.ofReal_im,
      zero_mul, sub_zero, expI, Complex.exp_ofReal_mul_I_re]
    unfold fejerKernel
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk h
    have hle := mem_modes.mp hk
    have hge : ¬ |k| < (N : ℤ) := fun hlt => h (Finset.mem_filter.mpr ⟨hk, hlt⟩)
    have heq : |k| = (N : ℤ) := le_antisymm hle (le_of_not_gt hge)
    simp [heq, hN']
  · simp only [Complex.ofReal_im, Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
      zero_mul, add_zero, expI, Complex.exp_ofReal_mul_I_im]
    let f (k : ℤ) := triangle N k * Real.sin ((k : ℝ) * x)
    change ∑ k ∈ modes N, f k = 0
    have hneg : (∑ k ∈ modes N, f k) = ∑ k ∈ modes N, -f k := by
      refine Finset.sum_nbij' Neg.neg Neg.neg ?_ ?_ ?_ ?_ ?_
      · intro k hk
        simpa only [mem_modes, abs_neg] using hk
      · intro k hk
        simpa only [mem_modes, abs_neg] using hk
      · simp
      · simp
      · intro k _
        simp [f, triangle]
    rw [Finset.sum_neg_distrib] at hneg
    linarith only [hneg]

private theorem fourier_edge (N : ℕ) (x : ℝ) :
    (∑ k ∈ modes N, (edge N k : ℂ) * expI ((k : ℝ) * x)) =
      (Real.cos ((N : ℝ) * x) : ℂ) := by
  have hpos : (N : ℤ) ∈ modes N := mem_modes.mpr (by simp)
  have hneg : -(N : ℤ) ∈ modes N := mem_modes.mpr (by simp)
  simp only [edge, Complex.ofReal_add, add_mul, Finset.sum_add_distrib, apply_ite
    (fun r : ℝ => (r : ℂ)), ite_mul, Complex.ofReal_zero, zero_mul,
    Finset.sum_ite_eq', hpos, hneg, ite_true, Int.cast_natCast, Int.cast_neg, neg_mul]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, expI, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, expI, Complex.exp_ofReal_mul_I_im, Real.sin_neg]
    ring

-- The defect removes only the zero coefficient in its replaced coordinate.
-- The remaining triangular coefficients and the two edge coefficients are retained.
private def correction (N : ℕ) (k : ℤ) : ℝ :=
  triangle N k - (if k = 0 then 1 else 0) + edge N k

private theorem fourier_correction {N : ℕ} (hN : 0 < N) (x : ℝ) :
    (∑ k ∈ modes N, (correction N k : ℂ) * expI ((k : ℝ) * x)) =
      ((fejerKernel N x + Real.cos ((N : ℝ) * x) - 1 : ℝ) : ℂ) := by
  have hzero : (0 : ℤ) ∈ modes N := mem_modes.mpr (by simp)
  have hcenter :
      (∑ k ∈ modes N, ((if k = 0 then 1 else 0 : ℝ) : ℂ) * expI ((k : ℝ) * x)) = 1 := by
    simp only [apply_ite (fun r : ℝ => (r : ℂ)), ite_mul,
      Complex.ofReal_zero, zero_mul, Finset.sum_ite_eq', hzero, ite_true]
    simp [expI]
  simp only [correction, Complex.ofReal_add, Complex.ofReal_sub, add_mul, sub_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, fourier_fejer hN, fourier_edge, hcenter,
    Complex.ofReal_one]
  ring

private theorem normSq_expI_sub_one (x : ℝ) :
    Complex.normSq (expI x - 1) = 2 * (1 - Real.cos x) := by
  unfold expI
  rw [Complex.normSq_sub, Complex.normSq_eq_norm_sq (Complex.exp _),
    Complex.norm_exp_ofReal_mul_I]
  simp [Complex.exp_ofReal_mul_I_re]
  ring

private theorem fejer_defect {N : ℕ} (hN : 0 < N) (x : ℝ) :
    (1 - Real.cos x) * fejerKernel N x = (1 - Real.cos ((N : ℝ) * x)) / N := by
  have hpow (n : ℕ) : expI ((n : ℝ) * x) = expI x ^ n := by
    unfold expI
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h := congrArg Complex.normSq (geom_sum_mul (expI x) N)
  rw [Complex.normSq_mul, normSq_expI_sub_one, ← hpow, normSq_expI_sub_one] at h
  rw [fejer_square hN x]
  change (1 - Real.cos x) * (1 / (N : ℝ) *
      Complex.normSq (∑ r ∈ Finset.range N, expI ((r : ℝ) * x))) = _
  simp_rw [hpow]
  rw [one_div_mul_eq_div, ← mul_div_assoc]
  congr 1
  nlinarith only [h]

private def frequencyBox {J : Type*} [Fintype J] [DecidableEq J] (N : ℕ) : Finset (J → ℤ) :=
  Fintype.piFinset fun _ => modes N

private theorem prod_cosine_expansion {J : Type*} [Fintype J] [DecidableEq J]
    (N : ℕ) (b : J → ℤ → ℝ) (x y : J → ℝ)
    (hy : ∀ j, ∑ k ∈ modes N, (b j k : ℂ) * expI ((k : ℝ) * x j) = (y j : ℂ)) :
    (∑ k ∈ frequencyBox N, (∏ j, b j (k j)) *
      Real.cos (∑ j, (k j : ℝ) * x j)) = ∏ j, y j := by
  have h := Finset.prod_univ_sum (fun _ : J => modes N)
    (fun j k => (b j k : ℂ) * expI ((k : ℝ) * x j))
  simp only [hy] at h
  have hprod (k : J → ℤ) : (∏ j, expI ((k j : ℝ) * x j)) =
      expI (∑ j, (k j : ℝ) * x j) := by
    unfold expI
    push_cast
    rw [Finset.sum_mul, Complex.exp_sum]
  simp only [Finset.prod_mul_distrib, ← Complex.ofReal_prod, hprod] at h
  have hre := congrArg Complex.re h.symm
  simpa only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, expI, Complex.exp_ofReal_mul_I_re, frequencyBox] using hre

private def weights {J : Type*} [Fintype J] [DecidableEq J]
    (N : ℕ) (ε : ℝ) (p : J → ℝ) (k : J → ℤ) : ℝ :=
  (ε - 1 / (N : ℝ)) * (∏ j, triangle N (k j)) +
    ∑ i, (p i / (N : ℝ)) * ∏ j, (if j = i then correction N (k j) else triangle N (k j))

private theorem weighted_fejer_expansion {J : Type*} [Fintype J] [DecidableEq J]
    {N : ℕ} (hN : 0 < N) (ε : ℝ) (p x : J → ℝ) (hp : ∑ j, p j = 1) :
    (∑ k ∈ frequencyBox N, weights N ε p k * Real.cos (∑ j, (k j : ℝ) * x j)) =
      (ε - ∑ j, p j * (1 - Real.cos (x j))) * ∏ j, fejerKernel N (x j) := by
  let F (j : J) := fejerKernel N (x j)
  let C (j : J) := F j + Real.cos ((N : ℝ) * x j) - 1
  let K := ∏ j, F j
  let L (i : J) := ∏ j ∈ Finset.univ.erase i, F j
  have hsplit (i : J) : L i * F i = K :=
    Finset.prod_erase_mul _ _ (Finset.mem_univ i)
  have heq (i : J) :
      (∏ j, if j = i then C j else F j) = L i * C i := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), ite_eq_left rfl]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [ite_eq_right (Finset.ne_of_mem_erase hj)]
  have hbulk := prod_cosine_expansion N (fun _ : J => triangle N) x F
    (fun j => fourier_fejer hN (x j))
  have hedge (i : J) := prod_cosine_expansion N
    (fun j k => if j = i then correction N k else triangle N k) x
    (fun j => if j = i then C j else F j)
    (fun j => by
      by_cases hji : j = i
      · subst j
        simpa [F, C] using fourier_correction hN (x i)
      · simpa only [ite_eq_right hji] using fourier_fejer hN (x j))
  calc
    _ = (ε - 1 / (N : ℝ)) * K + ∑ i, (p i / (N : ℝ)) * (L i * C i) := by
      simp only [weights, add_mul, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]
      rw [← Finset.mul_sum, hbulk, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.mul_sum, hedge i, heq]
    _ = ε * K - ∑ i, p i * (1 - Real.cos (x i)) * K := by
      have hdefect (i : J) :
          p i * (1 - Real.cos (x i)) * K =
            (p i / (N : ℝ)) * K - (p i / (N : ℝ)) * (L i * C i) := by
        rw [← hsplit i]
        calc
          _ = (p i * L i) * ((1 - Real.cos (x i)) * F i) := by ring
          _ = _ := by
            rw [show (1 - Real.cos (x i)) * F i =
              (1 - Real.cos ((N : ℝ) * x i)) / N from fejer_defect hN (x i)]
            dsimp [C]
            ring
      simp_rw [hdefect, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_div, hp]
      ring
    _ = _ := by rw [sub_mul, Finset.sum_mul]

private theorem weights_mass {J : Type*} [Fintype J] [DecidableEq J]
    {N : ℕ} (hN : 0 < N) (ε : ℝ) (p : J → ℝ) (hp : ∑ j, p j = 1) :
    ∑ k ∈ frequencyBox N, weights N ε p k = ε * (N : ℝ) ^ Fintype.card J := by
  simpa [fejer_zero hN] using weighted_fejer_expansion hN ε p (fun _ => 0) hp

private theorem mem_frequencyBox {J : Type*} [Fintype J] [DecidableEq J]
    {N : ℕ} {k : J → ℤ} : k ∈ frequencyBox N ↔ ∀ j, |k j| ≤ (N : ℤ) := by
  simp only [frequencyBox, Fintype.mem_piFinset, mem_modes]

private theorem weights_nonneg {J : Type*} [Fintype J] [DecidableEq J]
    {N : ℕ} {ε : ℝ} {p : J → ℝ} {k : J → ℤ}
    (hN : 0 < N) (hp : ∀ j, 0 ≤ p j) (hε : 1 / (N : ℝ) < ε)
    (hb : ∀ j, |k j| ≤ (N : ℤ)) : 0 ≤ weights N ε p k := by
  have htriangle (j : J) : 0 ≤ triangle N (k j) := by
    apply sub_nonneg.mpr
    have hN' : (0 : ℝ) < N := by positivity
    rw [div_le_iff₀ hN', one_mul]
    exact_mod_cast hb j
  have hcorrection (j : J) : 0 ≤ correction N (k j) := by
    unfold correction
    apply add_nonneg
    · by_cases h : k j = 0
      · simp [h, triangle]
      · simpa only [ite_eq_right h, sub_zero] using htriangle j
    · unfold edge
      apply add_nonneg <;> split <;> norm_num
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr hε.le) (Finset.prod_nonneg fun j _ =>
    htriangle j)) (Finset.sum_nonneg fun i _ =>
      mul_nonneg (div_nonneg (hp i) (Nat.cast_nonneg N))
        (Finset.prod_nonneg fun j _ => by
          by_cases h : j = i
          · simpa only [ite_eq_left h] using hcorrection j
          · simpa only [ite_eq_right h] using htriangle j))

private def modeFrequency {J : Type*} [Fintype J] (g : J → ℝ) (k : J → ℤ) : ℝ :=
  ∑ j, (k j : ℝ) * g j

private def sincBound (R ξ : ℝ) : ℝ :=
  2 * |Real.sin (R * ξ / 2)| / |ξ|

private theorem sincBound_le_reciprocal (R ξ : ℝ) : sincBound R ξ ≤ 2 / |ξ| := by
  unfold sincBound
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (R * ξ / 2)) (by norm_num : 0 ≤ (2 : ℝ))

private def resonantMass {K : Type*} (s : Finset K) (c ξ φ : K → ℝ) : ℝ := by
  classical
  exact ∑ k ∈ s.filter (fun k => ξ k = 0), c k * Real.cos (φ k)

private def sincPenalty {K : Type*} (s : Finset K) (c ξ : K → ℝ) (R : ℝ) : ℝ := by
  classical
  exact ∑ k ∈ s.filter (fun k => ξ k ≠ 0), c k * sincBound R (ξ k)

/-- Window length times the signed resonant coefficient sum, minus the sum of
the coefficient-weighted absolute interval cosine bounds at nonzero frequencies. -/
def recurrenceMargin {J : Type*} [Fintype J] (g θ p : J → ℝ) (N : ℕ) (ε R : ℝ) : ℝ := by
  classical
  exact R * resonantMass (frequencyBox N) (weights N ε p) (modeFrequency g) (modeFrequency θ) -
    sincPenalty (frequencyBox N) (weights N ε p) (modeFrequency g) R

private theorem cosine_integral_lower (a R ξ φ : ℝ) (hξ : ξ ≠ 0) :
    -sincBound R ξ ≤ ∫ t in a..a + R, Real.cos (ξ * t - φ) := by
  have heq : (∫ t in a..a + R, Real.cos (ξ * t - φ)) =
      (Real.sin (ξ * (a + R) - φ) - Real.sin (ξ * a - φ)) / ξ := by
    simpa only [sub_eq_add_neg, smul_eq_mul, div_eq_mul_inv, mul_comm ξ⁻¹] using
      (intervalIntegral.integral_comp_mul_add Real.cos (a := a) (b := a + R) hξ (-φ)).trans
        (congrArg (ξ⁻¹ • ·) integral_cos)
  have hbound : |∫ t in a..a + R, Real.cos (ξ * t - φ)| ≤ sincBound R ξ := by
    rw [heq, Real.sin_sub_sin, abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [show (ξ * (a + R) - φ - (ξ * a - φ)) / 2 = R * ξ / 2 by ring]
    unfold sincBound
    apply div_le_div_of_nonneg_right _ (abs_nonneg _)
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity)).trans_eq
      (mul_one _)
  exact (abs_le.mp hbound).1

private theorem cosine_sum_integral_lower {K : Type*} (s : Finset K) (c ξ φ : K → ℝ)
    (a R : ℝ) (hc : ∀ k ∈ s, 0 ≤ c k) :
    R * resonantMass s c ξ φ - sincPenalty s c ξ R ≤
      ∫ t in a..a + R, ∑ k ∈ s, c k * Real.cos (ξ k * t - φ k) := by
  classical
  rw [intervalIntegral.integral_finsetSum (fun k _ => by
    apply Continuous.intervalIntegrable
    fun_prop)]
  rw [← Finset.sum_filter_add_sum_filter_not s (fun k => ξ k = 0)]
  unfold resonantMass sincPenalty
  rw [Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro k hk
    simp only [(Finset.mem_filter.mp hk).2, zero_mul, zero_sub, Real.cos_neg,
      intervalIntegral.integral_const, smul_eq_mul]
    rw [show a + R - a = R by ring]
  · apply Finset.sum_le_sum
    intro k hk
    rw [intervalIntegral.integral_const_mul, ← mul_neg]
    exact mul_le_mul_of_nonneg_left (cosine_integral_lower a R _ _ (Finset.mem_filter.mp hk).2)
      (hc k (Finset.mem_filter.mp hk).1)

private theorem fejer_bounds {N : ℕ} (hN : 0 < N) (x : ℝ) :
    0 ≤ fejerKernel N x ∧ fejerKernel N x ≤ N := by
  refine ⟨fejer_nonnegative hN x, ?_⟩
  let S := ∑ r ∈ Finset.range N, expI ((r : ℝ) * x)
  rw [fejer_square hN]
  change (1 / (N : ℝ)) * Complex.normSq S ≤ N
  have hnorm : ‖S‖ ≤ (N : ℝ) := by
    calc
      ‖S‖ ≤ ∑ r ∈ Finset.range N, ‖expI ((r : ℝ) * x)‖ := norm_sum_le _ _
      _ = N := by
        simp only [expI, Complex.norm_exp_ofReal_mul_I, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, mul_one]
  rw [Complex.normSq_eq_norm_sq, one_div_mul_eq_div, div_le_iff₀ (by positivity)]
  simpa only [pow_two] using (sq_le_sq₀ (norm_nonneg _) (Nat.cast_nonneg N)).mpr hnorm

/-- Positive signed Fejér margin gives a quantitative loss guarantee on every closed
interval of length `R`. -/
theorem weighted_phase_recurrence_of_margin {J : Type*} [Fintype J]
    (g θ p : J → ℝ) (N : ℕ) (ε a R : ℝ)
    (hN : 0 < N) (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1)
    (hε : 1 / (N : ℝ) < ε) (hR : 0 < R)
    (hmargin : 0 < recurrenceMargin g θ p N ε R) :
    ∃ t ∈ Icc a (a + R),
      phaseLoss g θ p t ≤ ε - recurrenceMargin g θ p N ε R / (R * (N : ℝ) ^ Fintype.card J) := by
  classical
  let f (t : ℝ) := ∑ k ∈ frequencyBox N,
    weights N ε p k * Real.cos (modeFrequency g k * t - modeFrequency θ k)
  have hcont : Continuous f := by
    unfold f
    fun_prop
  have ha : a ≤ a + R := by linarith
  have hIntegral : recurrenceMargin g θ p N ε R ≤ ∫ t in a..a + R, f t :=
    cosine_sum_integral_lower (frequencyBox N) (weights N ε p) (modeFrequency g)
      (modeFrequency θ) a R (fun _ hk => weights_nonneg hN hp hε (mem_frequencyBox.mp hk))
  obtain ⟨t, ht, htmax⟩ := isCompact_Icc.exists_isMaxOn ⟨a, left_mem_Icc.mpr ha⟩ hcont.continuousOn
  have haverage : recurrenceMargin g θ p N ε R ≤ R * f t := by
    refine hIntegral.trans ?_
    have h := intervalIntegral.integral_mono_on (μ := volume) ha (hcont.intervalIntegrable _ _)
      (intervalIntegrable_const (c := f t)) (fun s hs => htmax hs)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] using h
  have hx (k : J → ℤ) :
      modeFrequency g k * t - modeFrequency θ k = ∑ j, (k j : ℝ) * (g j * t - θ j) := by
    simp only [modeFrequency, mul_sub, ← mul_assoc, Finset.sum_sub_distrib, Finset.sum_mul]
  let P := ∏ j, fejerKernel N (g j * t - θ j)
  have hexpansion : f t = (ε - phaseLoss g θ p t) * P := by
    simpa only [f, hx, phaseLoss, P] using
      weighted_fejer_expansion hN ε p (fun j => g j * t - θ j) hpsum
  rw [hexpansion, ← mul_assoc, mul_comm R, mul_assoc] at haverage
  have hP : 0 ≤ P := Finset.prod_nonneg fun j _ => (fejer_bounds hN _).1
  have hPmax : P ≤ (N : ℝ) ^ Fintype.card J := by
    change P ≤ (N : ℝ) ^ (Finset.univ : Finset J).card
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun _ _ => (fejer_bounds hN _).1)
      (fun _ _ => (fejer_bounds hN _).2)
  have hdefect : 0 < ε - phaseLoss g θ p t :=
    pos_of_mul_pos_left (hmargin.trans_le haverage) (mul_nonneg hR.le hP)
  have hscale : 0 < R * (N : ℝ) ^ Fintype.card J := by positivity
  have hquant : recurrenceMargin g θ p N ε R / (R * (N : ℝ) ^ Fintype.card J) ≤
      ε - phaseLoss g θ p t :=
    (div_le_iff₀ hscale).2 (haverage.trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPmax hR.le) hdefect.le))
  exact ⟨t, ht, by linarith⟩

/-- A finite band of compatible exact resonances and a lower bound for the other
frequencies give a uniform time window for normalized weighted phase loss. -/
theorem weighted_phase_recurrence {J : Type*} [Fintype J]
    (g θ p : J → ℝ) (N : ℕ) (ε δ a R : ℝ)
    (hN : 0 < N) (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1)
    (hε : 1 / (N : ℝ) < ε) (hδ : 0 < δ)
    (hzero : ∀ k : J → ℤ, (∀ j, |k j| ≤ (N : ℤ)) →
      (∑ j, (k j : ℝ) * g j) = 0 → Real.cos (∑ j, (k j : ℝ) * θ j) = 1)
    (hgap : ∀ k : J → ℤ, (∀ j, |k j| ≤ (N : ℤ)) →
      (∑ j, (k j : ℝ) * g j) ≠ 0 → δ ≤ |∑ j, (k j : ℝ) * g j|)
    (hbudget : R * δ * (ε - 1 / (N : ℝ)) >
      2 * (ε * (N : ℝ) ^ Fintype.card J - (ε - 1 / (N : ℝ)))) :
    ∃ t ∈ Icc a (a + R), phaseLoss g θ p t < ε := by
  classical
  let s := frequencyBox (J := J) N
  let c := weights N ε p
  let ξ := modeFrequency g
  let φ := modeFrequency θ
  have hc (k : J → ℤ) (hk : k ∈ s) : 0 ≤ c k :=
    weights_nonneg hN hp hε (mem_frequencyBox.mp hk)
  have ho : (0 : J → ℤ) ∈ s := mem_frequencyBox.mpr (by simp)
  have hξo : ξ 0 = 0 := by simp [ξ, modeFrequency]
  have hc0 : c 0 = ε - 1 / (N : ℝ) := by
    have hcast : (N : ℤ) ≠ 0 := by positivity
    simp [c, weights, triangle, correction, edge, hN.ne', Ne.symm hcast]
  have hmass : ∑ k ∈ s, c k = ε * (N : ℝ) ^ Fintype.card J := weights_mass hN ε p hpsum
  have hmass0 : c 0 ≤ ∑ k ∈ s, c k := Finset.single_le_sum hc ho
  have hbudget0 : 0 < R * δ * (ε - 1 / (N : ℝ)) := by linarith
  have hR : 0 < R := pos_of_mul_pos_left
    (pos_of_mul_pos_left hbudget0 (sub_nonneg.mpr hε.le)) hδ.le
  have hres : ε - 1 / (N : ℝ) ≤ resonantMass s c ξ φ := by
    unfold resonantMass
    rw [← hc0]
    have hcompat (k : J → ℤ) (hk : k ∈ s.filter (fun k => ξ k = 0)) :
        0 ≤ c k * Real.cos (φ k) := by
      obtain ⟨hks, hξk⟩ := Finset.mem_filter.mp hk
      have hcos : Real.cos (φ k) = 1 := hzero k (mem_frequencyBox.mp hks) hξk
      rw [hcos, mul_one]
      exact hc k hks
    calc
      c 0 = c 0 * Real.cos (φ 0) := by simp [φ, modeFrequency]
      _ ≤ _ := Finset.single_le_sum hcompat (Finset.mem_filter.mpr ⟨ho, hξo⟩)
  have hpenalty : sincPenalty s c ξ R ≤
      2 * (ε * (N : ℝ) ^ Fintype.card J - (ε - 1 / (N : ℝ))) / δ := by
    unfold sincPenalty
    calc
      _ ≤ ∑ k ∈ s.filter (fun k => ξ k ≠ 0), c k * (2 / δ) := by
        apply Finset.sum_le_sum
        intro k hk
        obtain ⟨hks, hξk⟩ := Finset.mem_filter.mp hk
        apply mul_le_mul_of_nonneg_left _ (hc k hks)
        exact (sincBound_le_reciprocal R (ξ k)).trans
          (div_le_div_of_nonneg_left (by norm_num) hδ (hgap k (mem_frequencyBox.mp hks) hξk))
      _ ≤ ∑ k ∈ s.erase 0, c k * (2 / δ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          obtain ⟨hks, hξk⟩ := Finset.mem_filter.mp hk
          exact Finset.mem_erase.mpr ⟨fun h => hξk (h ▸ hξo), hks⟩
        · intro k hk _
          exact mul_nonneg (hc k (Finset.mem_of_mem_erase hk)) (by positivity)
      _ = _ := by
        rw [← Finset.sum_mul, ← hmass, ← hc0, ← Finset.sum_erase_add s c ho]
        ring
  have hmargin : 0 < recurrenceMargin g θ p N ε R := by
    change 0 < R * resonantMass s c ξ φ - sincPenalty s c ξ R
    have hbudget' : 2 * (ε * (N : ℝ) ^ Fintype.card J - (ε - 1 / (N : ℝ))) / δ <
        R * (ε - 1 / (N : ℝ)) := (div_lt_iff₀ hδ).2 (by
      calc
        _ < R * δ * (ε - 1 / (N : ℝ)) := hbudget
        _ = _ := by ring)
    exact sub_pos.mpr (hpenalty.trans_lt (hbudget'.trans_le (mul_le_mul_of_nonneg_left hres hR.le)))
  obtain ⟨t, ht, hloss⟩ :=
    weighted_phase_recurrence_of_margin g θ p N ε a R hN hp hpsum hε hR hmargin
  exact ⟨t, ht, hloss.trans_lt (sub_lt_self _ (by positivity))⟩

end

end D5.S3.Fourier.WeightedPhaseRecurrence
