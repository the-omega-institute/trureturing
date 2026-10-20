/- GID: D5/S3/Weil/BurnolGram/SameWindowSmoothCutoff
   generality: I
   mirror-B: D5/B/S3/Weil/BurnolGram/SameWindowSmoothCutoff
   mirror-E: none(waiver:analytic-same-window-approximation)
   anchors: []
   utility: none
   digest: Construct same-window smooth even tests with plateau, variation and L1 error bounds. -/

import D5.S3.Weil.BurnolGram.FiniteBoxWeilMollifier

/-!
# Smooth cutoff inside the original window

A box of radius a-3h/2 averaged against a unit-mass smooth seed of radius
h/2 has support in [-a+h,a-h] and is one on [-a+2h,a-2h]. The box is
not itself a Weil test; its smooth convolution is. Multiplication by any
smooth even function therefore gives an actual test in the same window.

The first derivative of the cutoff has L1 norm at most two, independently
of h. A function bounded by M on the original window incurs L1 error at
most 4Mh. This is an unweighted boundary-layer estimate; convergence in a
logarithmically weighted Fourier norm requires a separate Fourier estimate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.BurnolGram.SameWindowSmoothCutoff

open Set MeasureTheory Function
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.InterpolationJets.QuantitativeEvenSeed
open D5.S3.Weil.BurnolGram.FiniteBoxWeilMollifier
open scoped ContDiff

/-- An unnormalized smooth box with a boundary layer of width h. -/
def sameWindowCutoff (a h : ℝ) (hh : 0 < h) : WeilTestFunction where
  toFun x := ((2 * (a - 3 * h / 2) : ℝ) : ℂ) *
    boxMean (a - 3 * h / 2) (normalizedEvenSeed (h / 2) (by positivity)) x
  contDiff' := contDiff_const.mul
    (boxMean (a - 3 * h / 2) (normalizedEvenSeed (h / 2) (by positivity))).contDiff
  hasCompactSupport' :=
    (boxMean (a - 3 * h / 2)
      (normalizedEvenSeed (h / 2) (by positivity))).hasCompactSupport.mul_left
  even' x := by
    rw [(boxMean (a - 3 * h / 2)
      (normalizedEvenSeed (h / 2) (by positivity))).even x]

/-- Multiply the cutoff by a smooth even function, which need not have
compact support before multiplication. -/
def sameWindowSmoothTrial (a h : ℝ) (hh : 0 < h) (p : ℝ → ℂ)
    (hp : ContDiff ℝ ∞ p) (heven : ∀ x, p (-x) = p x) : WeilTestFunction where
  toFun x := sameWindowCutoff a h hh x * p x
  contDiff' := (sameWindowCutoff a h hh).contDiff.mul hp
  hasCompactSupport' := (sameWindowCutoff a h hh).hasCompactSupport.mul_right
  even' x := by rw [(sameWindowCutoff a h hh).even x, heven x]

private theorem cutoff_integral (a h : ℝ) (hh : 0 < h) (ha : 4 * h ≤ a)
    (x : ℝ) :
    sameWindowCutoff a h hh x =
      ∫ t in Icc (-(a - 3 * h / 2)) (a - 3 * h / 2),
        normalizedEvenSeed (h / 2) (by positivity) (x - t) := by
  let b := a - 3 * h / 2
  have hb : 0 < b := by dsimp [b]; linarith
  have hc : ((2 * b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (mul_pos (by norm_num) hb).ne'
  change ((2 * b : ℝ) : ℂ) *
    (∫ t : ℝ, boxDensity b t * normalizedEvenSeed (h / 2) (by positivity) (x - t)) =
      ∫ t in Icc (-b) b, normalizedEvenSeed (h / 2) (by positivity) (x - t)
  rw [← integral_const_mul, ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  by_cases ht : t ∈ Icc (-b) b
  · simp only [boxDensity, indicator_of_mem ht]
    exact mul_inv_cancel_left₀ hc _
  · simp [boxDensity, ht]

private theorem cutoff_tsupport (a h : ℝ) (hh : 0 < h) :
    tsupport (sameWindowCutoff a h hh : ℝ → ℂ) ⊆ Icc (-a + h) (a - h) := by
  have hs := boxMean_tsupport (a - 3 * h / 2) (h / 2)
    (normalizedEvenSeed (h / 2) (by positivity)) (normalizedEvenSeed_tsupport _ _)
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hn : boxMean (a - 3 * h / 2)
      (normalizedEvenSeed (h / 2) (by positivity)) x ≠ 0 := by
    intro hz
    exact hx (by change ((2 * (a - 3 * h / 2) : ℝ) : ℂ) * _ = 0; rw [hz, mul_zero])
  have hi := hs (subset_tsupport _ hn)
  exact ⟨by linarith [hi.1], by linarith [hi.2]⟩

private theorem cutoff_plateau (a h : ℝ) (hh : 0 < h) (ha : 4 * h ≤ a)
    (x : ℝ) (hx : x ∈ Icc (-a + 2 * h) (a - 2 * h)) :
    sameWindowCutoff a h hh x = 1 := by
  let g := normalizedEvenSeed (h / 2) (by positivity : 0 < h / 2)
  have hfun : (Icc (-(a - 3 * h / 2)) (a - 3 * h / 2)).indicator
      (fun t : ℝ => g (x - t)) = fun t : ℝ => g (x - t) := by
    funext t
    by_cases ht : t ∈ Icc (-(a - 3 * h / 2)) (a - 3 * h / 2)
    · rw [indicator_of_mem ht]
    · have hz : g (x - t) = 0 := by
        by_contra hn
        have hs := normalizedEvenSeed_tsupport (h / 2) (by positivity)
          (subset_tsupport (g : ℝ → ℂ) hn)
        apply ht
        exact ⟨by linarith [hx.1, hs.2], by linarith [hx.2, hs.1]⟩
      rw [indicator_of_notMem ht, hz]
  rw [cutoff_integral a h hh ha, ← integral_indicator measurableSet_Icc]
  change (∫ t : ℝ, (Icc (-(a - 3 * h / 2)) (a - 3 * h / 2)).indicator
    (fun t : ℝ => g (x - t)) t) = 1
  rw [hfun, integral_sub_left_eq_self (g : ℝ → ℂ) volume x]
  exact normalizedEvenSeed_integral _ _

private theorem cutoff_complement_norm (a h : ℝ) (hh : 0 < h) (ha : 4 * h ≤ a)
    (x : ℝ) : ‖1 - sameWindowCutoff a h hh x‖ ≤ 1 := by
  let g := normalizedEvenSeed (h / 2) (by positivity : 0 < h / 2)
  let s := Icc (-(a - 3 * h / 2)) (a - 3 * h / 2)
  have hi : Integrable (fun t : ℝ => g (x - t)) := g.integrable.comp_sub_left x
  have hmass : (∫ t : ℝ, g (x - t)) = 1 := by
    rw [integral_sub_left_eq_self (g : ℝ → ℂ) volume x]
    exact normalizedEvenSeed_integral _ _
  have heq : 1 - sameWindowCutoff a h hh x = ∫ t in sᶜ, g (x - t) := by
    rw [setIntegral_compl measurableSet_Icc hi, hmass, cutoff_integral a h hh ha]
  rw [heq]
  calc
    _ ≤ ∫ t in sᶜ, ‖g (x - t)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, ‖g (x - t)‖ :=
      setIntegral_le_integral hi.norm (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    _ = 1 := by
      rw [integral_sub_left_eq_self (fun t : ℝ => ‖g t‖) volume x]
      exact normalizedEvenSeed_norm_integral _ _

private theorem cutoff_derivative_L1 (a h : ℝ) (hh : 0 < h) (ha : 4 * h ≤ a) :
    (∫ x : ℝ, ‖deriv (sameWindowCutoff a h hh : ℝ → ℂ) x‖) ≤ 2 := by
  let b := a - 3 * h / 2
  let g := normalizedEvenSeed (h / 2) (by positivity : 0 < h / 2)
  have hb : 0 < b := by dsimp [b]; linarith
  have hd (x : ℝ) : deriv (sameWindowCutoff a h hh : ℝ → ℂ) x =
      ((2 * b : ℝ) : ℂ) * deriv (boxMean b g : ℝ → ℂ) x := by
    exact deriv_const_mul _ ((boxMean b g).contDiff.differentiable (by simp) x)
  have hbudget := boxIterate_derivative_L1_budget b hb g 1 1 (by omega)
  have hbudget' : (∫ x : ℝ, ‖deriv (boxMean b g : ℝ → ℂ) x‖) ≤ b⁻¹ := by
    simpa only [boxIterate, Function.iterate_one, g, pow_one,
      normalizedEvenSeed_norm_integral, mul_one] using hbudget
  have hnorm : ‖((2 * b : ℝ) : ℂ)‖ = 2 * b := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  simp_rw [hd, norm_mul, hnorm]
  rw [integral_const_mul]
  calc
    _ ≤ (2 * b) * b⁻¹ := mul_le_mul_of_nonneg_left hbudget' (by positivity)
    _ = 2 := by field_simp [hb.ne']

/-- The central plateau and the boundary variation are controlled inside
the original window; multiplying by p produces an actual admissible test. -/
theorem sameWindowSmoothTrial_budget (a h : ℝ) (hh : 0 < h) (ha : 4 * h ≤ a)
    (p : ℝ → ℂ) (hp : ContDiff ℝ ∞ p) (heven : ∀ x, p (-x) = p x) :
    tsupport (sameWindowSmoothTrial a h hh p hp heven : ℝ → ℂ) ⊆
        Icc (-a + h) (a - h) ∧
      (∀ x ∈ Icc (-a + 2 * h) (a - 2 * h),
        sameWindowSmoothTrial a h hh p hp heven x = p x) ∧
      (∀ x, ‖1 - sameWindowCutoff a h hh x‖ ≤ 1) ∧
      (∫ x : ℝ, ‖deriv (sameWindowCutoff a h hh : ℝ → ℂ) x‖) ≤ 2 := by
  refine ⟨?_, ?_, cutoff_complement_norm a h hh ha, cutoff_derivative_L1 a h hh ha⟩
  · apply closure_minimal _ isClosed_Icc
    intro x hx
    have hn : sameWindowCutoff a h hh x ≠ 0 := by
      intro hz
      exact hx (by change sameWindowCutoff a h hh x * p x = 0; rw [hz, zero_mul])
    exact cutoff_tsupport a h hh (subset_tsupport _ hn)
  · intro x hx
    change sameWindowCutoff a h hh x * p x = p x
    rw [cutoff_plateau a h hh ha x hx, one_mul]

/-- Only the two boundary strips contribute to the L1 error. Their total
length is 4h, and the complementary cutoff is a contraction. -/
theorem sameWindowSmoothTrial_L1_error_le (a h M : ℝ) (hh : 0 < h)
    (ha : 4 * h ≤ a) (hM : 0 ≤ M) (p : ℝ → ℂ)
    (hp : ContDiff ℝ ∞ p) (heven : ∀ x, p (-x) = p x)
    (hbound : ∀ x ∈ Icc (-a) a, ‖p x‖ ≤ M) :
    (∫ x : ℝ, ‖(Ioo (-a) a).indicator p x -
      sameWindowSmoothTrial a h hh p hp heven x‖) ≤ 4 * M * h := by
  obtain ⟨hs, hplateau, hc, _⟩ := sameWindowSmoothTrial_budget a h hh ha p hp heven
  let e : ℝ → ℂ := fun x => (Ioo (-a) a).indicator p x -
    sameWindowSmoothTrial a h hh p hp heven x
  let left := Icc (-a) (-a + 2 * h)
  let right := Icc (a - 2 * h) a
  let bound : ℝ → ℝ := fun x => left.indicator (fun _ => M) x +
    right.indicator (fun _ => M) x
  have hei : Integrable e :=
    ((hp.continuous.integrableOn_Icc.mono_set Ioo_subset_Icc_self).integrable_indicator
      measurableSet_Ioo).sub (sameWindowSmoothTrial a h hh p hp heven).integrable
  have hli : Integrable (left.indicator (fun _ : ℝ => M)) :=
    (integrableOn_const (μ := volume) (s := left) (C := M)
      isCompact_Icc.measure_ne_top).integrable_indicator
      measurableSet_Icc
  have hri : Integrable (right.indicator (fun _ : ℝ => M)) :=
    (integrableOn_const (μ := volume) (s := right) (C := M)
      isCompact_Icc.measure_ne_top).integrable_indicator
      measurableSet_Icc
  have hpoint (x : ℝ) : ‖e x‖ ≤ bound x := by
    by_cases hx : x ∈ Ioo (-a) a
    · have hb : ‖e x‖ ≤ M := by
        have heq : e x = (1 - sameWindowCutoff a h hh x) * p x := by
          dsimp [e, sameWindowSmoothTrial]
          rw [indicator_of_mem hx]
          change p x - sameWindowCutoff a h hh x * p x =
            (1 - sameWindowCutoff a h hh x) * p x
          ring
        rw [heq, norm_mul]
        calc
          _ ≤ 1 * ‖p x‖ := mul_le_mul_of_nonneg_right (hc x) (norm_nonneg _)
          _ ≤ M := by simpa using hbound x ⟨hx.1.le, hx.2.le⟩
      by_cases hl : x ∈ left
      · by_cases hr : x ∈ right <;> simp [bound, hl, hr] <;> linarith
      · by_cases hr : x ∈ right
        · simpa [bound, hl, hr] using hb
        · have hi : x ∈ Icc (-a + 2 * h) (a - 2 * h) := by
            have hl' : ¬ (-a ≤ x ∧ x ≤ -a + 2 * h) := hl
            have hr' : ¬ (a - 2 * h ≤ x ∧ x ≤ a) := hr
            constructor
            · by_contra hn
              apply hl'
              exact ⟨hx.1.le, by linarith⟩
            · by_contra hn
              apply hr'
              exact ⟨by linarith, hx.2.le⟩
          have hz : e x = 0 := by simp [e, hx, hplateau x hi]
          simp [hz, bound, hl, hr]
    · have hz : sameWindowSmoothTrial a h hh p hp heven x = 0 := by
        by_contra hn
        have hi := hs (subset_tsupport _ hn)
        apply hx
        exact ⟨by linarith [hi.1], by linarith [hi.2]⟩
      have hez : e x = 0 := by simp [e, hx, hz]
      rw [hez, norm_zero]
      exact add_nonneg (by by_cases hl : x ∈ left <;> simp [hl, hM])
        (by by_cases hr : x ∈ right <;> simp [hr, hM])
  have hint (u v : ℝ) (huv : u ≤ v) :
      (∫ x : ℝ, (Icc u v).indicator (fun _ : ℝ => M) x) = (v - u) * M := by
    rw [integral_indicator measurableSet_Icc, setIntegral_const]
    simp only [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr huv),
      smul_eq_mul]
  calc
    _ = ∫ x : ℝ, ‖e x‖ := rfl
    _ ≤ ∫ x : ℝ, bound x := integral_mono hei.norm (hli.add hri) hpoint
    _ = 4 * M * h := by
      change (∫ x : ℝ, left.indicator (fun _ => M) x +
        right.indicator (fun _ => M) x) = 4 * M * h
      rw [integral_add hli hri, hint (-a) (-a + 2 * h) (by linarith),
        hint (a - 2 * h) a (by linarith)]
      ring

#print axioms sameWindowSmoothTrial_budget
#print axioms sameWindowSmoothTrial_L1_error_le

end D5.S3.Weil.BurnolGram.SameWindowSmoothCutoff
