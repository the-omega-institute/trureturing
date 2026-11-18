/- GID: D5/S3/Arith/Robin/Analytic/OmegaTail/Truncation
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaTail/Truncation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact normalized profiles approximate density mass, moment and entropy. -/

import D5.S3.Arith.Robin.Analytic.OmegaTail.Density

/-! Compact selection profiles obtained by horizontal rescaling. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter MeasureTheory Set
open scoped Topology

namespace D5.S3.Arith.Robin.Analytic.OmegaTail.Truncation

open D5.S3.Arith.Robin.Analytic.OmegaTail.Density

private def lo (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
private def hi (n : ℕ) : ℝ := (n : ℝ) + 1
private def window (n : ℕ) : Set ℝ := Ioc (lo n) (hi n)

private lemma lo_pos (n : ℕ) : 0 < lo n := by unfold lo; positivity

private lemma windows_mono : Monotone window := by
  intro n m hnm u hu
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have hl : lo m ≤ lo n := by
    exact one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (n : ℝ) + 1) (by linarith)
  exact ⟨hl.trans_lt hu.1, hu.2.trans (by dsimp [hi]; linarith)⟩

private lemma windows_union : (⋃ n, window n) = Ioi (0 : ℝ) := by
  ext u
  constructor
  · intro hu
    obtain ⟨n, hn⟩ := mem_iUnion.mp hu
    exact (lo_pos n).trans hn.1
  · intro hu
    obtain ⟨n, hn⟩ := exists_nat_gt (max u (1 / u))
    have hnu : u < (n : ℝ) := (le_max_left _ _).trans_lt hn
    have hni : 1 / u < (n : ℝ) := (le_max_right _ _).trans_lt hn
    refine mem_iUnion.mpr ⟨n, ?_⟩
    constructor
    · dsimp [lo]
      exact (div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr (by
        have h := (div_lt_iff₀ hu).mp hni
        nlinarith)
    · dsimp [hi]
      linarith

private theorem window_integral_tendsto {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) :
    Tendsto (fun n : ℕ => ∫ u in window n, f u) atTop (𝓝 (∫ u in Ioi (0 : ℝ), f u)) := by
  have h := tendsto_setIntegral_of_monotone (fun n : ℕ => measurableSet_Ioc)
    windows_mono (show IntegrableOn f (⋃ n, window n) from windows_union.symm ▸ hf)
  change Tendsto (fun n : ℕ => ∫ u in window n, f u) atTop
    (𝓝 (∫ u in ⋃ n, window n, f u)) at h
  rw [windows_union] at h
  exact h

private theorem normalized_window_limits {s : ℝ} (hs : 1 < s) :
    let M : ℕ → ℝ := fun n => ∫ u in window n, q s u
    Tendsto M atTop (𝓝 1) ∧
      Tendsto (fun n => -log (M n) + (∫ u in window n, q s u * log u) / M n)
        atTop (𝓝 (log (D5.S3.Arith.Robin.Analytic.OmegaTailUpper.a s) -
          (π / s) * cos (π / s) / sin (π / s))) ∧
      Tendsto (fun n => (∫ u in window n, binEntropy (q s u)) / M n)
        atTop (𝓝 (s - π * cos (π / s) / sin (π / s))) := by
  dsimp only
  have hM := window_integral_tendsto (q_mass hs).1
  rw [(q_mass hs).2] at hM
  have hlog := window_integral_tendsto (q_log_moment hs).1
  rw [(q_log_moment hs).2] at hlog
  have hent := window_integral_tendsto (q_entropy hs).1
  rw [(q_entropy hs).2] at hent
  refine ⟨hM, ?_, ?_⟩
  · simpa only [log_one, neg_zero, zero_add, div_one, Pi.div_apply, Pi.neg_apply, Pi.add_apply] using
      (hM.log (by norm_num)).neg.add (hlog.div hM (by norm_num))
  · have ht := hent.div hM (by norm_num)
    change Tendsto (fun n => (∫ u in window n, binEntropy (q s u)) /
      (∫ u in window n, q s u)) atTop
      (𝓝 ((s - π * cos (π / s) / sin (π / s)) / 1)) at ht
    simpa only [div_one] using ht

private lemma scaled_integral (f : ℝ → ℝ) {a b M : ℝ} (hab : a ≤ b) (hM : 0 < M) :
    (∫ u in Ioc (a / M) (b / M), f (M * u)) =
      (∫ u in Ioc a b, f u) / M := by
  rw [← intervalIntegral.integral_of_le (div_le_div_of_nonneg_right hab hM.le),
    intervalIntegral.integral_comp_mul_left f hM.ne']
  rw [mul_div_cancel₀ _ hM.ne', mul_div_cancel₀ _ hM.ne',
    intervalIntegral.integral_of_le hab, smul_eq_mul]
  ring

/-- A horizontally rescaled compact restriction has prescribed approximate moments. -/
theorem compact_profile {s epsilon : ℝ} (hs : 1 < s) (hepsilon : 0 < epsilon) :
    ∃ (A B : ℝ) (g : ℝ → ℝ),
      0 < A ∧ A < B ∧ ContinuousOn g (Icc A B) ∧
      (∀ u ∈ Icc A B, g u ∈ Ioo 0 1) ∧
      (∫ u in Ioc A B, g u) = 1 ∧
      |(∫ u in Ioc A B, g u * log u) -
        (log (D5.S3.Arith.Robin.Analytic.OmegaTailUpper.a s) -
          (π / s) * cos (π / s) / sin (π / s))| < epsilon ∧
      s - π * cos (π / s) / sin (π / s) - epsilon <
        ∫ u in Ioc A B, binEntropy (g u) := by
  let M : ℕ → ℝ := fun n => ∫ u in window n, q s u
  let J : ℕ → ℝ := fun n => ∫ u in window n, q s u * log u
  let E : ℕ → ℝ := fun n => ∫ u in window n, binEntropy (q s u)
  obtain ⟨hM, hJ, hE⟩ := normalized_window_limits hs
  change Tendsto M atTop (𝓝 1) at hM
  change Tendsto (fun n => -log (M n) + J n / M n) atTop _ at hJ
  change Tendsto (fun n => E n / M n) atTop _ at hE
  have hMpos := hM.eventually_const_lt (by norm_num : (0 : ℝ) < 1)
  have hJclose := (Metric.tendsto_nhds.mp hJ) epsilon hepsilon
  have hElarge := hE.eventually_const_lt (by linarith :
    s - π * cos (π / s) / sin (π / s) - epsilon <
      s - π * cos (π / s) / sin (π / s))
  obtain ⟨n, hn, hMn, hJn, hEn⟩ :=
    ((eventually_ge_atTop (1 : ℕ)).and (hMpos.and (hJclose.and hElarge))).exists
  have hlow : 0 < lo n := lo_pos n
  have hlh : lo n < hi n := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    dsimp [lo, hi]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    nlinarith
  let A : ℝ := lo n / M n
  let B : ℝ := hi n / M n
  let g : ℝ → ℝ := fun u => q s (M n * u)
  have hA : 0 < A := div_pos hlow hMn
  have hAB : A < B := (div_lt_div_iff_of_pos_right hMn).mpr hlh
  have hgcont : ContinuousOn g (Icc A B) := by
    apply (q_continuous hs).comp (continuous_const.mul continuous_id).continuousOn
    intro u hu
    exact mul_pos hMn (hA.trans_le hu.1)
  have hgrange : ∀ u ∈ Icc A B, g u ∈ Ioo 0 1 := by
    intro u hu
    exact q_range hs (mul_pos hMn (hA.trans_le hu.1))
  have hgmass : (∫ u in Ioc A B, g u) = 1 := by
    rw [scaled_integral (q s) hlh.le hMn]
    change M n / M n = 1
    exact div_self hMn.ne'
  have hgent : (∫ u in Ioc A B, binEntropy (g u)) = E n / M n := by
    exact scaled_integral (fun u => binEntropy (q s u)) hlh.le hMn
  have hglog : (∫ u in Ioc A B, g u * log u) = -log (M n) + J n / M n := by
    have hgint : IntegrableOn g (Ioc A B) := hgcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hglogcont : ContinuousOn (fun u => g u * log (M n * u)) (Icc A B) := by
      apply hgcont.mul
      exact ((continuous_const.mul continuous_id).continuousOn.log
        (fun u hu => ne_of_gt (mul_pos hMn (hA.trans_le hu.1))))
    have hglogint : IntegrableOn (fun u => g u * log (M n * u)) (Ioc A B) :=
      hglogcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hp : EqOn (fun u => g u * log u)
        (fun u => g u * log (M n * u) - log (M n) * g u) (Ioc A B) := by
      intro u hu
      change g u * log u = g u * log (M n * u) - log (M n) * g u
      rw [log_mul hMn.ne' (hA.trans hu.1).ne']
      ring
    rw [setIntegral_congr_fun measurableSet_Ioc (fun u hu => hp hu),
      integral_sub hglogint (hgint.const_mul _), integral_const_mul, hgmass]
    change (∫ u in Ioc (lo n / M n) (hi n / M n),
      (fun v => q s v * log v) (M n * u)) - log (M n) * 1 = _
    rw [scaled_integral (fun v => q s v * log v) hlh.le hMn]
    dsimp only [J, window]
    ring
  refine ⟨A, B, g, hA, hAB, hgcont, hgrange, hgmass, ?_, ?_⟩
  · rw [hglog]
    simpa only [Real.dist_eq] using hJn
  · rw [hgent]
    exact hEn

end D5.S3.Arith.Robin.Analytic.OmegaTail.Truncation
