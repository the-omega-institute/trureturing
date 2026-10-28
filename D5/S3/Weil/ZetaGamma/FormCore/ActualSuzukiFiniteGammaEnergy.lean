/- GID: D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFiniteGammaEnergy
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:analytic-source-domain-refutation)
   anchors: []
   utility: none
   digest: Unbounded finite Gamma energy under a strict physical moment cap. -/

import D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiFinitePhysicalFeature

noncomputable section

namespace D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiFiniteGammaEnergy

open _root_.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample

open MeasureTheory Set Filter
open scoped ENNReal FourierTransform Topology Function

private def finiteGammaEnergy (N : ℕ) (κ : ℝ) : ℝ :=
  ∫ ξ : ℝ, Symbol.gammaWeight ξ *
    ‖unitarySourceFourier (finiteCompressedProfile N κ) ξ‖ ^ 2

private def finiteScaledBand (κ : ℝ) (n : ℕ) : Set ℝ :=
  Icc ((frequency n - 1) / κ) ((frequency n + 1) / κ)

private theorem finiteScaledBand_mem {κ : ℝ} (hκ : 0 < κ) (n : ℕ)
    {ξ : ℝ} (hξ : ξ ∈ finiteScaledBand κ n) : κ * ξ ∈ positiveBand n := by
  have ha := (div_le_iff₀ hκ).mp hξ.1
  have hb := (le_div_iff₀ hκ).mp hξ.2
  change κ * ξ ∈ Icc (frequency n - 1) (frequency n + 1)
  constructor <;> nlinarith [ha, hb]

private theorem finiteScaledBands_disjoint {κ : ℝ} (hκ : 0 < κ) :
    Pairwise (Disjoint on finiteScaledBand κ) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro ξ hn hm
  exact Set.disjoint_left.mp (positiveBands_disjoint hnm)
    (finiteScaledBand_mem hκ n hn) (finiteScaledBand_mem hκ m hm)

private theorem finiteGammaEnergy_lower (N : ℕ) {κ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ((N + 1 : ℕ) : ℝ) * κ / (2048 * Real.pi * Symbol.domainConstant) ≤
      finiteGammaEnergy N κ := by
  let f : ℝ → ℝ := fun ξ => Symbol.gammaWeight ξ *
    ‖unitarySourceFourier (finiteCompressedProfile N κ) ξ‖ ^ 2
  let b : ℝ := κ / (2048 * Real.pi * Symbol.domainConstant)
  let d : ℝ := κ ^ 2 / (4096 * Real.pi * Symbol.domainConstant)
  have hC : 0 < Symbol.domainConstant := by unfold Symbol.domainConstant; positivity
  have hf : Integrable f volume := finiteCompressed_gamma_integrable N hκ
  have hf0 (ξ : ℝ) : 0 ≤ f ξ := by
    have hp := (Symbol.actualGammaWeight_bounds ξ).1
    exact mul_nonneg (by linarith [hp]) (sq_nonneg _)
  have hband (n : ℕ) (hn : n ∈ Finset.range (N + 1)) :
      b ≤ ∫ ξ : ℝ in finiteScaledBand κ n, f ξ := by
    have hpoint (ξ : ℝ) (hξ : ξ ∈ finiteScaledBand κ n) : d ≤ f ξ := by
      have hl := finiteCompressed_band_density_lower N n hn hκ hκ1
        (finiteScaledBand_mem hκ n hξ)
      have hc := mul_le_mul_of_nonneg_right
        (Symbol.actualGammaWeight_bounds ξ).2
        (sq_nonneg ‖unitarySourceFourier (finiteCompressedProfile N κ) ξ‖)
      dsimp [d, f]
      apply (div_le_iff₀ (by positivity : 0 < 4096 * Real.pi * Symbol.domainConstant)).mpr
      have hmul := mul_le_mul_of_nonneg_left (hl.trans (by simpa only [mul_assoc] using hc))
        (show 0 ≤ 4096 * Real.pi by positivity)
      field_simp [Real.pi_ne_zero] at hmul
      nlinarith [hmul]
    calc
      b = ∫ ξ : ℝ in finiteScaledBand κ n, d := by
        rw [setIntegral_const, finiteScaledBand, Real.volume_real_Icc, smul_eq_mul]
        have hw : (frequency n + 1) / κ - (frequency n - 1) / κ = 2 / κ := by ring
        rw [hw, max_eq_left (by positivity)]
        dsimp [b, d]
        field_simp [hκ.ne', hC.ne', Real.pi_ne_zero] <;> ring
      _ ≤ ∫ ξ : ℝ in finiteScaledBand κ n, f ξ := by
        apply integral_mono_ae (integrableOn_const (by simp [finiteScaledBand, Real.volume_Icc]))
          hf.integrableOn
        filter_upwards [ae_restrict_mem measurableSet_Icc] with ξ hξ
        exact hpoint ξ hξ
  have hdis : Set.PairwiseDisjoint (↑(Finset.range (N + 1))) (finiteScaledBand κ) :=
    fun n hn m hm hnm => finiteScaledBands_disjoint hκ hnm
  have hsum := integral_biUnion_finset (Finset.range (N + 1))
    (fun n hn => (show MeasurableSet (finiteScaledBand κ n) from measurableSet_Icc))
    hdis (fun n hn => hf.integrableOn (s := finiteScaledBand κ n))
  calc
    ((N + 1 : ℕ) : ℝ) * κ / (2048 * Real.pi * Symbol.domainConstant) =
        ∑ n ∈ Finset.range (N + 1), b := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      dsimp [b]
      ring
    _ ≤ ∑ n ∈ Finset.range (N + 1), ∫ ξ : ℝ in finiteScaledBand κ n, f ξ :=
      Finset.sum_le_sum hband
    _ = ∫ ξ : ℝ in ⋃ n ∈ Finset.range (N + 1), finiteScaledBand κ n, f ξ := hsum.symm
    _ ≤ finiteGammaEnergy N κ :=
      integral_mono_measure Measure.restrict_le_self (Eventually.of_forall hf0) hf

private theorem finitePhysical_H6_tail (N : ℕ) {κ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    (∫ x : ℝ in Ioi Real.pi, (x / Real.pi) ^ (6 : ℕ) *
      ‖compressedFeature κ x - finitePhysicalFeature N κ x‖ ^ 2) ≤
        12288 * Real.pi * (1 / 4 : ℝ) ^ (N + 1) := by
  let f : ℝ → ℝ := fun x => (x / Real.pi) ^ (6 : ℕ) *
    ‖compressedFeature κ x - finitePhysicalFeature N κ x‖ ^ 2
  let r : ℝ := (1 / 2 : ℝ) ^ (N + 1)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hz (x : ℝ) (hx : x ∉ Icc Real.pi (4 * Real.pi)) : f x = 0 := by
    by_cases hπ : Real.pi ≤ x
    · have hh : 4 * Real.pi ≤ x := by
        by_contra h
        exact hx ⟨hπ, le_of_lt (lt_of_not_ge h)⟩
      simp only [f, compressedFeature_zero_high hκ hκ1 hh,
        finitePhysical_zero_high N hκ hκ1 hh, sub_self, norm_zero,
        zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    · simp only [f, compressedFeature, finitePhysicalFeature, sourceOfProfile,
        if_neg hπ, sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
  have hc : Continuous f := by
    dsimp [f]
    exact ((continuous_id.div_const Real.pi).pow 6).mul
      (((compressedFeature_continuous hκ).sub
        (finitePhysical_continuous N hκ)).norm.pow 2)
  have hs : HasCompactSupport f := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := Real.pi) (b := 4 * Real.pi))
    intro x hx
    by_contra h
    exact hx (hz x h)
  have hi : Integrable f volume := hc.integrable_of_hasCompactSupport hs
  have hf0 (x : ℝ) : 0 ≤ f x := by dsimp [f]; positivity
  have heq : (∫ x : ℝ in Icc Real.pi (4 * Real.pi), f x) = ∫ x : ℝ, f x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hz
  have hpoint (x : ℝ) (hx : x ∈ Icc Real.pi (4 * Real.pi)) :
      f x ≤ 4096 * r ^ 2 := by
    have ha : 0 ≤ x / Real.pi := div_nonneg (le_trans Real.pi_pos.le hx.1) Real.pi_pos.le
    have hb : x / Real.pi ≤ 4 := (div_le_iff₀ Real.pi_pos).mpr hx.2
    have hw : (x / Real.pi) ^ (6 : ℕ) ≤ 4096 := by
      have h := pow_le_pow_left₀ ha hb 6
      norm_num at h
      exact h
    have ht := finitePhysical_uniform_tail N hκ x
    have ht2 := pow_le_pow_left₀
      (norm_nonneg (compressedFeature κ x - finitePhysicalFeature N κ x)) ht 2
    exact mul_le_mul hw ht2 (sq_nonneg _) (by norm_num)
  have hr2 : r ^ 2 = (1 / 4 : ℝ) ^ (N + 1) := by
    dsimp [r]
    calc
      ((1 / 2 : ℝ) ^ (N + 1)) ^ 2 = ((1 / 2 : ℝ) ^ 2) ^ (N + 1) := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm (N + 1) 2]
      _ = (1 / 4 : ℝ) ^ (N + 1) := by norm_num
  change (∫ x : ℝ in Ioi Real.pi, f x) ≤ _
  calc
    (∫ x : ℝ in Ioi Real.pi, f x) ≤ ∫ x : ℝ, f x :=
      integral_mono_measure Measure.restrict_le_self (Eventually.of_forall hf0) hi
    _ = ∫ x : ℝ in Icc Real.pi (4 * Real.pi), f x := heq.symm
    _ ≤ ∫ x : ℝ in Icc Real.pi (4 * Real.pi), 4096 * r ^ 2 := by
      apply integral_mono_ae hi.integrableOn
        (integrableOn_const (by simp [Real.volume_Icc]))
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact hpoint x hx
    _ = 12288 * Real.pi * (1 / 4 : ℝ) ^ (N + 1) := by
      rw [setIntegral_const, Real.volume_real_Icc, smul_eq_mul,
        max_eq_left (by linarith [Real.pi_pos]), hr2]
      ring

private theorem finitePhysical_H6_convergence {κ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    Tendsto (fun N : ℕ => ∫ x : ℝ in Ioi Real.pi,
      (x / Real.pi) ^ (6 : ℕ) *
        ‖compressedFeature κ x - finitePhysicalFeature N κ x‖ ^ 2)
      atTop (𝓝 0) := by
  have ht : Tendsto (fun N : ℕ => 12288 * Real.pi * (1 / 4 : ℝ) ^ (N + 1))
      atTop (𝓝 0) := by
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)
    simpa only [pow_succ, mul_zero, zero_mul] using
      (hpow.mul_const (1 / 4 : ℝ)).const_mul (12288 * Real.pi)
  apply squeeze_zero _ (fun N => finitePhysical_H6_tail N hκ hκ1) ht
  intro N
  apply integral_nonneg
  intro x
  positivity

/-- Finite actual Gamma energy has no upper bound relative to physical mass
inside any strict original H6 moment cap. Every witness belongs to every
constant-shift form domain. The same finite sources converge in actual H6
to a source outside every admissible constant-shift form domain. -/
theorem actual_h6_finite_gamma_energy_unbounded (K B : ℝ) (hK : 1 < K) :
    ∃ F : ℝ → ℂ,
      originalPhysicalH6 F ∧
      (∀ x : ℝ, (F x).im = 0) ∧
      (∀ x : ℝ, Real.pi ≤ x → HasSum (fun k : ℕ => physicalTerm F k x) (F x)) ∧
      (∀ c : ℝ, originalGammaFormDomain c F) ∧
      (0 < ∫ x : ℝ in Ioi Real.pi, ‖F x‖ ^ 2) ∧
      ((∫ x : ℝ in Ioi Real.pi, (x / Real.pi) ^ (6 : ℕ) * ‖F x‖ ^ 2) <
        K * (∫ x : ℝ in Ioi Real.pi, ‖F x‖ ^ 2)) ∧
      (B * (∫ x : ℝ in Ioi Real.pi, ‖F x‖ ^ 2) <
        ∫ ξ : ℝ, Symbol.gammaWeight ξ *
          ‖unitarySourceFourier (actualGammaProfile F) ξ‖ ^ 2) ∧
      ∃ (F_limit : ℝ → ℂ) (G : ℕ → ℝ → ℂ),
        originalPhysicalH6 F_limit ∧
        (∀ c : ℝ, (∀ ξ : ℝ, 1 ≤ Symbol.gammaWeight ξ + c) →
          ¬ originalGammaFormDomain c F_limit) ∧
        (∀ n : ℕ, originalPhysicalH6 (G n) ∧
          (∀ x : ℝ, (G n x).im = 0) ∧
          (∀ x : ℝ, Real.pi ≤ x →
            HasSum (fun k : ℕ => physicalTerm (G n) k x) (G n x)) ∧
          (∀ c : ℝ, originalGammaFormDomain c (G n)) ∧
          (0 < ∫ x : ℝ in Ioi Real.pi, ‖G n x‖ ^ 2) ∧
          ((∫ x : ℝ in Ioi Real.pi, (x / Real.pi) ^ (6 : ℕ) * ‖G n x‖ ^ 2) <
            K * (∫ x : ℝ in Ioi Real.pi, ‖G n x‖ ^ 2))) ∧
        (∃ n : ℕ, F = G n) ∧
        Tendsto (fun n : ℕ => ∫ x : ℝ in Ioi Real.pi,
          (x / Real.pi) ^ (6 : ℕ) * ‖F_limit x - G n x‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨κ, hk, hkc, hkK⟩ := exists_cap_compression K hK
  have hk1 : κ ≤ 1 := by linarith
  have hC : 0 < Symbol.domainConstant := by unfold Symbol.domainConstant; positivity
  let D : ℝ := 2048 * Real.pi * Symbol.domainConstant
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (max B 0 * (3 * Real.pi) * D / κ)
  have hNenergy : max B 0 * (3 * Real.pi) <
      ((N + 1 : ℕ) : ℝ) * κ / D := by
    have hm := (div_lt_iff₀ hk).mp hN
    apply (lt_div_iff₀ hD).mpr
    push_cast
    nlinarith [hm]
  have hmass := finitePhysical_mass_pos N hk
  have hupper := finitePhysical_mass_upper N hk hk1
  have henergy : B * (∫ x : ℝ in Ioi Real.pi, ‖finitePhysicalFeature N κ x‖ ^ 2) <
      finiteGammaEnergy N κ := by
    calc
      B * (∫ x : ℝ in Ioi Real.pi, ‖finitePhysicalFeature N κ x‖ ^ 2) ≤
          max B 0 * (∫ x : ℝ in Ioi Real.pi, ‖finitePhysicalFeature N κ x‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hmass.le
      _ ≤ max B 0 * (3 * Real.pi) :=
        mul_le_mul_of_nonneg_left hupper (le_max_right _ _)
      _ < ((N + 1 : ℕ) : ℝ) * κ / D := hNenergy
      _ ≤ finiteGammaEnergy N κ := finiteGammaEnergy_lower N hk hk1
  refine ⟨finitePhysicalFeature N κ, finitePhysical_h6 N hk,
    finitePhysical_real N κ, ?_, ?_, hmass, ?_, ?_, ?_⟩
  · intro x hx
    exact finitePhysical_fullHasSum N hk hk1 hx
  · intro c
    exact finitePhysical_in_all_shift_domains N hk hk1 c
  · exact lt_of_le_of_lt (finitePhysical_cap_bound N hk)
      (mul_lt_mul_of_pos_right hkK hmass)
  · rw [finitePhysical_actualProfile_eq N hk hk1]
    exact henergy
  · refine ⟨compressedFeature κ, (fun n => finitePhysicalFeature n κ),
      compressed_original_h6 hk, ?_, ?_, ⟨N, rfl⟩, finitePhysical_H6_convergence hk hk1⟩
    · intro c hc
      exact compressed_not_form_domain hk hk1 c hc
    · intro n
      have hn_mass := finitePhysical_mass_pos n hk
      exact ⟨finitePhysical_h6 n hk, finitePhysical_real n κ,
        fun x hx => finitePhysical_fullHasSum n hk hk1 hx,
        fun c => finitePhysical_in_all_shift_domains n hk hk1 c,
        hn_mass, lt_of_le_of_lt (finitePhysical_cap_bound n hk)
          (mul_lt_mul_of_pos_right hkK hn_mass)⟩

end D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiFiniteGammaEnergy
