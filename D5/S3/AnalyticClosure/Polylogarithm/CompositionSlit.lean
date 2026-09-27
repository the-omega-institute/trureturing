/- GID: D5/S3/AnalyticClosure/Polylogarithm/CompositionSlit
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/Polylogarithm/CompositionSlit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive-composition source continuation on the full slit domain. -/
import D5.S3.AnalyticClosure.Polylogarithm.CompositionContinuation
import Mathlib.Analysis.Complex.RemovableSingularity
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Complex MeasureTheory Metric Set Topology
open scoped Interval BigOperators ComplexConjugate
namespace D5.S3.AnalyticClosure.Polylogarithm.CompositionSlit
open CompositionDisk CompositionRecurrences CompositionContinuation
/-- The actual all-composition slit branch, including its source normalization.
This intermediate theorem asserts neither global nonvanishing nor Conjecture 1.3. -/
theorem result :
    continued [] = (fun _ => 1) ∧
    (∀ ks, AnalyticOnNhd ℂ (continued ks) omega ∧
      ∀ z, ‖z‖ < 1 → continued ks z = source ks z) ∧
    (∀ (head : ℕ+) tail, continued (head :: tail) 0 = 0 ∧
      analyticOrderAt (continued (head :: tail)) 0 = (depth tail : ℕ∞) ∧
      (∀ z, ‖z‖ < 1 → continued (head :: tail) z = strictNestedSeries head tail z) ∧
      ∀ z ∈ omega, continued (head :: tail) (conj z) = conj (continued (head :: tail) z)) ∧
    (∀ tail z, z ∈ omega → HasDerivAt (continued (1 :: tail))
      (continued tail z / (1 - z)) z) ∧
    (∀ (head : ℕ+) tail (hh : 1 < (head : ℕ)) z, z ∈ omega →
      HasDerivAt (continued (head :: tail))
        (if z = 0 then (if tail = [] then 1 else 0)
          else continued (⟨(head : ℕ) - 1, by omega⟩ :: tail) z / z) z) := by
  classical
  -- A17.2 local transplant; exact attribution and full license are in CompositionContinuation.
  have primitive : ∀ {U : Set ℂ} {f : ℂ → ℂ} {p : ℂ},
      IsOpen U → StarConvex ℝ p U → DifferentiableOn ℂ f U →
      ∀ {z : ℂ}, z ∈ U → HasDerivAt (starPrimitive p f) (f z) z := by
    intro U f p hU hSC hf z hz
    have hp : p ∈ U := hSC.mem ⟨z, hz⟩
    obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hU z hz
    set r' := r / 2 with hr'_def
    have hr'_pos : 0 < r' := half_pos hr_pos
    have h_cb_sub_U : Metric.closedBall z r' ⊆ U := fun w hw =>
      hr_sub (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hw)
        (half_lt_self hr_pos)))
    set s_nbhd := Metric.ball z r' with hs_nbhd_def
    have hs_mem : s_nbhd ∈ 𝓝 z := Metric.ball_mem_nhds z hr'_pos
    have hs_sub_cb : s_nbhd ⊆ Metric.closedBall z r' := Metric.ball_subset_closedBall
    have h_pt_in_U : ∀ w ∈ Metric.closedBall z r', ∀ t ∈ Set.Icc (0:ℝ) 1,
        p + (t : ℂ) * (w - p) ∈ U := by
      intro w hw t ht
      have hw_U := h_cb_sub_U hw
      apply hSC.segment_subset hw_U
      refine ⟨1 - t, t, by linarith [ht.2], ht.1, by linarith, ?_⟩
      simp only [Complex.real_smul]; push_cast; ring
    set K : Set ℂ := (fun wt : ℂ × ℝ => p + (wt.2 : ℂ) * (wt.1 - p)) ''
      (Metric.closedBall z r' ×ˢ Set.Icc (0:ℝ) 1) with hK_def
    have hK_compact : IsCompact K := by
      refine IsCompact.image ((isCompact_closedBall z r').prod isCompact_Icc) ?_
      fun_prop
    have hK_sub_U : K ⊆ U := by
      rintro _ ⟨⟨w, t⟩, ⟨hw, ht⟩, rfl⟩
      exact h_pt_in_U w hw t ht
    have h_pt_K : ∀ w ∈ Metric.closedBall z r', ∀ t ∈ Set.Icc (0:ℝ) 1,
        p + (t : ℂ) * (w - p) ∈ K := fun w hw t ht => ⟨⟨w, t⟩, ⟨hw, ht⟩, rfl⟩
    have hf_an : AnalyticOnNhd ℂ f U := hf.analyticOnNhd hU
    have hf_cont_U : ContinuousOn f U := hf.continuousOn
    have hf_cont_K : ContinuousOn f K := hf_cont_U.mono hK_sub_U
    have hdf_cont_U : ContinuousOn (deriv f) U := fun w hw =>
      ((hf_an w hw).deriv.continuousAt).continuousWithinAt
    have hdf_cont_K : ContinuousOn (deriv f) K := hdf_cont_U.mono hK_sub_U
    obtain ⟨Mf, hMf⟩ := hK_compact.exists_bound_of_continuousOn hf_cont_K
    obtain ⟨Mdf, hMdf⟩ := hK_compact.exists_bound_of_continuousOn hdf_cont_K
    set Bwp := ‖z - p‖ + r' with hBwp_def
    have hBwp_bd : ∀ w ∈ Metric.closedBall z r', ‖w - p‖ ≤ Bwp := by
      intro w hw
      have h_w_z : ‖w - z‖ ≤ r' := by rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hw
      calc ‖w - p‖ = ‖(w - z) + (z - p)‖ := by congr 1; ring
        _ ≤ ‖w - z‖ + ‖z - p‖ := norm_add_le _ _
        _ ≤ r' + ‖z - p‖ := by linarith
        _ = Bwp := by rw [hBwp_def]; ring
    have hMf_nn : 0 ≤ Mf := by
      have hp_in_K : p ∈ K := by
        have h1 : z ∈ Metric.closedBall z r' := Metric.mem_closedBall_self hr'_pos.le
        have h2 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := Set.left_mem_Icc.mpr (by norm_num)
        have h3 := h_pt_K z h1 0 h2
        have : p + ((0:ℝ):ℂ) * (z - p) = p := by push_cast; ring
        rwa [this] at h3
      exact le_trans (norm_nonneg _) (hMf p hp_in_K)
    have hMdf_nn : 0 ≤ Mdf := by
      have hp_in_K : p ∈ K := by
        have h1 : z ∈ Metric.closedBall z r' := Metric.mem_closedBall_self hr'_pos.le
        have h2 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := Set.left_mem_Icc.mpr (by norm_num)
        have h3 := h_pt_K z h1 0 h2
        have : p + ((0:ℝ):ℂ) * (z - p) = p := by push_cast; ring
        rwa [this] at h3
      exact le_trans (norm_nonneg _) (hMdf p hp_in_K)
    have hBwp_nn : 0 ≤ Bwp := add_nonneg (norm_nonneg _) hr'_pos.le
    set C := Mf + Bwp * Mdf with hC_def
    have hC_nn : 0 ≤ C := add_nonneg hMf_nn (mul_nonneg hBwp_nn hMdf_nn)
    set F : ℂ → ℝ → ℂ := fun w t => (w - p) * f (p + (t : ℂ) * (w - p)) with hF_def
    set F' : ℂ → ℝ → ℂ := fun w t =>
      f (p + (t : ℂ) * (w - p)) +
      (w - p) * (t : ℂ) * deriv f (p + (t : ℂ) * (w - p)) with hF'_def
    have h_pt_deriv : ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        t ∈ Set.uIoc (0:ℝ) 1 → ∀ w ∈ s_nbhd, HasDerivAt (fun w => F w t) (F' w t) w := by
      refine Filter.Eventually.of_forall ?_
      intro t ht w hw
      have ht_Icc : t ∈ Set.Icc (0:ℝ) 1 := by
        rw [show Set.uIoc (0:ℝ) 1 = Set.Ioc 0 1 from Set.uIoc_of_le (by norm_num)] at ht
        exact ⟨ht.1.le, ht.2⟩
      have hw_cb := hs_sub_cb hw
      have h_pt_w_in_U := h_pt_in_U w hw_cb t ht_Icc
      have h_id_sub : HasDerivAt (fun w : ℂ => w - p) 1 w := (hasDerivAt_id w).sub_const p
      have h_inner : HasDerivAt (fun w : ℂ => p + (t : ℂ) * (w - p)) (t : ℂ) w := by
        have h2 := h_id_sub.const_mul (t : ℂ)
        simpa using h2.const_add p
      have hf_at : HasDerivAt f (deriv f (p + (t : ℂ) * (w - p))) (p + (t : ℂ) * (w - p)) :=
        (hf.differentiableAt (hU.mem_nhds h_pt_w_in_U)).hasDerivAt
      have hf_at_inner : HasDerivAt f (deriv f (p + (t : ℂ) * (w - p)))
          ((fun w : ℂ => p + (t : ℂ) * (w - p)) w) := by simpa using hf_at
      have h_f_inner : HasDerivAt (fun w : ℂ => f (p + (t : ℂ) * (w - p)))
          ((t : ℂ) * deriv f (p + (t : ℂ) * (w - p))) w := by
        have h_c := HasDerivAt.comp w hf_at_inner h_inner
        simp only [Function.comp_def] at h_c
        rw [mul_comm]; exact h_c
      have h_prod := h_id_sub.mul h_f_inner
      have h_func_eq : (fun w : ℂ => F w t) = fun w : ℂ => (w - p) * f (p + (t : ℂ) * (w - p)) := by
        funext w; simp only [hF_def]
      have h_deriv_eq : F' w t = 1 * f (p + (t : ℂ) * (w - p)) +
          (w - p) * ((t : ℂ) * deriv f (p + (t : ℂ) * (w - p))) := by
        simp only [hF'_def]; ring
      rw [h_func_eq, h_deriv_eq]
      exact h_prod
    have h_bound : ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        t ∈ Set.uIoc (0:ℝ) 1 → ∀ w ∈ s_nbhd, ‖F' w t‖ ≤ C := by
      refine Filter.Eventually.of_forall ?_
      intro t ht w hw
      have ht_Icc : t ∈ Set.Icc (0:ℝ) 1 := by
        rw [show Set.uIoc (0:ℝ) 1 = Set.Ioc 0 1 from Set.uIoc_of_le (by norm_num)] at ht
        exact ⟨ht.1.le, ht.2⟩
      have hw_cb := hs_sub_cb hw
      have h_pt_K_wt := h_pt_K w hw_cb t ht_Icc
      have h_t_abs : ‖(t : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht_Icc.1]; exact ht_Icc.2
      have h_wp : ‖w - p‖ ≤ Bwp := hBwp_bd w hw_cb
      have h_f_bd : ‖f (p + (t : ℂ) * (w - p))‖ ≤ Mf := hMf _ h_pt_K_wt
      have h_df_bd : ‖deriv f (p + (t : ℂ) * (w - p))‖ ≤ Mdf := hMdf _ h_pt_K_wt
      calc ‖F' w t‖
          = ‖f (p + (t : ℂ) * (w - p)) +
              (w - p) * (t : ℂ) * deriv f (p + (t : ℂ) * (w - p))‖ := by rw [hF'_def]
        _ ≤ ‖f (p + (t : ℂ) * (w - p))‖ +
            ‖(w - p) * (t : ℂ) * deriv f (p + (t : ℂ) * (w - p))‖ := norm_add_le _ _
        _ = ‖f (p + (t : ℂ) * (w - p))‖ +
            ‖w - p‖ * ‖(t : ℂ)‖ * ‖deriv f (p + (t : ℂ) * (w - p))‖ := by
              rw [norm_mul, norm_mul]
        _ ≤ Mf + Bwp * 1 * Mdf := by
              have h1 : ‖w - p‖ * ‖(t : ℂ)‖ * ‖deriv f (p + (t : ℂ) * (w - p))‖
                  ≤ Bwp * 1 * Mdf := by
                apply mul_le_mul _ h_df_bd (norm_nonneg _) (mul_nonneg hBwp_nn (by norm_num))
                exact mul_le_mul h_wp h_t_abs (norm_nonneg _) hBwp_nn
              linarith [h_f_bd, h1]
        _ = C := by rw [hC_def]; ring
    have h_F_cont_w_on : ∀ w ∈ Metric.closedBall z r', ContinuousOn (F w) (Set.Icc (0:ℝ) 1) := by
      intro w hw
      apply ContinuousOn.mul continuousOn_const
      have h_inner_cont : Continuous (fun t : ℝ => p + (t : ℂ) * (w - p)) := by fun_prop
      apply hf_cont_U.comp h_inner_cont.continuousOn
      intro t ht
      exact h_pt_in_U w hw t ht
    have h_F_aemeas : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable (F x)
        (MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) 1)) := by
      filter_upwards [hs_mem] with x hx
      have h_cont := (h_F_cont_w_on x (hs_sub_cb hx)).mono
        (show Set.uIoc (0:ℝ) 1 ⊆ Set.Icc (0:ℝ) 1 from by
          rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
          exact Set.Ioc_subset_Icc_self)
      exact h_cont.aestronglyMeasurable measurableSet_uIoc
    have h_F_int : IntervalIntegrable (F z) MeasureTheory.volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact h_F_cont_w_on z (Metric.mem_closedBall_self hr'_pos.le)
    have h_F'_aemeas : AEStronglyMeasurable (F' z)
        (MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) 1)) := by
      apply ContinuousOn.aestronglyMeasurable _ measurableSet_uIoc
      rw [show Set.uIoc (0:ℝ) 1 = Set.Ioc 0 1 from Set.uIoc_of_le (by norm_num)]
      apply ContinuousOn.mono _ Set.Ioc_subset_Icc_self
      have h_inner_cont : Continuous (fun t : ℝ => p + (t : ℂ) * (z - p)) := by fun_prop
      have h_f_comp : ContinuousOn (fun t : ℝ => f (p + (t : ℂ) * (z - p)))
          (Set.Icc (0:ℝ) 1) := by
        apply hf_cont_U.comp h_inner_cont.continuousOn
        intro t ht
        exact h_pt_in_U z (Metric.mem_closedBall_self hr'_pos.le) t ht
      have h_df_comp : ContinuousOn (fun t : ℝ => deriv f (p + (t : ℂ) * (z - p)))
          (Set.Icc (0:ℝ) 1) := by
        apply hdf_cont_U.comp h_inner_cont.continuousOn
        intro t ht
        exact h_pt_in_U z (Metric.mem_closedBall_self hr'_pos.le) t ht
      apply ContinuousOn.add h_f_comp
      apply ContinuousOn.mul (ContinuousOn.mul continuousOn_const (by fun_prop)) h_df_comp
    have h_bound_int : IntervalIntegrable (fun _ : ℝ => C) MeasureTheory.volume 0 1 :=
      intervalIntegrable_const
    have h_diff := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (𝕜 := ℂ) (E := ℂ) (a := 0) (b := 1) (F := F) (F' := F') (x₀ := z) (s := s_nbhd)
      (bound := fun _ => C) hs_mem h_F_aemeas h_F_int h_F'_aemeas h_bound h_bound_int h_pt_deriv
    set g : ℝ → ℂ := fun t => (t : ℂ) * f (p + (t : ℂ) * (z - p)) with hg_def
    have hg_deriv : ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt g (F' z t) t := by
      intro t ht
      have ht_Icc : t ∈ Set.Icc (0:ℝ) 1 := by
        rwa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      have h_pt_z_in_U := h_pt_in_U z (Metric.mem_closedBall_self hr'_pos.le) t ht_Icc
      have h_t_id : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
      have h_inner_real : HasDerivAt (fun t : ℝ => p + (t : ℂ) * (z - p)) (z - p) t := by
        have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) * (z - p)) ((1:ℂ) * (z - p)) t :=
          h_t_id.mul_const (z - p)
        simpa using h2.const_add p
      have h_inner_C : HasDerivAt (fun w : ℂ => p + w * (z - p)) (z - p) ((t : ℂ) : ℂ) := by
        have h1 : HasDerivAt (fun w : ℂ => w) (1 : ℂ) ((t : ℂ) : ℂ) := hasDerivAt_id _
        have h2 : HasDerivAt (fun w : ℂ => w * (z - p)) ((1 : ℂ) * (z - p)) ((t : ℂ) : ℂ) :=
          h1.mul_const (z - p)
        simpa using h2.const_add p
      have hf_at_pre : HasDerivAt f (deriv f (p + (t : ℂ) * (z - p)))
          ((fun w : ℂ => p + w * (z - p)) (t : ℂ)) := by
        simpa using (hf.differentiableAt (hU.mem_nhds h_pt_z_in_U)).hasDerivAt
      have hf_comp_C : HasDerivAt (fun w : ℂ => f (p + w * (z - p)))
          (deriv f (p + (t : ℂ) * (z - p)) * (z - p)) ((t : ℂ) : ℂ) := by
        have h_c := HasDerivAt.comp ((t : ℂ) : ℂ) hf_at_pre h_inner_C
        simp only [Function.comp_def] at h_c
        exact h_c
      have hf_comp_real : HasDerivAt (fun t : ℝ => f (p + (t : ℂ) * (z - p)))
          (deriv f (p + (t : ℂ) * (z - p)) * (z - p)) t := hf_comp_C.comp_ofReal
      have h_prod := h_t_id.mul hf_comp_real
      have h_eq : (1 : ℂ) * f (p + (t : ℂ) * (z - p))
            + (t : ℂ) * (deriv f (p + (t : ℂ) * (z - p)) * (z - p))
          = f (p + (t : ℂ) * (z - p))
            + (z - p) * (t : ℂ) * deriv f (p + (t : ℂ) * (z - p)) := by ring
      rw [h_eq] at h_prod
      exact h_prod
    have h_F'_int : IntervalIntegrable (F' z) MeasureTheory.volume 0 1 := h_diff.1
    have h_ftc : ∫ t in (0:ℝ)..1, F' z t = g 1 - g 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hg_deriv h_F'_int
    have h_g_endpoints : g 1 - g 0 = f z := by
      simp only [hg_def]
      have h1 : p + ((1 : ℝ) : ℂ) * (z - p) = z := by push_cast; ring
      have h0 : ((0 : ℝ) : ℂ) * f (p + ((0 : ℝ) : ℂ) * (z - p)) = 0 := by push_cast; ring
      rw [h0, h1]; push_cast; ring
    have h_final : HasDerivAt (fun w => ∫ t in (0:ℝ)..1, F w t)
        (∫ t in (0:ℝ)..1, F' z t) z := h_diff.2
    rw [h_ftc, h_g_endpoints] at h_final
    have h_eq : (fun w => ∫ t in (0:ℝ)..1, F w t) = starPrimitive p f := by
      funext w
      simp only [hF_def, starPrimitive]
    rw [h_eq] at h_final
    exact h_final
  have hopen : IsOpen omega := Complex.isOpen_slitPlane.preimage (by fun_prop)
  have hzero : (0 : ℂ) ∈ omega := by simp [omega]
  have hball : Metric.ball (0 : ℂ) 1 ⊆ omega := by
    intro z hz
    simpa [omega, sub_eq_add_neg] using
      Complex.mem_slitPlane_of_norm_lt_one (z := -z) (by simpa using hz)
  have hstar : StarConvex ℝ (0 : ℂ) omega := by
    rw [starConvex_zero_iff]
    intro z hz a ha ha1
    simp only [omega, mem_ofPred_eq, Complex.mem_slitPlane_iff,
      Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      sub_pos, zero_sub, neg_ne_zero] at hz ⊢
    simp only [Complex.smul_re, Complex.smul_im]
    rcases hz with hz | hz
    · left
      by_cases hr : 0 ≤ z.re
      · exact (mul_le_mul_of_nonneg_right ha1 hr).trans_lt (by simpa using hz)
      · exact (mul_nonpos_of_nonneg_of_nonpos ha (le_of_not_ge hr)).trans_lt zero_lt_one
    · by_cases ha0 : a = 0
      · simp [ha0]
      · exact Or.inr (mul_ne_zero ha0 hz)
  have hconn : IsPreconnected omega := (hstar.isPathConnected hzero).isConnected.isPreconnected
  have hden : ∀ z ∈ omega, 1 - z ≠ 0 := fun z hz => Complex.slitPlane_ne_zero hz
  have hp0 : ∀ f, starPrimitive 0 f 0 = 0 := by intro f; simp [starPrimitive]
  have hs0 : ∀ (head : ℕ+) tail, source (head :: tail) 0 = 0 := by intro head tail; simp [source]
  have hd0 : ∀ (head : ℕ+) tail,
      deriv (source (head :: tail)) 0 = if tail = [] then 1 else 0 := by
    intro head tail
    rw [(source_derivative head tail 0 (by simp)).deriv]
    simp only [derivativeSeries]
    rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
    cases tail <;> simp [H]
  have glue : ∀ (head : ℕ+) tail (g : ℂ → ℂ),
      DifferentiableOn ℂ g omega →
      (∀ z, ‖z‖ < 1 → g z = deriv (source (head :: tail)) z) →
      AnalyticOnNhd ℂ (starPrimitive 0 g) omega ∧
        ∀ z, ‖z‖ < 1 → starPrimitive 0 g z = source (head :: tail) z := by
    intro head tail g hg heq
    have hd : ∀ z ∈ omega, HasDerivAt (starPrimitive 0 g) (g z) z :=
      fun z hz => primitive hopen hstar hg hz
    refine ⟨(show DifferentiableOn ℂ (starPrimitive 0 g) omega from
      fun z hz => (hd z hz).differentiableAt.differentiableWithinAt).analyticOnNhd hopen, ?_⟩
    have he := Metric.isOpen_ball.eqOn_of_deriv_eq (convex_ball (0 : ℂ) 1).isPreconnected
      (fun z hz => (hd z (hball hz)).differentiableAt.differentiableWithinAt)
      (fun z hz => (source_derivative head tail z (by simpa using hz)).differentiableAt.differentiableWithinAt)
      (fun z hz => (hd z (hball hz)).deriv.trans (heq z (by simpa using hz)))
      (by simp : (0 : ℂ) ∈ Metric.ball 0 1) ((hp0 g).trans (hs0 head tail).symm)
    exact fun z hz => he (by simpa using hz)
  have family : ∀ ks, AnalyticOnNhd ℂ (continued ks) omega ∧
      ∀ z, ‖z‖ < 1 → continued ks z = source ks z := by
    intro ks
    induction ks with
    | nil => exact ⟨analyticOnNhd_const, fun _ _ => rfl⟩
    | cons head tail ih =>
      have hr : ∀ n, AnalyticOnNhd ℂ (raise (continued tail) n) omega ∧
          ∀ z, ‖z‖ < 1 → raise (continued tail) n z = source (⟨n + 1, by omega⟩ :: tail) z := by
        intro n
        induction n with
        | zero =>
          apply glue 1 tail
          · exact ih.1.differentiableOn.div (by fun_prop) hden
          · intro z hz; rw [ih.2 z hz, source_recurrences.1 tail z hz]
        | succ n ihn =>
          have hg : DifferentiableOn ℂ (dslope (raise (continued tail) n) 0) omega :=
            (Complex.differentiableOn_dslope (hopen.mem_nhds hzero)).2 ihn.1.differentiableOn
          apply glue ⟨n + 1 + 1, by omega⟩ tail _ hg
          intro z hz
          rw [source_recurrences.2 ⟨n + 1 + 1, by omega⟩ tail (by simp) z hz]
          by_cases hz0 : z = 0
          · subst z
            rw [if_pos rfl, dslope_same]
            have he : raise (continued tail) n =ᶠ[𝓝 0] source (⟨n + 1, by omega⟩ :: tail) :=
              Filter.eventually_of_mem (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1))
                (fun w hw => ihn.2 w (by simpa using hw))
            rw [he.deriv_eq, hd0]
          · rw [if_neg hz0, dslope_of_ne _ hz0, slope_def_field,
              ihn.2 z hz, ihn.2 0 (by simp), hs0, sub_zero, sub_zero]
            rfl
      have he : (⟨(head : ℕ) - 1 + 1, by omega⟩ : ℕ+) = head := Subtype.ext (Nat.sub_add_cancel head.pos)
      simpa only [continued, he] using hr ((head : ℕ) - 1)
  have germ : ∀ ks z, ‖z‖ < 1 → continued ks =ᶠ[𝓝 z] source ks := by
    intro ks z hz
    exact Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds (show z ∈ Metric.ball 0 1 by simpa using hz))
      (fun w hw => (family ks).2 w (by simpa using hw))
  have hnorm : ∀ (head : ℕ+) tail, continued (head :: tail) 0 = 0 :=
    fun head tail => ((family _).2 0 (by simp)).trans (hs0 head tail)
  have hds : ∀ (head : ℕ+) tail, AnalyticOnNhd ℂ (dslope (continued (head :: tail)) 0) omega :=
    fun head tail => ((Complex.differentiableOn_dslope (hopen.mem_nhds hzero)).2
      (family _).1.differentiableOn).analyticOnNhd hopen
  refine ⟨rfl, family, ?_, ?_, ?_⟩
  · intro head tail
    have he : continued (head :: tail) =ᶠ[𝓝 0] li head tail := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
      exact ((family _).2 z (by simpa using hz)).trans
        ((source_series head tail).2.2.2.2.1 z (by simpa using hz)).symm
    refine ⟨hnorm head tail, (analyticOrderAt_congr he).trans (source_series head tail).2.2.2.2.2.1,
      ?_, ?_⟩
    · intro z hz
      exact ((family _).2 z hz).trans (((source_series head tail).2.2.2.2.1 z hz).symm.trans
        ((source_series head tail).2.2.2.2.2.2 z hz))
    · have hc : ∀ z ∈ omega, conj z ∈ omega := by
        intro z hz
        simpa [omega, Complex.mem_slitPlane_iff] using hz
      have ha : AnalyticOnNhd ℂ (fun z => conj (continued (head :: tail) (conj z))) omega := by
        apply DifferentiableOn.analyticOnNhd _ hopen
        intro z hz
        exact (differentiableAt_conj_conj_iff.mpr
          ((family (head :: tail)).1 (conj z) (hc z hz)).differentiableAt).differentiableWithinAt
      have hi := (family (head :: tail)).1.eqOn_of_preconnected_of_eventuallyEq ha hconn hzero
        (show continued (head :: tail) =ᶠ[𝓝 0] (fun z => conj (continued (head :: tail) (conj z))) from by
          filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with w hw
          rw [(family _).2 w (by simpa using hw), (family _).2 (conj w) (by simpa using hw)]
          simp [source, Complex.conj_tsum])
      intro z hz
      simpa using (congrArg conj (hi hz)).symm
  · intro tail z hz
    have ha : AnalyticOnNhd ℂ (fun z => continued tail z / (1 - z)) omega :=
      (family tail).1.div (analyticOnNhd_const.sub analyticOnNhd_id) hden
    have hi := (family (1 :: tail)).1.deriv.eqOn_of_preconnected_of_eventuallyEq ha hconn hzero
      (show deriv (continued (1 :: tail)) =ᶠ[𝓝 0] (fun z => continued tail z / (1 - z)) from by
        filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with w hw
        have hw' : ‖w‖ < 1 := by simpa using hw
        rw [(germ _ w hw').deriv_eq, source_recurrences.1 tail w hw', (family tail).2 w hw'])
    convert! ((family (1 :: tail)).1 z hz).differentiableAt.hasDerivAt using 1
    exact (hi hz).symm
  · intro head tail hh z hz
    let prev : ℕ+ := ⟨(head : ℕ) - 1, by omega⟩
    have hi := (family (head :: tail)).1.deriv.eqOn_of_preconnected_of_eventuallyEq
      (hds prev tail) hconn hzero (show deriv (continued (head :: tail)) =ᶠ[𝓝 0]
        dslope (continued (prev :: tail)) 0 from by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with w hw
      have hw' : ‖w‖ < 1 := by simpa using hw
      rw [(germ _ w hw').deriv_eq, source_recurrences.2 head tail hh w hw']
      by_cases hw0 : w = 0
      · subst w; rw [if_pos rfl, dslope_same, (germ _ 0 (by simp)).deriv_eq, hd0]
      · rw [if_neg hw0, dslope_of_ne _ hw0, slope_def_field, hnorm, sub_zero, sub_zero,
          (family _).2 w hw'])
    have hd := ((family (head :: tail)).1 z hz).differentiableAt.hasDerivAt
    rw [hi hz] at hd
    by_cases hz0 : z = 0
    · subst z
      simpa only [ite_true, dslope_same, (germ _ 0 (by simp)).deriv_eq, hd0] using hd
    · simpa only [if_neg hz0, dslope_of_ne _ hz0, slope_def_field, hnorm, sub_zero] using hd
#print axioms result
end D5.S3.AnalyticClosure.Polylogarithm.CompositionSlit
