/- GID: D5/S3/Quantum/Analysis/MeasurableNonautonomousDysonPhillips
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/MeasurableNonautonomousDysonPhillips
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Vectorwise measurable Volterra integrals with integrable scalar clocks. -/

import D5.S3.Quantum.Analysis.StrongNonautonomousDysonPhillips
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! # Vectorwise measurable nonautonomous Bochner integrals -/

open scoped Nat Topology
open MeasureTheory Filter intervalIntegral
open D5.S3.Quantum.Analysis.NonautonomousDysonPhillips

namespace D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Vectorwise AE strong measurability is stable under AE strongly measurable evaluation. -/
theorem aestronglyMeasurable_evaluation {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (B : α → E →L[ℂ] E)
    (hB : ∀ x : E, AEStronglyMeasurable (fun s => B s x) μ)
    {v : α → E} (hv : AEStronglyMeasurable v μ) :
    AEStronglyMeasurable (fun s => B s (v s)) μ := by
  classical
  have hs : ∀ f : SimpleFunc α E, AEStronglyMeasurable (fun s => B s (f s)) μ := by
    intro f
    apply SimpleFunc.induction' (P := fun f =>
      AEStronglyMeasurable (fun s => B s (f s)) μ) _ _ f
    · intro c
      exact hB c
    · intro f g A hA hf hg
      convert AEStronglyMeasurable.piecewise hA.nullMeasurableSet hf.restrict hg.restrict using 1
      ext s
      by_cases hmem : s ∈ A <;> simp [SimpleFunc.piecewise_apply, Set.piecewise, hmem]
  have hm := hv.stronglyMeasurable_mk
  apply aestronglyMeasurable_of_tendsto_ae atTop (fun n => hs (hm.approx n))
  filter_upwards [hv.ae_eq_mk] with s hs
  rw [hs]
  exact (B s).continuous.continuousAt.tendsto.comp (hm.tendsto_approx s)

private theorem clock_ac {r t : ℝ} (hrt : r ≤ t) {g : ℝ → ℝ}
    (hg : IntegrableOn g (Set.Icc r t)) :
    AbsolutelyContinuousOnInterval (fun u => ∫ s in r..u, g s) r t := by
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hrt).mpr hg
  exact hi.absolutelyContinuousOnInterval_intervalIntegral (by simp)

private theorem ac_pow {f : ℝ → ℝ} {r t : ℝ}
    (hf : AbsolutelyContinuousOnInterval f r t) (n : ℕ) :
    AbsolutelyContinuousOnInterval (fun s => f s ^ n) r t := by
  induction n with
  | zero => simpa using (LipschitzOnWith.absolutelyContinuousOnInterval (LipschitzWith.const (1 : ℝ)).lipschitzOnWith)
  | succ n ih => simpa only [pow_succ] using ih.fun_mul hf

/-- The L1 primitive clock has the exact factorial-weighted moment, including a zero interval. -/
theorem clock_moment {r t : ℝ} (hrt : r ≤ t) {g : ℝ → ℝ}
    (hg : IntegrableOn g (Set.Icc r t)) (n : ℕ) :
    IntervalIntegrable (fun s => g s * ((∫ z in r..s, g z)^n / n !)) volume r t ∧
    (∫ s in r..t, g s * ((∫ z in r..s, g z)^n / n !)) =
      (∫ z in r..t, g z)^(n+1) / (n+1)! := by
  let F : ℝ → ℝ := fun u => ∫ s in r..u, g s
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hrt).mpr hg
  have hF := clock_ac hrt hg
  have hpow := ac_pow hF (n+1)
  have hderiv : ∀ᵐ s, s ∈ Set.uIcc r t →
      deriv (fun u => F u ^ (n+1)) s = (n+1 : ℝ) * F s ^ n * g s := by
    filter_upwards [hi.ae_hasDerivAt_integral] with s hs hmem
    simpa only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, Pi.pow_apply] using
      ((hs hmem r (by simp)).fun_pow (n+1)).deriv
  have hFTC := hpow.integral_deriv_eq_sub
  have heq : (fun s => deriv (fun u => F u ^ (n+1)) s) =ᵐ[volume.restrict (Set.uIcc r t)]
      (fun s => (n+1 : ℝ) * F s ^ n * g s) := by
    exact (ae_restrict_iff' measurableSet_uIcc).mpr hderiv
  have hw : IntervalIntegrable (fun s => g s * (F s ^ n / n !)) volume r t :=
    hi.mul_continuousOn ((hF.continuousOn.pow n).div_const _)
  refine ⟨hw, ?_⟩
  have heq' := intervalIntegral.integral_congr_ae_restrict
    (heq.filter_mono (ae_mono (Measure.restrict_mono Set.uIoc_subset_uIcc le_rfl)))
  change (∫ s in r..t, g s * (F s ^ n / n !)) = _
  have hfactor : (∫ s in r..t, (n+1 : ℝ) * F s ^ n * g s) =
      ((n+1 : ℝ) * n !) * (∫ s in r..t, g s * (F s ^ n / n !)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    have hn : (n ! : ℝ) ≠ 0 := by positivity
    field_simp
  rw [heq'] at hFTC
  simp only [F, intervalIntegral.integral_same, zero_pow (Nat.succ_ne_zero n), sub_zero] at hFTC
  rw [hfactor] at hFTC
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  exact (eq_div_iff (by positivity)).mpr (by simpa [mul_comm] using hFTC)

private theorem evaluation_integrable {r H : ℝ} {B : ℝ → E →L[ℂ] E}
    (hB : ∀ x : E, AEStronglyMeasurable (fun s => B s x) (volume.restrict (Set.Icc r H)))
    {g : ℝ → ℝ} (hg : IntegrableOn g (Set.Icc r H))
    (hBg : ∀ s ∈ Set.Icc r H, ‖B s‖ ≤ g s)
    {v : ℝ → E} (hv : ContinuousOn v (Set.Icc r H)) :
    IntegrableOn (fun s => B s (v s)) (Set.Icc r H) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hv
  apply (hg.mul_const C).mono'
    (aestronglyMeasurable_evaluation B hB (hv.aestronglyMeasurable measurableSet_Icc))
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  exact ((B s).le_opNorm _).trans
    (mul_le_mul (hBg s hs) (hC s hs) (norm_nonneg _) ((norm_nonneg _).trans (hBg s hs)))


private theorem convolution_continuous (S : Contraction E) {w : ℝ → E}
    (hw : Integrable w) (r : ℝ) :
    Continuous (fun t => ∫ s in r..t, S.action (t-s) (w s)) := by
  rw [continuous_iff_continuousAt]
  intro t
  let a := min r t - 1
  let b := max r t + 1
  have hmeas : ∀ u, AEStronglyMeasurable (fun s => S.action (u-s) (w s))
      (volume.restrict (Set.uIoc a b)) := by
    intro u
    exact S.action_continuous.comp_aestronglyMeasurable
      (((continuous_const.sub continuous_id).aestronglyMeasurable).prodMk
        hw.aestronglyMeasurable.restrict)
  have h := intervalIntegral.continuousAt_parametric_primitive_of_dominated
    (F := fun u s => S.action (u-s) (w s)) (x₀ := t) (a₀ := r) (b₀ := t)
    (fun s => ‖w s‖) a b hmeas
    (Eventually.of_forall fun u => Eventually.of_forall fun s => S.action_bound _ _)
    hw.norm.intervalIntegrable
    (Eventually.of_forall fun s =>
      (S.action_continuous.comp ((continuous_id.sub continuous_const).prodMk continuous_const)).continuousAt)
    (show r ∈ Set.Ioo a b from ⟨by dsimp [a]; linarith [min_le_left r t],
      by dsimp [b]; linarith [le_max_left r t]⟩)
    (show t ∈ Set.Ioo a b from ⟨by dsimp [a]; linarith [min_le_right r t],
      by dsimp [b]; linarith [le_max_right r t]⟩) (by simp)
  exact h.comp (f := fun u : ℝ => (u,u))
    (continuous_id.prodMk continuous_id).continuousAt

/-- Every continuous vector path has actual causal integrability and continuous causal output. -/
theorem causal_regular (S : Contraction E) {B : ℝ → E →L[ℂ] E} {r H : ℝ}
    (hB : ∀ x : E, AEStronglyMeasurable (fun s => B s x) (volume.restrict (Set.Icc r H)))
    {g : ℝ → ℝ} (hg : IntegrableOn g (Set.Icc r H))
    (hBg : ∀ s ∈ Set.Icc r H, ‖B s‖ ≤ g s)
    {v : ℝ → E} (hv : ContinuousOn v (Set.Icc r H)) :
    ContinuousOn (causal S B r v) (Set.Icc r H) ∧
    ∀ t ∈ Set.Icc r H, IntervalIntegrable
      (fun s => S.action (t-s) (B s (v s))) volume r t := by
  have hi := evaluation_integrable hB hg hBg hv
  let w := (Set.Icc r H).indicator (fun s => B s (v s))
  have hw : Integrable w := hi.integrable_indicator measurableSet_Icc
  constructor
  · apply (convolution_continuous S hw r).continuousOn.congr
    intro t ht
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le ht.1] at hs
    have hsH : s ∈ Set.Icc r H := ⟨hs.1, hs.2.trans ht.2⟩
    simp only [w, Set.indicator_of_mem hsH]
  · intro t ht
    have hmeas : AEStronglyMeasurable (fun s => S.action (t-s) (B s (v s)))
        (volume.restrict (Set.Icc r t)) :=
      S.action_continuous.comp_aestronglyMeasurable
        (((continuous_const.sub continuous_id).aestronglyMeasurable).prodMk
          (hi.aestronglyMeasurable.mono_set (Set.Icc_subset_Icc le_rfl ht.2)))
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).mpr
    have hiN : IntegrableOn (fun s => ‖B s (v s)‖) (Set.Icc r H) := hi.norm
    apply (hiN.mono_set (Set.Icc_subset_Icc le_rfl ht.2)).mono' hmeas
    exact Eventually.of_forall fun s => S.action_bound _ _

variable [CompleteSpace E]

/-- The weighted factorial estimate for the original causal iterates and every real path bound. -/
theorem measurable_causal_iterate_bound
    (S : Contraction E) (B : ℝ → E →L[ℂ] E) {r H : ℝ} (hrH : r ≤ H)
    (hB : ∀ x : E, AEStronglyMeasurable (fun s => B s x) (volume.restrict (Set.Icc r H)))
    (g : ℝ → ℝ) (hg : IntegrableOn g (Set.Icc r H))
    (hgn : ∀ s ∈ Set.Icc r H, 0 ≤ g s)
    (hBg : ∀ s ∈ Set.Icc r H, ‖B s‖ ≤ g s)
    (v : ℝ → E) (hv : ContinuousOn v (Set.Icc r H))
    (C : ℝ) (hvC : ∀ s ∈ Set.Icc r H, ‖v s‖ ≤ C) :
    ∀ n : ℕ, ∀ t ∈ Set.Icc r H,
      ‖causalIterate S B r v n t‖ ≤ C * ((∫ s in r..t, g s)^n / n !) := by
  have hcont : ∀ n, ContinuousOn (causalIterate S B r v n) (Set.Icc r H) := by
    intro n
    induction n with
    | zero => exact hv
    | succ n ih => exact (causal_regular S hB hg hBg ih).1
  intro n
  induction n with
  | zero => intro t ht; simpa [causalIterate] using hvC t ht
  | succ n ih =>
    intro t ht
    have hint := (causal_regular S hB hg hBg (hcont n)).2 t ht
    have hw := clock_moment ht.1 (hg.mono_set (Set.Icc_subset_Icc le_rfl ht.2)) n
    change ‖∫ s in r..t, S.action (t-s) (B s (causalIterate S B r v n s))‖ ≤ _
    calc
      _ ≤ ∫ s in r..t, ‖S.action (t-s) (B s (causalIterate S B r v n s))‖ :=
        intervalIntegral.norm_integral_le_integral_norm ht.1
      _ ≤ ∫ s in r..t, C * (g s * ((∫ z in r..s, g z)^n / n !)) := by
        apply intervalIntegral.integral_mono_on ht.1 hint.norm (hw.1.const_mul C)
        intro s hs
        have hsH : s ∈ Set.Icc r H := ⟨hs.1, hs.2.trans ht.2⟩
        calc
          _ ≤ ‖B s (causalIterate S B r v n s)‖ := S.action_bound _ _
          _ ≤ ‖B s‖ * ‖causalIterate S B r v n s‖ := (B s).le_opNorm _
          _ ≤ g s * (C * ((∫ z in r..s, g z)^n / n !)) :=
            mul_le_mul (hBg s hsH) (ih s hsH) (norm_nonneg _) (hgn s hsH)
          _ = _ := by ring
      _ = C * ((∫ z in r..t, g z)^(n+1) / (n+1)!) := by
        rw [intervalIntegral.integral_const_mul, hw.2]


section Horizon
variable (S : Contraction E) (B : ℝ → E →L[ℂ] E) {r H : ℝ} (hrH : r ≤ H)
  (hB : ∀ x : E, AEStronglyMeasurable (fun s => B s x) (volume.restrict (Set.Icc r H)))
  (g : ℝ → ℝ) (hg : IntegrableOn g (Set.Icc r H))
  (hgn : ∀ s ∈ Set.Icc r H, 0 ≤ g s)
  (hBg : ∀ s ∈ Set.Icc r H, ‖B s‖ ≤ g s)
include hrH hB hg hgn hBg

private theorem iterate_continuous {v : ℝ → E} (hv : ContinuousOn v (Set.Icc r H)) (n : ℕ) :
    ContinuousOn (causalIterate S B r v n) (Set.Icc r H) := by
  induction n with
  | zero => exact hv
  | succ n ih => exact (causal_regular S hB hg hBg ih).1

private theorem term_continuous (n : ℕ) (x : E) :
    ContinuousOn (fun t => term S B n t r x) (Set.Icc r H) :=
  iterate_continuous S B hrH hB g hg hgn hBg (orbit_continuous S r x).continuousOn n

private theorem term_integrable (n : ℕ) (x : E) {t : ℝ} (ht : t ∈ Set.Icc r H) :
    IntervalIntegrable (fun s => S.action (t-s) (B s (term S B n s r x))) volume r t :=
  (causal_regular S hB hg hBg (term_continuous S B hrH hB g hg hgn hBg n x)).2 t ht

private theorem term_bound (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc r H) (x : E) :
    ‖term S B n t r x‖ ≤ (∫ s in r..t, g s)^n / n ! * ‖x‖ := by
  simpa only [term, mul_comm] using measurable_causal_iterate_bound S B hrH hB g hg hgn hBg
    (fun s => S.action (s-r) x) (orbit_continuous S r x).continuousOn
    ‖x‖ (fun s _ => S.action_bound _ _) n t ht

/-- Absolute norm convergence and the actual sum of the original vector Bochner series. -/
theorem measurable_series {t : ℝ} (ht : t ∈ Set.Icc r H) (x : E) :
    Summable (fun n => ‖term S B n t r x‖) ∧
    HasSum (fun n => term S B n t r x) (sum S B t r x) := by
  have hn : Summable (fun n => ‖term S B n t r x‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => term_bound S B hrH hB g hg hgn hBg n ht x)
      ((Real.summable_pow_div_factorial (∫ s in r..t, g s)).mul_right _)
  exact ⟨hn, hn.of_norm.hasSum⟩

/-- A continuous residual equal to its causal integral vanishes without a supplied norm bound. -/
theorem continuous_residual_eq_zero {Y : ℝ → E}
    (hY : ContinuousOn Y (Set.Icc r H))
    (heq : ∀ t ∈ Set.Icc r H, Y t = causal S B r Y t) :
    ∀ t ∈ Set.Icc r H, Y t = 0 := by
  have hIter : ∀ n, Set.EqOn (causalIterate S B r Y n) Y (Set.Icc r H) := by
    intro n
    induction n with
    | zero => intro t _; rfl
    | succ n ih =>
      intro t ht
      rw [heq t ht]
      change (∫ s in r..t, S.action (t-s) (B s (causalIterate S B r Y n s))) = _
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le ht.1] at hs
      dsimp only
      rw [ih ⟨hs.1, hs.2.trans ht.2⟩]
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hY
  intro t ht
  have hb : ∀ n, ‖Y t‖ ≤ C * ((∫ s in r..t, g s)^n / n !) := by
    intro n
    rw [← hIter n ht]
    exact measurable_causal_iterate_bound S B hrH hB g hg hgn hBg Y hY C hC n t ht
  have hlim : Tendsto (fun n : ℕ => C * ((∫ s in r..t, g s)^n / n !)) atTop (𝓝 0) := by
    simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop (∫ s in r..t, g s)).const_mul C
  exact norm_le_zero_iff.mp (ge_of_tendsto' hlim hb)

end Horizon
end D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips
