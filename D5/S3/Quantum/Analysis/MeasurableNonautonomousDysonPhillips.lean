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

theorem evaluation_integrable {r H : ℝ} {B : ℝ → E →L[ℂ] E}
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

theorem term_integrable (n : ℕ) (x : E) {t : ℝ} (ht : t ∈ Set.Icc r H) :
    IntervalIntegrable (fun s => S.action (t-s) (B s (term S B n s r x))) volume r t :=
  (causal_regular S hB hg hBg (term_continuous S B hrH hB g hg hgn hBg n x)).2 t ht

theorem term_bound (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc r H) (x : E) :
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



private theorem clock_nonneg {t : ℝ} (ht : t ∈ Set.Icc r H) : 0 ≤ ∫ s in r..t, g s :=
  intervalIntegral.integral_nonneg ht.1 (fun s hs => hgn s ⟨hs.1, hs.2.trans ht.2⟩)

private theorem clock_le {t : ℝ} (ht : t ∈ Set.Icc r H) :
    (∫ s in r..t, g s) ≤ ∫ s in r..H, g s := by
  apply intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
    _ ((intervalIntegrable_iff_integrableOn_Icc_of_le hrH).mpr hg)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact hgn s ⟨hs.1.le, hs.2⟩

private theorem term_uniform_bound (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc r H) (x : E) :
    ‖term S B n t r x‖ ≤ (∫ s in r..H, g s)^n / n ! * ‖x‖ := by
  apply (term_bound S B hrH hB g hg hgn hBg n ht x).trans
  have hn := clock_nonneg (E := E) (B := B) (hrH := hrH) (hB := hB) (g := g) (hg := hg)
    (hgn := hgn) (hBg := hBg) ht
  have hl := clock_le (E := E) (B := B) (hrH := hrH) (hB := hB) (g := g) (hg := hg)
    (hgn := hgn) (hBg := hBg) ht
  gcongr

private theorem sum_continuous (x : E) :
    ContinuousOn (fun t => sum S B t r x) (Set.Icc r H) := by
  apply continuousOn_tsum
    (u := fun n => (∫ s in r..H, g s)^n / n ! * ‖x‖)
    (fun n => term_continuous S B hrH hB g hg hgn hBg n x)
    ((Real.summable_pow_div_factorial _).mul_right _) _
  exact fun n t ht => term_uniform_bound S B hrH hB g hg hgn hBg n ht x

private theorem sum_bound {t : ℝ} (ht : t ∈ Set.Icc r H) (x : E) :
    ‖sum S B t r x‖ ≤ Real.exp (∫ s in r..t, g s) * ‖x‖ := by
  have hn := (measurable_series S B hrH hB g hg hgn hBg ht x).1
  calc
    _ ≤ ∑' n, ‖term S B n t r x‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n, (∫ s in r..t, g s)^n / n ! * ‖x‖ := hn.tsum_le_tsum
      (fun n => term_bound S B hrH hB g hg hgn hBg n ht x)
      ((Real.summable_pow_div_factorial _).mul_right _)
    _ = _ := by
      rw [tsum_mul_right, Real.exp_eq_exp_ℝ, ← (NormedSpace.expSeries_div_hasSum_exp (∫ s in r..t, g s)).tsum_eq]

private theorem term_add (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc r H) (x y : E) :
    term S B n t r (x+y) = term S B n t r x + term S B n t r y := by
  induction n generalizing t with
  | zero => exact map_add _ _ _
  | succ n ih =>
    simp only [term_succ]
    calc
      _ = ∫ s in r..t, (S.action (t-s) (B s (term S B n s r x)) +
          S.action (t-s) (B s (term S B n s r y))) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [Set.uIcc_of_le ht.1] at hs
        dsimp only
        rw [ih ⟨hs.1, hs.2.trans ht.2⟩, map_add, map_add]
      _ = _ := intervalIntegral.integral_add
        (term_integrable S B hrH hB g hg hgn hBg n x ht)
        (term_integrable S B hrH hB g hg hgn hBg n y ht)

private theorem sum_mild {t : ℝ} (ht : t ∈ Set.Icc r H) (x : E) :
    sum S B t r x = S.action (t-r) x +
      ∫ s in r..t, S.action (t-s) (B s (sum S B s r x)) := by
  have hsum := (measurable_series S B hrH hB g hg hgn hBg ht x).1.of_norm
  rw [sum, hsum.tsum_eq_zero_add, term_zero]
  congr 1
  have hg' := hg.mono_set (Set.Icc_subset_Icc le_rfl ht.2)
  have hB' := fun z => (hB z).mono_set (Set.Icc_subset_Icc le_rfl ht.2)
  have hgn' := fun s (hs : s ∈ Set.Icc r t) => hgn s ⟨hs.1, hs.2.trans ht.2⟩
  have hBg' := fun s (hs : s ∈ Set.Icc r t) => hBg s ⟨hs.1, hs.2.trans ht.2⟩
  have hi : HasSum (fun n => ∫ s in r..t, S.action (t-s) (B s (term S B n s r x)))
      (∫ s in r..t, S.action (t-s) (B s (sum S B s r x))) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (bound := fun n s => g s * ((∫ z in r..t, g z)^n / n ! * ‖x‖))
    · intro n
      exact (term_integrable S B hrH hB g hg hgn hBg n x ht).aestronglyMeasurable_restrict_uIoc
    · intro n
      exact Eventually.of_forall fun s hs => by
        rw [Set.uIoc_of_le ht.1] at hs
        have hsH : s ∈ Set.Icc r H := ⟨hs.1.le, hs.2.trans ht.2⟩
        calc
          _ ≤ ‖B s (term S B n s r x)‖ := S.action_bound _ _
          _ ≤ ‖B s‖ * ‖term S B n s r x‖ := (B s).le_opNorm _
          _ ≤ g s * ((∫ z in r..t, g z)^n / n ! * ‖x‖) :=
            mul_le_mul (hBg s hsH)
              (term_uniform_bound S B ht.1 hB' g hg' hgn' hBg' n ⟨hs.1.le, hs.2⟩ x)
              (norm_nonneg _) (hgn s hsH)
    · exact Eventually.of_forall fun s _ =>
        ((Real.summable_pow_div_factorial _).mul_right ‖x‖).mul_left (g s)
    · simp_rw [tsum_mul_left]
      exact ((intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).mpr hg').mul_const _
    · exact Eventually.of_forall fun s hs => by
        rw [Set.uIoc_of_le ht.1] at hs
        exact ((S.action (t-s)).comp (B s)).hasSum
          (measurable_series S B hrH hB g hg hgn hBg ⟨hs.1.le, hs.2.trans ht.2⟩ x).2
  simpa only [term_succ] using hi.tsum_eq

private theorem sum_unique {X : ℝ → E} (hX : ContinuousOn X (Set.Icc r H)) (x : E)
    (heq : ∀ t ∈ Set.Icc r H, X t = S.action (t-r) x +
      ∫ s in r..t, S.action (t-s) (B s (X s))) :
    ∀ t ∈ Set.Icc r H, X t = sum S B t r x := by
  let Y := fun t => X t - sum S B t r x
  have hSc := sum_continuous S B hrH hB g hg hgn hBg x
  have hY := hX.sub hSc
  have hYeq : ∀ t ∈ Set.Icc r H, Y t = causal S B r Y t := by
    intro t ht
    have hiX := (causal_regular S hB hg hBg hX).2 t ht
    have hiS := (causal_regular S hB hg hBg hSc).2 t ht
    change X t - sum S B t r x = ∫ s in r..t, S.action (t-s) (B s (Y s))
    rw [heq t ht, sum_mild S B hrH hB g hg hgn hBg ht x]
    rw [show (∫ s in r..t, S.action (t-s) (B s (Y s))) =
      (∫ s in r..t, S.action (t-s) (B s (X s))) -
      (∫ s in r..t, S.action (t-s) (B s (sum S B s r x))) by
        simp only [Y, map_sub]
        exact intervalIntegral.integral_sub hiX hiS]
    abel
  intro t ht
  exact sub_eq_zero.mp (continuous_residual_eq_zero S B hrH hB g hg hgn hBg hY hYeq t ht)

private noncomputable def sum_linear {t : ℝ} (ht : t ∈ Set.Icc r H) : E →ₗ[ℂ] E where
  toFun := sum S B t r
  map_add' x y := by
    simp only [sum, term_add S B hrH hB g hg hgn hBg _ ht]
    exact (measurable_series S B hrH hB g hg hgn hBg ht x).1.of_norm.tsum_add
      (measurable_series S B hrH hB g hg hgn hBg ht y).1.of_norm
  map_smul' c x := by
    simp only [sum, term_smul]
    exact tsum_const_smul'' c

private theorem sum_realization {t : ℝ} (ht : t ∈ Set.Icc r H) :
    ∃ A : E →L[ℂ] E, ∀ x, A x = sum S B t r x := by
  exact ⟨(sum_linear S B hrH hB g hg hgn hBg ht).mkContinuous
    (Real.exp (∫ s in r..t, g s)) (sum_bound S B hrH hB g hg hgn hBg ht), fun _ => rfl⟩

end Horizon

/-- A single coefficient-indexed linear realization of the original sum, before any control. -/
noncomputable def measurableEvolution (S : Contraction E) (B : ℝ → E →L[ℂ] E)
    (t r : ℝ) : E →L[ℂ] E := by
  classical
  exact if h : ∃ A : E →L[ℂ] E, ∀ x, A x = sum S B t r x then h.choose else 0

theorem measurableEvolution_apply (S : Contraction E) (B : ℝ → E →L[ℂ] E)
    {r H : ℝ} (hrH : r ≤ H)
    (hB : ∀ x : E, AEStronglyMeasurable (fun s => B s x) (volume.restrict (Set.Icc r H)))
    (g : ℝ → ℝ) (hg : IntegrableOn g (Set.Icc r H))
    (hgn : ∀ s ∈ Set.Icc r H, 0 ≤ g s)
    (hBg : ∀ s ∈ Set.Icc r H, ‖B s‖ ≤ g s)
    {t : ℝ} (ht : t ∈ Set.Icc r H) (x : E) :
    measurableEvolution S B t r x = sum S B t r x := by
  classical
  have h := sum_realization S B hrH hB g hg hgn hBg ht
  simp only [measurableEvolution, dif_pos h]
  exact h.choose_spec x


theorem parametric_primitive_continuous {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] (F : X → ℝ → E) {b : ℝ → ℝ} (hb : Integrable b)
    (hm : ∀ p, AEStronglyMeasurable (F p))
    (hbound : ∀ p s, ‖F p s‖ ≤ b s)
    (hc : ∀ s, Continuous (fun p => F p s)) (a₀ : ℝ) :
    Continuous (fun p : X × ℝ => ∫ s in a₀..p.2, F p.1 s) := by
  rw [continuous_iff_continuousAt]
  intro p
  let a := min a₀ p.2 - 1
  let z := max a₀ p.2 + 1
  exact intervalIntegral.continuousAt_parametric_primitive_of_dominated
    b a z (fun q => (hm q).restrict)
    (Eventually.of_forall fun q => Eventually.of_forall fun s => hbound q s)
    hb.intervalIntegrable (Eventually.of_forall fun s => (hc s).continuousAt)
    (show a₀ ∈ Set.Ioo a z from ⟨by dsimp [a]; linarith [min_le_left a₀ p.2],
      by dsimp [z]; linarith [le_max_left a₀ p.2]⟩)
    (show p.2 ∈ Set.Ioo a z from ⟨by dsimp [a]; linarith [min_le_right a₀ p.2],
      by dsimp [z]; linarith [le_max_right a₀ p.2]⟩) (by simp)

private theorem global_term_continuous (S : Contraction E) (B : ℝ → E →L[ℂ] E)
    (hB : ∀ x : E, AEStronglyMeasurable (fun s => B s x))
    (g : ℝ → ℝ) (hg : Integrable g) (hgn : ∀ s, 0 ≤ g s)
    (hBg : ∀ s, ‖B s‖ ≤ g s) (x : E) :
    ∀ n : ℕ, Continuous (fun p : ℝ × ℝ => term S B n p.1 p.2 x) ∧
      ∀ t r, ‖term S B n t r x‖ ≤ (∫ s, g s)^n * ‖x‖ := by
  have hG : 0 ≤ ∫ s, g s := integral_nonneg hgn
  intro n
  induction n with
  | zero =>
    exact ⟨S.action_continuous.comp
      ((continuous_fst.sub continuous_snd).prodMk continuous_const),
      fun t r => by simpa [term_zero] using S.action_bound (t-r) x⟩
  | succ n ih =>
    let K := (∫ s, g s)^n * ‖x‖
    have hK : 0 ≤ K := mul_nonneg (pow_nonneg hG _) (norm_nonneg _)
    let F : (ℝ × ℝ) → ℝ → E :=
      fun p s => S.action (p.1-s) (B s (term S B n s p.2 x))
    have hm : ∀ p, AEStronglyMeasurable (F p) := by
      intro p
      exact S.action_continuous.comp_aestronglyMeasurable
        (((continuous_const.sub continuous_id).aestronglyMeasurable).prodMk
          (aestronglyMeasurable_evaluation B hB
            (ih.1.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable))
    have hbound : ∀ p s, ‖F p s‖ ≤ g s * K := by
      intro p s
      exact (S.action_bound _ _).trans (((B s).le_opNorm _).trans
        (mul_le_mul (hBg s) (ih.2 s p.2) (norm_nonneg _) (hgn s)))
    have hi : ∀ p, Integrable (F p) := fun p =>
      (hg.mul_const K).mono' (hm p) (Eventually.of_forall (hbound p))
    have hc : ∀ s, Continuous (fun p => F p s) := by
      intro s
      exact S.action_continuous.comp ((continuous_fst.sub continuous_const).prodMk
        ((B s).continuous.comp (ih.1.comp (continuous_const.prodMk continuous_snd))))
    have hprim := parametric_primitive_continuous F (hg.mul_const K) hm hbound hc 0
    constructor
    · have ht := hprim.comp (continuous_id.prodMk continuous_fst)
      have hr := hprim.comp (continuous_id.prodMk continuous_snd)
      apply (ht.sub hr).congr
      intro p
      exact intervalIntegral.integral_interval_sub_left
        (hi p).intervalIntegrable (hi p).intervalIntegrable
    · intro t r
      change ‖∫ s in r..t, F (t,r) s‖ ≤ _
      calc
        _ ≤ ∫ s in Set.uIoc r t, ‖F (t,r) s‖ :=
          intervalIntegral.norm_integral_le_integral_norm_uIoc
        _ ≤ ∫ s in Set.uIoc r t, g s * K :=
          setIntegral_mono_ae (hi (t,r)).norm.integrableOn (hg.mul_const K).integrableOn
            (Eventually.of_forall (hbound (t,r)))
        _ ≤ ∫ s, g s * K := setIntegral_le_integral (hg.mul_const K)
          (Eventually.of_forall fun s => mul_nonneg (hgn s) hK)
        _ = _ := by rw [MeasureTheory.integral_mul_const]; dsimp [K]; ring

theorem term_joint_continuous (S : Contraction E) (B : ℝ → E →L[ℂ] E)
    {T : ℝ} (hT : 0 ≤ T)
    (hB : ∀ x : E, AEStronglyMeasurable (fun s => B s x) (volume.restrict (Set.Icc 0 T)))
    (g : ℝ → ℝ) (hg : IntegrableOn g (Set.Icc 0 T))
    (hgn : ∀ s ∈ Set.Icc 0 T, 0 ≤ g s)
    (hBg : ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ g s) (n : ℕ) (x : E) :
    ContinuousOn (fun p : ℝ × ℝ => term S B n p.1 p.2 x) (triangle T) := by
  classical
  let Q := (Set.Icc 0 T).indicator B
  let k := (Set.Icc 0 T).indicator g
  have hQ : ∀ x : E, AEStronglyMeasurable (fun s => Q s x) := by
    intro x
    have h := (aestronglyMeasurable_indicator_iff measurableSet_Icc).mpr (hB x)
    convert h using 1
    ext s
    by_cases hs : s ∈ Set.Icc 0 T <;> simp [Q, hs]
  have hk : Integrable k := hg.integrable_indicator measurableSet_Icc
  have hkn : ∀ s, 0 ≤ k s := fun s => by
    by_cases hs : s ∈ Set.Icc 0 T
    · simpa [k, hs] using hgn s hs
    · simp [k, hs]
  have hQk : ∀ s, ‖Q s‖ ≤ k s := fun s => by
    by_cases hs : s ∈ Set.Icc 0 T
    · simpa [Q, k, hs] using hBg s hs
    · simp [Q, k, hs]
  apply ((global_term_continuous S Q hQ k hk hkn hQk x n).1).continuousOn.congr
  intro p hp
  apply (term_locality S B (B' := Q) _ n ⟨hp.2.1, hp.2.2⟩ x)
  intro s hs
  simp [Q, Set.indicator_of_mem (show s ∈ Set.Icc 0 T from ⟨hp.1.trans hs.1, hs.2⟩)]

private theorem sum_joint_continuous (S : Contraction E) (B : ℝ → E →L[ℂ] E)
    {T : ℝ} (hT : 0 ≤ T)
    (hB : ∀ x : E, AEStronglyMeasurable (fun s => B s x) (volume.restrict (Set.Icc 0 T)))
    (g : ℝ → ℝ) (hg : IntegrableOn g (Set.Icc 0 T))
    (hgn : ∀ s ∈ Set.Icc 0 T, 0 ≤ g s)
    (hBg : ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ g s) (x : E) :
    ContinuousOn (fun p : ℝ × ℝ => sum S B p.1 p.2 x) (triangle T) := by
  apply continuousOn_tsum (u := fun n => (∫ s in 0..T, g s)^n / n ! * ‖x‖)
    (fun n => term_joint_continuous S B hT hB g hg hgn hBg n x)
    ((Real.summable_pow_div_factorial _).mul_right _) _
  intro n p hp
  have hBr := fun z => (hB z).mono_set (Set.Icc_subset_Icc hp.1 le_rfl)
  have hgr := hg.mono_set (Set.Icc_subset_Icc hp.1 le_rfl)
  have hnr := fun s (hs : s ∈ Set.Icc p.2 T) => hgn s ⟨hp.1.trans hs.1, hs.2⟩
  have hBgr := fun s (hs : s ∈ Set.Icc p.2 T) => hBg s ⟨hp.1.trans hs.1, hs.2⟩
  apply (term_bound S B (hp.2.1.trans hp.2.2) hBr g hgr hnr hBgr n
    ⟨hp.2.1, hp.2.2⟩ x).trans
  have hn : 0 ≤ ∫ s in p.2..p.1, g s := intervalIntegral.integral_nonneg hp.2.1
    (fun s hs => hgn s ⟨hp.1.trans hs.1, hs.2.trans hp.2.2⟩)
  have hl : (∫ s in p.2..p.1, g s) ≤ ∫ s in 0..T, g s := by
    apply intervalIntegral.integral_mono_interval hp.1 hp.2.1 hp.2.2
      _ ((intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr hg)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hgn s ⟨hs.1.le, hs.2⟩
  gcongr


private theorem sum_restart (S : Contraction E) (B : ℝ → E →L[ℂ] E)
    {T r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hsT : s ≤ T)
    (hB : ∀ x : E, AEStronglyMeasurable (fun q => B q x) (volume.restrict (Set.Icc 0 T)))
    (g : ℝ → ℝ) (hg : IntegrableOn g (Set.Icc 0 T))
    (hgn : ∀ q ∈ Set.Icc 0 T, 0 ≤ g q)
    (hBg : ∀ q ∈ Set.Icc 0 T, ‖B q‖ ≤ g q) (x : E) :
    ∀ t ∈ Set.Icc s T, sum S B t r x = S.action (t-s) (sum S B s r x) +
      ∫ q in s..t, S.action (t-q) (B q (sum S B q r x)) := by
  have hBr := fun z => (hB z).mono_set (Set.Icc_subset_Icc hr le_rfl)
  have hgr := hg.mono_set (Set.Icc_subset_Icc hr le_rfl)
  have hnr := fun q (hq : q ∈ Set.Icc r T) => hgn q ⟨hr.trans hq.1, hq.2⟩
  have hBgr := fun q (hq : q ∈ Set.Icc r T) => hBg q ⟨hr.trans hq.1, hq.2⟩
  have hSc := sum_continuous S B (hrs.trans hsT) hBr g hgr hnr hBgr x
  intro t ht
  have htr : t ∈ Set.Icc r T := ⟨hrs.trans ht.1, ht.2⟩
  have hsr : s ∈ Set.Icc r T := ⟨hrs, hsT⟩
  have hi : ∀ u ∈ Set.Icc r T, IntervalIntegrable
      (fun q => S.action (u-q) (B q (sum S B q r x))) volume r u :=
    (causal_regular S hBr hgr hBgr hSc).2
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    ((hi t htr).mono_set (by
      rw [Set.uIcc_of_le hrs, Set.uIcc_of_le htr.1]
      exact Set.Icc_subset_Icc le_rfl ht.1))
    ((hi t htr).mono_set (by
      rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le htr.1]
      exact Set.Icc_subset_Icc hrs le_rfl))
  have hfirst : (∫ q in r..s, S.action (t-q) (B q (sum S B q r x))) =
      S.action (t-s) (∫ q in r..s, S.action (s-q) (B q (sum S B q r x))) := by
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ (hi s hsr)]
    apply intervalIntegral.integral_congr
    intro q hq
    rw [Set.uIcc_of_le hrs] at hq
    dsimp only
    rw [show t-q = (t-s)+(s-q) by ring,
      action_add S (sub_nonneg.mpr ht.1) (sub_nonneg.mpr hq.2)]
    rfl
  rw [sum_mild S B (hrs.trans hsT) hBr g hgr hnr hBgr htr x, ← hsplit, hfirst,
    sum_mild S B (hrs.trans hsT) hBr g hgr hnr hBgr hsr x, map_add]
  rw [show t-r = (t-s)+(s-r) by ring,
    action_add S (sub_nonneg.mpr ht.1) (sub_nonneg.mpr hrs)]
  simp only [ContinuousLinearMap.comp_apply, add_assoc]

/-- The complete measurable-coefficient evolution uses the original ordered Bochner series. -/
theorem measurable_evolution (S : Contraction E) :
    ∃ Phi : (ℝ → E →L[ℂ] E) → ℝ → ℝ → E →L[ℂ] E,
    ∀ (B : ℝ → E →L[ℂ] E) (T : ℝ), 0 ≤ T →
    (∀ x : E, AEStronglyMeasurable (fun s => B s x) (volume.restrict (Set.Icc 0 T))) →
    ∀ (g : ℝ → ℝ), IntegrableOn g (Set.Icc 0 T) →
    (∀ s ∈ Set.Icc 0 T, 0 ≤ g s) → (∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ g s) →
    (∀ r ∈ Set.Icc 0 T, ∀ v : ℝ → E, ContinuousOn v (Set.Icc r T) →
      ContinuousOn (causal S B r v) (Set.Icc r T) ∧
      ∀ t ∈ Set.Icc r T, IntervalIntegrable
        (fun s => S.action (t-s) (B s (v s))) volume r t) ∧
    (∀ n t r, (t,r) ∈ triangle T → ∀ x : E,
      IntervalIntegrable (fun s => S.action (t-s) (B s (term S B n s r x))) volume r t) ∧
    (∀ n t r, (t,r) ∈ triangle T → ∀ x : E,
      ‖term S B n t r x‖ ≤ (∫ s in r..t, g s)^n / n ! * ‖x‖) ∧
    (∀ t r, (t,r) ∈ triangle T → ∀ x : E,
      Summable (fun n => ‖term S B n t r x‖) ∧
      HasSum (fun n => term S B n t r x) (Phi B t r x)) ∧
    (∀ x : E, ContinuousOn (fun p : ℝ × ℝ => Phi B p.1 p.2 x) (triangle T)) ∧
    (∀ t r, (t,r) ∈ triangle T → ∀ x : E,
      Phi B t r x = S.action (t-r) x +
        ∫ s in r..t, S.action (t-s) (B s (Phi B s r x))) ∧
    (∀ r ∈ Set.Icc 0 T, Phi B r r = 1) ∧
    (∀ r ∈ Set.Icc 0 T, ∀ (X : ℝ → E) (x : E), ContinuousOn X (Set.Icc r T) →
      (∀ t ∈ Set.Icc r T, X t = S.action (t-r) x +
        ∫ s in r..t, S.action (t-s) (B s (X s))) →
      ∀ t ∈ Set.Icc r T, X t = Phi B t r x) ∧
    (∀ r s t, 0 ≤ r → r ≤ s → s ≤ t → t ≤ T →
      (Phi B t s).comp (Phi B s r) = Phi B t r) ∧
    (∀ t r, (t,r) ∈ triangle T → ‖Phi B t r‖ ≤ Real.exp (∫ s in r..t, g s)) ∧
    (∀ n r x, term S B (n+1) r r x = 0) ∧
    (∀ (Q : ℝ → E →L[ℂ] E) t r, (t,r) ∈ triangle T →
      Set.EqOn B Q (Set.Icc r t) → Phi B t r = Phi Q t r) ∧
    ((∀ x : E, ContinuousOn (fun s => B s x) (Set.Icc 0 T)) →
      ∀ t r, (t,r) ∈ triangle T →
      Phi B t r = StrongNonautonomousDysonPhillips.strongEvolution S B t r) ∧
    (∀ Z : E →L[ℂ] E, Set.EqOn B (fun _ => Z) (Set.Icc 0 T) →
      ∀ t r, (t,r) ∈ triangle T → ∀ x : E, Phi B t r x =
        DysonPhillipsPerturbation.dysonSum S.action Z (t-r) x) ∧
    (Set.EqOn B (fun _ => 0) (Set.Icc 0 T) → ∀ t r, (t,r) ∈ triangle T →
      Phi B t r = S.action (t-r)) := by
  refine ⟨measurableEvolution S, ?_⟩
  intro B T hT hB g hg hgn hBg
  have hBr := fun r (hr : 0 ≤ r) z =>
    (hB z).mono_set (Set.Icc_subset_Icc hr le_rfl)
  have hgr := fun r (hr : 0 ≤ r) => hg.mono_set (Set.Icc_subset_Icc hr le_rfl)
  have hnr := fun r (hr : 0 ≤ r) s (hs : s ∈ Set.Icc r T) => hgn s ⟨hr.trans hs.1, hs.2⟩
  have hBgr := fun r (hr : 0 ≤ r) s (hs : s ∈ Set.Icc r T) => hBg s ⟨hr.trans hs.1, hs.2⟩
  have happly : ∀ t r, (t,r) ∈ triangle T → ∀ x : E,
      measurableEvolution S B t r x = sum S B t r x := fun t r h x =>
    measurableEvolution_apply S B (h.2.1.trans h.2.2) (hBr r h.1) g
      (hgr r h.1) (hnr r h.1) (hBgr r h.1) ⟨h.2.1, h.2.2⟩ x
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr v hv
    exact causal_regular S (hBr r hr.1) (hgr r hr.1) (hBgr r hr.1) hv
  · intro n t r h x
    exact term_integrable S B (h.2.1.trans h.2.2) (hBr r h.1) g
      (hgr r h.1) (hnr r h.1) (hBgr r h.1) n x ⟨h.2.1, h.2.2⟩
  · intro n t r h x
    exact term_bound S B (h.2.1.trans h.2.2) (hBr r h.1) g
      (hgr r h.1) (hnr r h.1) (hBgr r h.1) n ⟨h.2.1, h.2.2⟩ x
  · intro t r h x
    rw [happly t r h x]
    exact measurable_series S B (h.2.1.trans h.2.2) (hBr r h.1) g
      (hgr r h.1) (hnr r h.1) (hBgr r h.1) ⟨h.2.1, h.2.2⟩ x
  · intro x
    apply (sum_joint_continuous S B hT hB g hg hgn hBg x).congr
    intro p hp
    exact happly p.1 p.2 hp x
  · intro t r h x
    rw [happly t r h x, sum_mild S B (h.2.1.trans h.2.2) (hBr r h.1) g
      (hgr r h.1) (hnr r h.1) (hBgr r h.1) ⟨h.2.1, h.2.2⟩ x]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le h.2.1] at hs
    dsimp only
    rw [happly s r ⟨h.1, hs.1, hs.2.trans h.2.2⟩ x]
  · intro r hr
    ext x
    rw [happly r r ⟨hr.1, le_rfl, hr.2⟩ x, sum_diagonal]
    rfl
  · intro r hr X x hX heq t ht
    rw [happly t r ⟨hr.1, ht.1, ht.2⟩ x]
    exact sum_unique S B hr.2 (hBr r hr.1) g (hgr r hr.1)
      (hnr r hr.1) (hBgr r hr.1) hX x heq t ht
  · intro r s t hr hrs hst htT
    ext x
    change measurableEvolution S B t s (measurableEvolution S B s r x) =
      measurableEvolution S B t r x
    rw [happly s r ⟨hr, hrs, hst.trans htT⟩ x,
      happly t s ⟨hr.trans hrs, hst, htT⟩, happly t r ⟨hr, hrs.trans hst, htT⟩ x]
    exact (sum_unique S B (hst.trans htT) (hBr s (hr.trans hrs)) g
      (hgr s (hr.trans hrs)) (hnr s (hr.trans hrs)) (hBgr s (hr.trans hrs))
      ((sum_continuous S B (hrs.trans (hst.trans htT)) (hBr r hr) g
        (hgr r hr) (hnr r hr) (hBgr r hr) x).mono (Set.Icc_subset_Icc hrs le_rfl))
      (sum S B s r x) (sum_restart S B hr hrs (hst.trans htT) hB g hg hgn hBg x)
      t ⟨hst, htT⟩).symm
  · intro t r h
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
    intro x
    rw [happly t r h x]
    exact sum_bound S B (h.2.1.trans h.2.2) (hBr r h.1) g
      (hgr r h.1) (hnr r h.1) (hBgr r h.1) ⟨h.2.1, h.2.2⟩ x
  · intro n r x
    simp [term_succ]
  · intro Q t r h heq
    have hBt := fun z => (hB z).mono_set (Set.Icc_subset_Icc h.1 h.2.2)
    have hQt : ∀ z : E, AEStronglyMeasurable (fun s => Q s z)
        (volume.restrict (Set.Icc r t)) := by
      intro z
      apply (hBt z).congr
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      rw [heq hs]
    have hgt := hg.mono_set (Set.Icc_subset_Icc h.1 h.2.2)
    have hnt := fun s (hs : s ∈ Set.Icc r t) => hgn s ⟨h.1.trans hs.1, hs.2.trans h.2.2⟩
    have hQgt : ∀ s ∈ Set.Icc r t, ‖Q s‖ ≤ g s := fun s hs => by
      rw [← heq hs]
      exact hBg s ⟨h.1.trans hs.1, hs.2.trans h.2.2⟩
    ext x
    rw [happly t r h x,
      measurableEvolution_apply S Q h.2.1 hQt g hgt hnt hQgt ⟨h.2.1, le_rfl⟩ x]
    exact tsum_congr fun n => term_locality S B heq n ⟨h.2.1, le_rfl⟩ x
  · intro hcont t r h
    obtain ⟨⟨M,hM,hBM⟩, hall⟩ := StrongNonautonomousDysonPhillips.fullstrongconstruction S B hT hcont
    ext x
    rw [happly t r h x]
    exact (measurable_series S B (h.2.1.trans h.2.2) (hBr r h.1) g
      (hgr r h.1) (hnr r h.1) (hBgr r h.1) ⟨h.2.1,h.2.2⟩ x).2.unique
      ((hall M hM hBM).2.1 t r h x)
  · intro Z heq t r h x
    rw [happly t r h x]
    simp only [sum, DysonPhillipsPerturbation.dysonSum, max_eq_left (sub_nonneg.mpr h.2.1)]
    exact tsum_congr fun n =>
      (term_locality S B (heq.mono (Set.Icc_subset_Icc h.1 le_rfl)) n ⟨h.2.1,h.2.2⟩ x).trans (term_constant S Z n t r x)
  · intro heq t r h
    ext x
    rw [happly t r h x]
    calc
      _ = sum S (fun _ => 0) t r x := tsum_congr fun n =>
        term_locality S B (heq.mono (Set.Icc_subset_Icc h.1 le_rfl)) n ⟨h.2.1,h.2.2⟩ x
      _ = _ := sum_zero_coefficient S t r x

end D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips
