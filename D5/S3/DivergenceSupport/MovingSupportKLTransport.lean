/- GID: D5/S3/DivergenceSupport/MovingSupportKLTransport
   generality: I
   mirror-B: D5/B/S3/DivergenceSupport/MovingSupportKLTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Common-record likelihood ratios give moving-support KL tail bounds and L1 limits. -/
import D5.S3.DivergenceSupport.Garbling.DeterministicGarbling
import D5.S3.Observer.ProductMeasures.FinitePmfLikelihood
import Mathlib.MeasureTheory.Function.UniformIntegrable
import D5.S3.Divergence.GibbsEquality
import D5.S3.Entropy.Forgetting.CompletionEntropyMinimality
import D5.S3.Entropy.Forgetting.PushforwardComposition
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.InfinitePi
open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
namespace D5.S3.DivergenceSupport.MovingSupportKLTransport
open D5.S3.Divergence.ClassicalDPI
open D5.S3.Divergence.GrandmotherTheorem
open D5.S3.DivergenceSupport.ZeroSupportDPI
open D5.S3.DivergenceSupport.Garbling.DeterministicGarbling
open D5.S3.Entropy.Forgetting.CapacityMonotone
/-- The scalar posterior KL loss, set to zero on actual null records. Posterior vectors
are used only in the positive-evidence branch. -/
def posteriorDefect {J I H : Type*} [Fintype J] [Fintype I]
    (d q : J → ℝ) (W : J → H → ℝ) (r : J → I) (h : H) : ℝ := if 0 < channelOutput W d h then
    klDivergence (posterior W d h) (posterior W q h) -
      klDivergence (pushforward r (posterior W d h))
        (pushforward r (posterior W q h))
  else 0
private lemma posterior_mass {J H : Type*} [Fintype J]
    (W : J → H → ℝ) (hW : ∀ j h, 0 ≤ W j h) (h : H)
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hP : 0 < channelOutput W p h) :
    (∀ j, 0 ≤ posterior W p h j) ∧ ∑ j, posterior W p h j = 1 := by
  refine ⟨fun j => div_nonneg (mul_nonneg (hp j) (hW j h)) hP.le, ?_⟩
  simpa only [posterior, ← Finset.sum_div, channelOutput] using div_self hP.ne'
private lemma posterior_defect_bounds {J I H : Type*} [Fintype J] [Fintype I]
    (d q : J → ℝ) (W : J → H → ℝ) (r : J → I)
    (hd : (∀ j, 0 ≤ d j) ∧ ∑ j, d j = 1) (hq : ∀ j, 0 < q j) (hW : ∀ j h, 0 ≤ W j h)
    {M : ℝ} (hM : 0 < M) (hdom : ∀ j, d j ≤ M * q j)
    (h : H) (hD : 0 < channelOutput W d h) :
    0 < channelOutput W q h ∧ 0 ≤ posteriorDefect d q W r h ∧
      posteriorDefect d q W r h ≤
        Real.log (M / (channelOutput W d h / channelOutput W q h)) := by classical
  have hQnn : 0 ≤ channelOutput W q h := Finset.sum_nonneg fun j _ => mul_nonneg (hq j).le (hW j h)
  have hQ : 0 < channelOutput W q h := by
    refine lt_of_le_of_ne hQnn ?_
    intro he
    have := channel_output_absolute_continuity d q W (fun j => (hq j).le)
      (fun j hj => False.elim ((hq j).ne' hj)) hW h he.symm
    linarith
  have hpd := posterior_mass W hW h d hd.1 hD
  have hpq := posterior_mass W hW h q (fun j => (hq j).le) hQ
  have hac : ∀ j, posterior W q h j = 0 → posterior W d h j = 0 := by
    intro j hj
    have hz : W j h = 0 := by
      simpa only [posterior, div_eq_zero_iff, mul_eq_zero, (hq j).ne', hQ.ne',
        false_or, or_false] using hj
    simp [posterior, hz]
  have hpushac : ∀ i, pushforward r (posterior W q h) i = 0 →
      pushforward r (posterior W d h) i = 0 := by
    intro i hi
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => show 0 ≤ (if r j = i then posterior W q h j else 0) from
        by split_ifs <;> simp_all only [le_refl])).mp hi
    apply Finset.sum_eq_zero
    intro j hj
    split_ifs with he
    · exact hac j (by simpa [he] using hz j hj)
    · rfl
  have hcoarse := kl_divergence_nonneg _ _ (D5.S3.Entropy.Forgetting.CompletionEntropyMinimality.pushforward_is_law _ r hpd)
    (D5.S3.Entropy.Forgetting.CompletionEntropyMinimality.pushforward_is_law _ r hpq) hpushac
  have hkl : klDivergence (posterior W d h) (posterior W q h) ≤
      Real.log (M / (channelOutput W d h / channelOutput W q h)) := by
    calc
      _ ≤ ∑ j, posterior W d h j *
          Real.log (M / (channelOutput W d h / channelOutput W q h)) := by
        apply Finset.sum_le_sum; intro j _
        by_cases hj : posterior W d h j = 0
        · simp [hj]
        have hdp : 0 < posterior W d h j := lt_of_le_of_ne (hpd.1 j) (Ne.symm hj)
        have hqp : 0 < posterior W q h j := lt_of_le_of_ne (hpq.1 j) (Ne.symm (mt (hac j) hj))
        apply mul_le_mul_of_nonneg_left _ hdp.le
        apply Real.log_le_log (div_pos hdp hqp)
        rw [div_le_iff₀ hqp]
        dsimp only [posterior]
        calc
          _ ≤ (M * q j * W j h) / channelOutput W d h := div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hdom j) (hW j h)) hD.le
          _ = _ := by field_simp [hD.ne', hQ.ne']
      _ = _ := by rw [← Finset.sum_mul, hpd.2, one_mul]
  rw [posteriorDefect, if_pos hD]
  exact ⟨hQ, deterministic_forgetting_kl_loss_nonnegative _ _ r hpd hpq hac,
    (sub_le_self _ hcoarse).trans hkl⟩
private lemma posterior_density_bound {J H : Type*} [Fintype J]
    (d q : J → ℝ) (W : J → H → ℝ) {M : ℝ}
    (hdom : ∀ j, d j ≤ M * q j) (hW : ∀ j h, 0 ≤ W j h)
    (h : H) (hD : 0 < channelOutput W d h) (hQ : 0 < channelOutput W q h) (j : J) :
    posterior W d h j ≤
      (M / (channelOutput W d h / channelOutput W q h)) * posterior W q h j := by
  dsimp only [posterior]
  calc
    _ ≤ (M * q j * W j h) / channelOutput W d h := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hdom j) (hW j h)) hD.le
    _ = _ := by field_simp [hD.ne', hQ.ne']
private lemma likelihood_weighted_tail {D Q M f R : ℝ}
    (hD : 0 < D) (hQ : 0 < Q) (hM : 0 < M)
    (hR : 0 ≤ R) (hfR : R ≤ f) (hf : f ≤ Real.log (M / (D / Q))) :
    D * f ≤ Q * (M * (R + 1) * Real.exp (-R)) := by
  let u := Real.log (M / (D / Q))
  have hRu : R ≤ u := hfR.trans hf
  have he : Real.exp u = M / (D / Q) := Real.exp_log (by positivity)
  have hDrep : D = Q * M * Real.exp (-u) := by
    rw [Real.exp_neg, he]
    field_simp
  have hscalar : u ≤ (R + 1) * Real.exp (u - R) := by
    have hlin := Real.add_one_le_exp (u - R)
    have hexp : 1 ≤ Real.exp (u - R) := Real.one_le_exp_iff.mpr (sub_nonneg.mpr hRu)
    nlinarith [mul_nonneg hR (sub_nonneg.mpr hexp)]
  calc
    D * f ≤ D * u := mul_le_mul_of_nonneg_left hf hD.le
    _ = Q * M * (u * Real.exp (-u)) := by rw [hDrep]; ring
    _ ≤ Q * M * ((R + 1) * Real.exp (-R)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hQ.le hM.le)
      calc
        _ ≤ ((R + 1) * Real.exp (u - R)) * Real.exp (-u) := mul_le_mul_of_nonneg_right hscalar (Real.exp_pos _).le
        _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ = _ := by ring
private lemma finite_record_integral {Ω H : Type*} [MeasurableSpace Ω]
    [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]
    (μ : Measure Ω) [IsFiniteMeasure μ] (record : Ω → H) (hr : Measurable record)
    (D : H → ℝ) (hmass : ∀ h, μ.real (record ⁻¹' {h}) = D h) (f : H → ℝ) :
    ∫ ω, f (record ω) ∂μ = ∑ h, D h * f h := by
  rw [← integral_map hr.aemeasurable (by exact .of_discrete),
    integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl; intro h _; rw [map_measureReal_apply hr (measurableSet_singleton h), hmass, smul_eq_mul]
private lemma finite_record_tail {Ω H : Type*} [MeasurableSpace Ω]
    [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]
    (μ : Measure Ω) [IsFiniteMeasure μ] (record : Ω → H) (hr : Measurable record)
    (D Q f : H → ℝ) (hmass : ∀ h, μ.real (record ⁻¹' {h}) = D h)
    (hD : ∀ h, 0 ≤ D h) (hQ : ∀ h, 0 ≤ Q h) (hQsum : ∑ h, Q h = 1)
    (hac : ∀ h, 0 < D h → 0 < Q h) {M : ℝ} (hM : 0 < M)
    (hf : ∀ h, 0 < D h → f h ≤ Real.log (M / (D h / Q h)))
    {R : ℝ} (hR : 0 ≤ R) :
    ∫ ω, ({ω | R ≤ f (record ω)}.indicator (fun ω => f (record ω))) ω ∂μ ≤
      M * (R + 1) * Real.exp (-R) := by classical
  rw [show (fun ω => ({ω | R ≤ f (record ω)}.indicator
      (fun ω => f (record ω))) ω) =
      (fun ω => (if R ≤ f (record ω) then f (record ω) else 0)) from rfl,
    finite_record_integral μ record hr D hmass (fun h => if R ≤ f h then f h else 0)]
  calc
    _ ≤ ∑ h, Q h * (M * (R + 1) * Real.exp (-R)) := by
      apply Finset.sum_le_sum; intro h _
      by_cases hd : 0 < D h
      · split_ifs with hfr
        · exact likelihood_weighted_tail hd (hac h hd) hM hR hfr (hf h hd)
        · simp only [mul_zero]
          exact mul_nonneg (hQ h) (by positivity)
      · have hz : D h = 0 := le_antisymm (le_of_not_gt hd) (hD h)
        rw [hz, zero_mul]
        exact mul_nonneg (hQ h) (by positivity)
    _ = _ := by rw [← Finset.sum_mul, hQsum, one_mul]
private lemma finite_record_log_tail {Ω H : Type*} [MeasurableSpace Ω]
    [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]
    (μ : Measure Ω) [IsFiniteMeasure μ] (record : Ω → H) (hr : Measurable record)
    (D Q : H → ℝ) (hmass : ∀ h, μ.real (record ⁻¹' {h}) = D h)
    (hQ : ∀ h, 0 ≤ Q h) (hQsum : ∑ h, Q h = 1)
    (hac : ∀ h, 0 < D h → 0 < Q h) {M : ℝ} (hM : 0 < M)
    {v : ℝ} (hv : 0 ≤ v) :
    μ.real {ω | v < if 0 < D (record ω) then
      Real.log (M / (D (record ω) / Q (record ω))) else 0} ≤ M * Real.exp (-v) := by classical
  let U : H → ℝ := fun h => if 0 < D h then Real.log (M / (D h / Q h)) else 0
  have hm : Measurable (fun ω => U (record ω)) := (measurable_of_countable U).comp hr
  change μ.real {ω | v < U (record ω)} ≤ _
  rw [← integral_indicator_one (measurableSet_lt measurable_const hm)]
  change (∫ ω, (if v < U (record ω) then (1 : ℝ) else 0) ∂μ) ≤ _
  rw [finite_record_integral μ record hr D hmass (fun h => if v < U h then 1 else 0)]
  calc
    _ ≤ ∑ h, Q h * (M * Real.exp (-v)) := by
      apply Finset.sum_le_sum; intro h _
      by_cases hu : v < U h
      · rw [if_pos hu, mul_one]
        have hd : 0 < D h := by
          by_contra hn
          simp only [U, if_neg hn] at hu
          exact (not_lt_of_ge hv) hu
        have hq := hac h hd
        have he : Real.exp v < M / (D h / Q h) := by
          rw [← Real.exp_log (div_pos hM (div_pos hd hq))]
          exact Real.exp_lt_exp.mpr (by simpa only [U, if_pos hd] using hu)
        rw [div_div_eq_mul_div, lt_div_iff₀ hd] at he
        have ht : D h < (Q h * M) / Real.exp v := (lt_div_iff₀ (Real.exp_pos v)).mpr (by nlinarith)
        simpa only [Real.exp_neg, div_eq_mul_inv, mul_assoc] using ht.le
      · rw [if_neg hu, mul_zero]
        exact mul_nonneg (hQ h) (mul_nonneg hM.le (Real.exp_pos _).le)
    _ = _ := by rw [← Finset.sum_mul, hQsum, one_mul]
/-- A single actual law realizes all finite records. A fixed prior density bound gives
a uniform exponential tail bound for the moving-support KL defects. Consequently
every almost-sure limit is an L1 limit and its expectation is the limit of expectations.
The finite-record mass identity is explicit; no independence of the mixed records is assumed. -/
theorem posterior_defect_l1_of_ae_tendsto
    {J I Ω : Type*} {H : ℕ → Type*} [Fintype J] [Fintype I] [MeasurableSpace Ω] [∀ n, Fintype (H n)]
    [∀ n, MeasurableSpace (H n)] [∀ n, MeasurableSingletonClass (H n)]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (record : (n : ℕ) → Ω → H n) (hr : ∀ n, Measurable (record n))
    (d q : J → ℝ) (W : (n : ℕ) → J → H n → ℝ) (r : J → I)
    (hd : (∀ j, 0 ≤ d j) ∧ ∑ j, d j = 1) (hq : (∀ j, 0 < q j) ∧ ∑ j, q j = 1)
    (hW : ∀ n, (∀ j h, 0 ≤ W n j h) ∧ ∀ j, ∑ h, W n j h = 1)
    (hmass : ∀ n h, μ.real (record n ⁻¹' {h}) = channelOutput (W n) d h)
    {M : ℝ} (hM : 0 < M) (hdom : ∀ j, d j ≤ M * q j)
    (g : Ω → ℝ)
    (hlim : ∀ᵐ ω ∂μ, Tendsto
      (fun n => posteriorDefect d q (W n) r (record n ω)) atTop (𝓝 (g ω))) :
    let f := fun n ω => posteriorDefect d q (W n) r (record n ω)
    (∀ v : ℝ, 0 ≤ v → ∀ n,
      μ.real {ω | v < if 0 < channelOutput (W n) d (record n ω) then
        Real.log (M / (channelOutput (W n) d (record n ω) /
          channelOutput (W n) q (record n ω))) else 0} ≤ M * Real.exp (-v)) ∧
    (∀ R : ℝ, 0 ≤ R → ∀ n,
      (∫ ω, ({ω | R ≤ f n ω}.indicator (f n)) ω ∂μ) ≤
        M * (R + 1) * Real.exp (-R)) ∧
    UniformIntegrable f 1 μ ∧ Integrable g μ ∧
    Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0) ∧
    Tendsto (fun n => ∫ ω, f n ω ∂μ) atTop (𝓝 (∫ ω, g ω ∂μ)) := by classical
  dsimp only
  let f := fun n ω => posteriorDefect d q (W n) r (record n ω)
  have hb n h (hh : 0 < channelOutput (W n) d h) := posterior_defect_bounds d q (W n) r hd hq.1 (hW n).1 hM hdom h hh
  have hnonneg n ω : 0 ≤ f n ω := by
    by_cases hh : 0 < channelOutput (W n) d (record n ω)
    · exact (hb n _ hh).2.1
    · simp [f, posteriorDefect, hh]
  have hint n : Integrable (f n) μ := (Integrable.of_finite (μ := μ.map (record n))
      (f := posteriorDefect d q (W n) r)).comp_measurable (hr n)
  have hfmeas n : Measurable (f n) := (measurable_of_countable (posteriorDefect d q (W n) r)).comp (hr n)
  have hQnn n h : 0 ≤ channelOutput (W n) q h := Finset.sum_nonneg fun j _ => mul_nonneg (hq.1 j).le ((hW n).1 j h)
  have hQsum n : ∑ h, channelOutput (W n) q h = 1 := by
    simp only [channelOutput, Finset.sum_comm (f := fun h j => q j * W n j h),
      ← Finset.mul_sum, (hW n).2, mul_one, hq.2]
  have htail (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
      (∫ ω, ({ω | R ≤ f n ω}.indicator (f n)) ω ∂μ) ≤
        M * (R + 1) * Real.exp (-R) := by
    apply finite_record_tail μ (record n) (hr n)
      (channelOutput (W n) d) (channelOutput (W n) q)
      (posteriorDefect d q (W n) r) (hmass n)
    · intro h; exact Finset.sum_nonneg fun j _ => mul_nonneg (hd.1 j) ((hW n).1 j h)
    · exact hQnn n
    · exact hQsum n
    · exact fun h hh => (hb n h hh).1
    · exact hM
    · exact fun h hh => (hb n h hh).2.2
    · exact hR
  have hdecay : Tendsto (fun R : ℝ => M * (R + 1) * Real.exp (-R)) atTop (𝓝 0) := by
    have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).add
      Real.tendsto_exp_neg_atTop_nhds_zero
    convert ht.const_mul M using 1
    · ext R
      simp only [pow_one]
      ring
    · simp
  have hui : UniformIntegrable f 1 μ := by
    apply uniformIntegrable_of (by norm_num) (by norm_num) (fun n => (hint n).1)
    intro ε hε
    obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ M * (C + 1) * Real.exp (-C) < ε := by
      obtain ⟨a, ha⟩ := eventually_atTop.mp (hdecay.eventually (gt_mem_nhds hε))
      exact ⟨max a 0, le_max_right _ _, ha _ (le_max_left _ _)⟩
    let Cnn : ℝ≥0 := ⟨C, hC0⟩
    refine ⟨Cnn, ?_⟩
    intro n
    change eLpNorm ({ω | Cnn ≤ ‖f n ω‖₊}.indicator (f n)) 1 μ ≤ ENNReal.ofReal ε
    have hset : {ω | Cnn ≤ ‖f n ω‖₊} = {ω | C ≤ f n ω} := by
      ext ω
      change (C ≤ ‖f n ω‖) ↔ C ≤ f n ω
      rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg n ω)]
    have hi : Integrable ({ω | C ≤ f n ω}.indicator (f n)) μ :=
      (hint n).indicator (measurableSet_le measurable_const (hfmeas n))
    rw [hset, eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm hi]
    have hn : (fun ω => ‖({ω | C ≤ f n ω}.indicator (f n)) ω‖) =
        ({ω | C ≤ f n ω}.indicator (f n)) := by
      ext ω
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact Set.indicator_nonneg (fun ω _ => hnonneg n ω) _
    rw [hn]
    exact ENNReal.ofReal_le_ofReal ((htail C hC0 n).trans hC.le)
  have hg : MemLp g 1 μ := hui.memLp_of_ae_tendsto hlim
  have hl1 := tendsto_Lp_finite_of_tendsto_ae (by norm_num : 1 ≤ (1 : ℝ≥0∞))
    (by norm_num : (1 : ℝ≥0∞) ≠ ∞) (fun n => (hint n).1) hg hui.unifIntegrable hlim
  refine ⟨?_, htail, hui, memLp_one_iff_integrable.mp hg, hl1,
    tendsto_integral_of_L1' g hg.1 (Eventually.of_forall hint) hl1⟩
  intro v hv n; exact finite_record_log_tail μ (record n) (hr n) _ _ (hmass n)
    (hQnn n) (hQsum n) (fun h hh => (hb n h hh).1) hM hv
private lemma tendsto_mul_log_ratio {a b : ℕ → ℝ} {A B C : ℝ}
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) (hbound : ∀ᶠ n in atTop, a n ≤ C * b n)
    (hta : Tendsto a atTop (𝓝 A)) (htb : Tendsto b atTop (𝓝 B)) :
    Tendsto (fun n => a n * Real.log (a n / b n)) atTop
      (𝓝 (A * Real.log (A / B))) := by
  have hA : 0 ≤ A := le_of_tendsto_of_tendsto tendsto_const_nhds hta (Eventually.of_forall ha)
  have hB : 0 ≤ B := le_of_tendsto_of_tendsto tendsto_const_nhds htb (Eventually.of_forall hb)
  by_cases hB0 : B = 0
  · have hA0 : A = 0 := by
      have h := le_of_tendsto_of_tendsto hta (htb.const_mul C) hbound
      simp only [hB0, mul_zero] at h
      exact le_antisymm h hA
    rw [hA0, zero_mul]
    obtain ⟨L, hL⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) C)).exists_bound_of_continuousOn
      Real.continuous_mul_log.continuousOn
    apply squeeze_zero_norm' (a := fun n => b n * L)
    · filter_upwards [hbound] with n hn
      by_cases hn0 : b n = 0
      · have han0 : a n = 0 := by rw [hn0, mul_zero] at hn; exact le_antisymm hn (ha n)
        simp [hn0, han0]
      · have hbn : 0 < b n := lt_of_le_of_ne (hb n) (Ne.symm hn0)
        have hx : a n / b n ∈ Icc (0 : ℝ) C := ⟨div_nonneg (ha n) (hb n), (div_le_iff₀ hbn).mpr hn⟩
        have he : a n * Real.log (a n / b n) =
            b n * ((a n / b n) * Real.log (a n / b n)) := by field_simp
        rw [he, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hb n)]
        exact mul_le_mul_of_nonneg_left (hL _ hx) (hb n)
    · simpa [hB0] using htb.mul_const L
  · have hBpos := lt_of_le_of_ne hB (Ne.symm hB0)
    have ht := (Real.continuous_mul_log.tendsto A |>.comp hta).sub
      (hta.mul ((Real.continuousAt_log hB0).tendsto.comp htb))
    have hident {x y : ℝ} (hy : y ≠ 0) :
        x * Real.log (x / y) = x * Real.log x - x * Real.log y := by
      by_cases hx : x = 0
      · simp [hx]
      · rw [Real.log_div hx hy, mul_sub]
    rw [← hident hB0] at ht
    apply ht.congr'
    filter_upwards [htb.eventually (Ioi_mem_nhds hBpos)] with n hn
    exact (hident (ne_of_gt hn)).symm
private lemma kl_tendsto_of_dominated {J : Type*} [Fintype J]
    {a b : ℕ → J → ℝ} {A B : J → ℝ} {C : ℝ}
    (ha : ∀ n j, 0 ≤ a n j) (hb : ∀ n j, 0 ≤ b n j) (hbound : ∀ᶠ n in atTop, ∀ j, a n j ≤ C * b n j)
    (hta : ∀ j, Tendsto (fun n => a n j) atTop (𝓝 (A j)))
    (htb : ∀ j, Tendsto (fun n => b n j) atTop (𝓝 (B j))) :
    Tendsto (fun n => klDivergence (a n) (b n)) atTop (𝓝 (klDivergence A B)) := by
  apply tendsto_finsetSum; intro j _; exact tendsto_mul_log_ratio (fun n => ha n j) (fun n => hb n j)
    (hbound.mono fun _ hn => hn j) (hta j) (htb j)
/-- Coordinate limits of both posteriors and a positive limiting evidence ratio suffice
at every support boundary. The resulting KL-loss limit also holds in L1 under the
same actual law. The finite-class identification of the coordinate limits is separate. -/
theorem moving_support_posterior_limit
    {J I Ω : Type*} {H : ℕ → Type*} [Fintype J] [Fintype I] [MeasurableSpace Ω] [∀ n, Fintype (H n)]
    [∀ n, MeasurableSpace (H n)] [∀ n, MeasurableSingletonClass (H n)]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (record : (n : ℕ) → Ω → H n) (hr : ∀ n, Measurable (record n))
    (d q : J → ℝ) (W : (n : ℕ) → J → H n → ℝ) (r : J → I)
    (hd : (∀ j, 0 ≤ d j) ∧ ∑ j, d j = 1) (hq : (∀ j, 0 < q j) ∧ ∑ j, q j = 1)
    (hW : ∀ n, (∀ j h, 0 ≤ W n j h) ∧ ∀ j, ∑ h, W n j h = 1)
    (hmass : ∀ n h, μ.real (record n ⁻¹' {h}) = channelOutput (W n) d h)
    {M : ℝ} (hM : 0 < M) (hdom : ∀ j, d j ≤ M * q j)
    (a b : Ω → J → ℝ) (t : Ω → ℝ)
    (hpath : ∀ᵐ ω ∂μ,
      0 < t ω ∧
      Tendsto (fun n => channelOutput (W n) d (record n ω) /
        channelOutput (W n) q (record n ω)) atTop (𝓝 (t ω)) ∧
      (∀ j, Tendsto (fun n => posterior (W n) d (record n ω) j) atTop (𝓝 (a ω j))) ∧
      (∀ j, Tendsto (fun n => posterior (W n) q (record n ω) j) atTop (𝓝 (b ω j)))) :
    let f := fun n ω => posteriorDefect d q (W n) r (record n ω)
    let g := fun ω => klDivergence (a ω) (b ω) -
      klDivergence (pushforward r (a ω)) (pushforward r (b ω))
    (∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) ∧
    UniformIntegrable f 1 μ ∧ Integrable g μ ∧
    Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0) ∧
    Tendsto (fun n => ∫ ω, f n ω ∂μ) atTop (𝓝 (∫ ω, g ω ∂μ)) := by classical
  let f := fun n ω => posteriorDefect d q (W n) r (record n ω)
  let g := fun ω => klDivergence (a ω) (b ω) -
    klDivergence (pushforward r (a ω)) (pushforward r (b ω))
  have hpositive : ∀ᵐ ω ∂μ, ∀ n, 0 < channelOutput (W n) d (record n ω) := by
    rw [ae_all_iff]; intro n
    refine ae_of_ae_map (μ := μ) (p := fun h => 0 < channelOutput (W n) d h)
      (hr n).aemeasurable ?_
    apply ae_iff_of_countable.mpr
    intro h hh; rw [← hmass n h, ← map_measureReal_apply (hr n) (measurableSet_singleton h)]
    exact ENNReal.toReal_pos hh (by finiteness)
  have hae : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) := by
    filter_upwards [hpath, hpositive] with ω hω hD
    obtain ⟨ht, hT, ha, hb⟩ := hω
    let p := fun n => posterior (W n) d (record n ω)
    let s := fun n => posterior (W n) q (record n ω)
    have hQ n : 0 < channelOutput (W n) q (record n ω) :=
      (posterior_defect_bounds d q (W n) r hd hq.1 (hW n).1 hM hdom _ (hD n)).1
    have hp n j : 0 ≤ p n j := div_nonneg (mul_nonneg (hd.1 j) ((hW n).1 j _)) (hD n).le
    have hs n j : 0 ≤ s n j := div_nonneg (mul_nonneg (hq.1 j).le ((hW n).1 j _)) (hQ n).le
    let C := 2 * M / t ω
    have hbound : ∀ᶠ n in atTop, ∀ j, p n j ≤ C * s n j := by
      filter_upwards [hT.eventually (Ioi_mem_nhds (half_lt_self ht))] with n hn
      intro j
      apply (posterior_density_bound d q (W n) hdom (hW n).1 _ (hD n) (hQ n) j).trans
      apply mul_le_mul_of_nonneg_right _ (hs n j)
      calc
        _ ≤ M / (t ω / 2) := div_le_div_of_nonneg_left hM.le (half_pos ht) hn.le
        _ = C := by dsimp [C]; ring
    have hpushnn (v : J → ℝ) (hv : ∀ j, 0 ≤ v j) i : 0 ≤ pushforward r v i := by
      exact Finset.sum_nonneg fun j _ => by split_ifs <;> simp_all only [le_refl]
    have hpushlim (v : ℕ → J → ℝ) (V : J → ℝ)
        (hv : ∀ j, Tendsto (fun n => v n j) atTop (𝓝 (V j))) i :
        Tendsto (fun n => pushforward r (v n) i) atTop (𝓝 (pushforward r V i)) := by
      apply tendsto_finsetSum; intro j _
      by_cases hj : r j = i
      · simpa only [if_pos hj] using hv j
      · simp only [if_neg hj]
        exact tendsto_const_nhds
    have hpushbound : ∀ᶠ n in atTop, ∀ i,
        pushforward r (p n) i ≤ C * pushforward r (s n) i := by
      filter_upwards [hbound] with n hn
      intro i; simp only [pushforward, Finset.mul_sum]
      apply Finset.sum_le_sum; intro j _
      split_ifs with hj
      · exact hn j
      · simp
    have hk := kl_tendsto_of_dominated hp hs hbound ha hb
    have hc := kl_tendsto_of_dominated
      (fun n => hpushnn _ (hp n)) (fun n => hpushnn _ (hs n)) hpushbound
      (hpushlim p (a ω) ha) (hpushlim s (b ω) hb)
    apply (hk.sub hc).congr'
    exact Eventually.of_forall fun n => by simp only [f, posteriorDefect, if_pos (hD n), p, s]
  have h := posterior_defect_l1_of_ae_tendsto μ record hr d q W r hd hq hW hmass
    hM hdom g hae
  exact ⟨hae, h.2.2⟩
open ProbabilityTheory hiding posterior
open D5.S3.Observer.ProductMeasures.FinitePmfLikelihood
private lemma iid_average {Z : Type*} [Fintype Z]
    [MeasurableSpace Z] [MeasurableSingletonClass Z] (p : PMF Z) (g : Z → ℝ) :
    ∀ᵐ x ∂productLaw (fun _ : ℕ => p),
      Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, g (x k)) / n) atTop
        (𝓝 (∑ z, (p z).toReal * g z)) := by
  let μ := productLaw (fun _ : ℕ => p)
  have hid (n : ℕ) : IdentDistrib (fun x : ℕ → Z => x n) id μ p.toMeasure :=
    ⟨(measurable_pi_apply n).aemeasurable, measurable_id.aemeasurable,
      by simp [μ, productLaw, Measure.infinitePi_map_eval]⟩
  have hg := fun n => (hid n).comp (measurable_of_countable g)
  have hi : Integrable (fun x : ℕ → Z => g (x 0)) μ := (hg 0).integrable_iff.mpr Integrable.of_finite
  have hind := iIndepFun_infinitePi (P := fun _ : ℕ => p.toMeasure)
    (X := fun _ : ℕ => g) (fun _ => measurable_of_countable g)
  have h := strong_law_ae_real (fun n (x : ℕ → Z) => g (x n)) hi
    (fun _ _ hne => hind.indepFun hne) (fun n => (hg n).trans (hg 0).symm)
  have he : (∫ x, g (x 0) ∂μ) = ∑ z, (p z).toReal * g z := by
    calc
      _ = ∫ z, g z ∂p.toMeasure := (hg 0).integral_eq
      _ = _ := by simpa only [smul_eq_mul] using PMF.integral_eq_sum p g
  simpa only [he] using h
private lemma iid_positive {Z : Type*} [Fintype Z]
    [MeasurableSpace Z] [MeasurableSingletonClass Z] (p : PMF Z) :
    ∀ᵐ x ∂productLaw (fun _ : ℕ => p), ∀ k, 0 < (p (x k)).toReal := by
  let μ := productLaw (fun _ : ℕ => p)
  rw [ae_all_iff]; intro k
  apply ae_of_ae_map (μ := μ) (p := fun z => 0 < (p z).toReal)
    (measurable_pi_apply k).aemeasurable
  rw [show μ.map (fun x => x k) = p.toMeasure from
    Measure.infinitePi_map_eval (fun _ : ℕ => p.toMeasure) k]
  apply ae_iff_of_countable.mpr
  intro z hz; exact ENNReal.toReal_pos (by simpa using hz) (PMF.apply_ne_top p z)
private lemma iid_likelihood_ratio {Z : Type*} [Fintype Z]
    [MeasurableSpace Z] [MeasurableSingletonClass Z] (p q : PMF Z) (hne : p ≠ q) :
    ∀ᵐ x ∂productLaw (fun _ : ℕ => p),
      (∀ n, 0 < ∏ k : Fin n, (p (x k)).toReal) ∧
      Tendsto (fun n => (∏ k : Fin n, (q (x k)).toReal) /
        (∏ k : Fin n, (p (x k)).toReal)) atTop (𝓝 0) := by classical
  have hpos := iid_positive p
  by_cases hac : ∀ z, (q z).toReal = 0 → (p z).toReal = 0
  · have hp : (∀ z, 0 ≤ (p z).toReal) ∧ ∑ z, (p z).toReal = 1 :=
      ⟨fun _ => ENNReal.toReal_nonneg, pmfRealMass_sum (Output := fun _ : ℕ => Z) (i := 0) p⟩
    have hq : (∀ z, 0 ≤ (q z).toReal) ∧ ∑ z, (q z).toReal = 1 :=
      ⟨fun _ => ENNReal.toReal_nonneg, pmfRealMass_sum (Output := fun _ : ℕ => Z) (i := 0) q⟩
    have hkl : 0 < klDivergence (fun z => (p z).toReal) (fun z => (q z).toReal) := by
      apply lt_of_le_of_ne (kl_divergence_nonneg _ _ hp hq hac)
      intro hzero
      have he := (D5.S3.Divergence.GibbsEquality.kl_divergence_eq_zero_iff _ _ hp hq hac).mp hzero.symm
      apply hne
      ext z
      exact (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top p z) (PMF.apply_ne_top q z)).mp (congrFun he z)
    have hm := iid_average p (fun z => Real.log ((q z).toReal / (p z).toReal))
    have he : (∑ z, (p z).toReal * Real.log ((q z).toReal / (p z).toReal)) =
        -klDivergence (fun z => (p z).toReal) (fun z => (q z).toReal) := by
      simp only [klDivergence, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro z _
      by_cases hz : (p z).toReal = 0
      · simp [hz]
      · have hqz : (q z).toReal ≠ 0 := mt (hac z) hz
        rw [Real.log_div hqz hz, Real.log_div hz hqz]
        ring
    rw [he] at hm
    filter_upwards [hpos, hm] with x hx hmean
    have hqpos k : 0 < (q (x k)).toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm (mt (hac _) (hx k).ne'))
    refine ⟨fun n => Finset.prod_pos (fun _ _ => hx _), ?_⟩
    have hs : Tendsto (fun n => ∑ k ∈ Finset.range n,
        Real.log ((q (x k)).toReal / (p (x k)).toReal)) atTop atBot := by
      have ht := hmean.neg_mul_atTop (neg_neg_of_pos hkl) tendsto_natCast_atTop_atTop
      apply ht.congr'
      filter_upwards [eventually_gt_atTop 0] with n hn
      simp [ne_of_gt hn]
    have hh := Real.tendsto_exp_atBot.comp hs
    apply hh.congr; intro n; simp only [Function.comp_apply]; rw [Real.exp_sum, ← Finset.prod_div_distrib, ← Fin.prod_univ_eq_prod_range]
    apply Finset.prod_congr rfl
    intro k _; exact Real.exp_log (div_pos (hqpos k) (hx k))
  · push_neg at hac
    obtain ⟨z, hqz, hpz⟩ := hac
    have hm := iid_average p (fun y => if y = z then (1 : ℝ) else 0)
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hm
    filter_upwards [hpos, hm] with x hx hmean
    have hex : ∃ k, x k = z := by
      by_contra hn
      push_neg at hn
      simp only [hn, if_false, Finset.sum_const_zero, zero_div] at hmean
      exact hpz (tendsto_nhds_unique hmean tendsto_const_nhds)
    obtain ⟨k, hk⟩ := hex
    refine ⟨fun n => Finset.prod_pos (fun _ _ => hx _), ?_⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop k] with n hn
    have hz : (∏ i : Fin n, (q (x i)).toReal) = 0 := Finset.prod_eq_zero (Finset.mem_univ ⟨k, hn⟩) (by simpa [hk] using hqz)
    simp [hz]
private lemma iid_class_ratios {J S Z : Type*} [DecidableEq S] [Fintype J] [Fintype Z]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (K : J → PMF Z) (s : J → S) (hs : ∀ j k, s j = s k ↔ K j = K k) (k : J) :
    ∀ᵐ x ∂productLaw (fun _ : ℕ => K k),
      (∀ n, 0 < ∏ i : Fin n, (K k (x i)).toReal) ∧
      ∀ j, Tendsto (fun n => (∏ i : Fin n, (K j (x i)).toReal) /
        (∏ i : Fin n, (K k (x i)).toReal)) atTop (𝓝 (if s j = s k then 1 else 0)) := by classical
  have hpos := iid_positive (K k)
  have hrat : ∀ j, ∀ᵐ x ∂productLaw (fun _ : ℕ => K k),
      Tendsto (fun n => (∏ i : Fin n, (K j (x i)).toReal) /
        (∏ i : Fin n, (K k (x i)).toReal)) atTop (𝓝 (if s j = s k then 1 else 0)) := by
    intro j
    by_cases hj : s j = s k
    · filter_upwards [hpos] with x hx
      have he := (hs j k).mp hj
      rw [if_pos hj]
      apply tendsto_const_nhds.congr; intro n; rw [he]; exact (div_self (Finset.prod_pos (fun (i : Fin n) _ => hx i)).ne').symm
    · simpa only [if_neg hj] using
        (iid_likelihood_ratio (K k) (K j) (fun he => hj ((hs j k).mpr he.symm))).mono
          (fun _ h => h.2)
  filter_upwards [hpos, ae_all_iff.mpr hrat] with x hx hr
  exact ⟨fun n => Finset.prod_pos (fun i _ => hx i), hr⟩
private lemma class_posterior_limit {J S : Type*} [DecidableEq S] [Fintype J]
    (p : J → ℝ) (s : J → S) (k : J) (L : ℕ → J → ℝ)
    (hL : ∀ n, 0 < L n k)
    (hlim : ∀ j, Tendsto (fun n => L n j / L n k) atTop
      (𝓝 (if s j = s k then 1 else 0)))
    (hp : channelOutput (fun j c => if s j = c then 1 else 0) p (s k) ≠ 0) :
    Tendsto (fun n => (∑ j, p j * L n j) / L n k) atTop
      (𝓝 (channelOutput (fun j c => if s j = c then 1 else 0) p (s k))) ∧
    ∀ j, Tendsto (fun n => p j * L n j / (∑ i, p i * L n i)) atTop
      (𝓝 (posterior (fun j c => if s j = c then 1 else 0) p (s k) j)) := by classical
  have ht := tendsto_finsetSum Finset.univ (fun j _ => (hlim j).const_mul (p j))
  have hsum : Tendsto (fun n => (∑ j, p j * L n j) / L n k) atTop
      (𝓝 (channelOutput (fun j c => if s j = c then 1 else 0) p (s k))) := by
    simpa only [channelOutput, Finset.sum_div, mul_div_assoc] using ht
  refine ⟨hsum, fun j => ?_⟩
  have hh := ((hlim j).const_mul (p j)).div hsum hp
  convert hh using 1
  · ext n
    change p j * L n j / (∑ x, p x * L n x) =
      (p j * (L n j / L n k)) / ((∑ x, p x * L n x) / L n k)
    rw [← mul_div_assoc, div_div_div_cancel_right₀ (hL n).ne']
  · rfl
private lemma iid_class_decoder {J S Z : Type*} [Fintype J] [Nonempty J]
    [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace S] (K : J → PMF Z) (s : J → S) (hs : ∀ j k, s j = s k ↔ K j = K k) :
    ∃ dec : (ℕ → Z) → S, Measurable dec ∧
      ∀ k, ∀ᵐ x ∂productLaw (fun _ : ℕ => K k), dec x = s k := by classical
  let freq := fun n (x : ℕ → Z) z => (∑ i ∈ Finset.range n, if x i = z then (1 : ℝ) else 0) / n
  let good := fun j x => ∀ z, Tendsto (fun n => freq n x z) atTop (𝓝 (K j z).toReal)
  have hgood j : MeasurableSet {x | good j x} := by
    simp only [good, setOf_forall]
    apply MeasurableSet.iInter; intro z
    apply measurableSet_tendsto_fun _ measurable_const
    intro n; exact (Finset.measurable_sum _ (fun i _ =>
      (measurable_of_countable (fun y : Z => if y = z then (1 : ℝ) else 0)).comp
        (measurable_pi_apply i))).div_const _
  let code : (ℕ → Z) → (J → Bool) := fun x j => decide (good j x)
  have hcode : Measurable code := by
    apply measurable_pi_lambda; intro j
    apply measurable_to_bool
    simpa only [code, preimage, mem_singleton_iff, decide_eq_true_eq] using hgood j
  let pick : (J → Bool) → J := fun b => if h : ∃ j, b j = true then h.choose else Classical.choice inferInstance
  refine ⟨fun x => s (pick (code x)), (measurable_of_countable (s ∘ pick)).comp hcode, ?_⟩
  intro k
  have hfreq : ∀ᵐ x ∂productLaw (fun _ : ℕ => K k), good k x := by
    rw [ae_all_iff]; intro z
    simpa only [freq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] using iid_average (K k) (fun y => if y = z then (1 : ℝ) else 0)
  filter_upwards [hfreq] with x hx
  have hex : ∃ j, code x j = true := ⟨k, by simp [code, hx]⟩
  have hpick : good (pick (code x)) x := by
    have hh := hex.choose_spec
    simpa only [pick, dif_pos hex, code, decide_eq_true_eq] using hh
  apply (hs _ _).mpr
  ext z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  exact tendsto_nhds_unique (hpick z) (hx z)
/-- The finite-record bridge for a latent state drawn once and a conditionally iid
record is obtained from the product measure. Given the posterior coordinate limits,
the common-record KL limit holds under the actual joint law, including zero priors. -/
theorem iid_moving_support_posterior_limit_of_coordinates
    {J I Z : Type*} [Fintype J] [Fintype I] [Fintype Z] [MeasurableSpace J] [MeasurableSingletonClass J]
    [MeasurableSpace Z] [MeasurableSingletonClass Z] (d q : J → ℝ) (K : J → PMF Z) (r : J → I)
    (hd : (∀ j, 0 ≤ d j) ∧ ∑ j, d j = 1) (hq : (∀ j, 0 < q j) ∧ ∑ j, q j = 1)
    {M : ℝ} (hM : 0 < M) (hdom : ∀ j, d j ≤ M * q j)
    (a b : (J × (ℕ → Z)) → J → ℝ) (t : (J × (ℕ → Z)) → ℝ) :
    let μ : Measure (J × (ℕ → Z)) := ∑ j, ENNReal.ofReal (d j) •
      (productLaw (fun _ : ℕ => K j)).map (fun x => (j, x))
    let W := fun n j (h : Fin n → Z) => ∏ k, pmfRealMass (Output := fun _ : ℕ => Z) (i := 0) (K j) (h k)
    let record := fun n (ω : J × (ℕ → Z)) (k : Fin n) => ω.2 k
    let f := fun n ω => posteriorDefect d q (W n) r (record n ω)
    let g := fun ω => klDivergence (a ω) (b ω) -
      klDivergence (pushforward r (a ω)) (pushforward r (b ω))
    (∀ᵐ ω ∂μ, 0 < t ω ∧
      Tendsto (fun n => channelOutput (W n) d (record n ω) /
        channelOutput (W n) q (record n ω)) atTop (𝓝 (t ω)) ∧
      (∀ j, Tendsto (fun n => posterior (W n) d (record n ω) j) atTop (𝓝 (a ω j))) ∧
      (∀ j, Tendsto (fun n => posterior (W n) q (record n ω) j) atTop (𝓝 (b ω j)))) →
    (∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) ∧
    UniformIntegrable f 1 μ ∧ Integrable g μ ∧
    Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0) ∧
    Tendsto (fun n => ∫ ω, f n ω ∂μ) atTop (𝓝 (∫ ω, g ω ∂μ)) := by classical
  dsimp only
  let μ : Measure (J × (ℕ → Z)) := ∑ j, ENNReal.ofReal (d j) •
    (productLaw (fun _ : ℕ => K j)).map (fun x => (j, x))
  let W := fun n j (h : Fin n → Z) => ∏ k, pmfRealMass (Output := fun _ : ℕ => Z) (i := 0) (K j) (h k)
  let record := fun n (ω : J × (ℕ → Z)) (k : Fin n) => ω.2 k
  have hp j : IsProbabilityMeasure (productLaw (fun _ : ℕ => K j)) := by
    dsimp only [productLaw]
    infer_instance
  have hmj j : ((productLaw (fun _ : ℕ => K j)).map
      (fun x => (j, x))) univ = 1 := by
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, preimage_univ]
    exact measure_univ
  have hμ : IsProbabilityMeasure μ := by
    constructor
    simp only [μ, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      hmj, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hd.1 j), hd.2, ENNReal.ofReal_one]
  letI := hμ
  have hr n : Measurable (record n) := by fun_prop
  have hrow j n :
      (productLaw (fun _ : ℕ => K j)).map (fun x (k : Fin n) => x k) =
        Measure.pi (fun _ : Fin n => (K j).toMeasure) := by
    exact (Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : ℕ => (K j).toMeasure) (f := fun k : Fin n => k.val)
      Fin.val_injective).trans (Measure.infinitePi_eq_pi _)
  have hprefix j n (h : Fin n → Z) :
      (productLaw (fun _ : ℕ => K j)) {x | (fun k : Fin n => x k) = h} =
        ∏ k, K j (h k) := by
    change (productLaw (fun _ : ℕ => K j))
      ((fun x : ℕ → Z => fun k : Fin n => x k) ⁻¹' {h}) = _
    rw [← Measure.map_apply (by fun_prop :
      Measurable (fun x : ℕ → Z => fun k : Fin n => x k)) (measurableSet_singleton h),
      hrow, Measure.pi_singleton]
    simp [PMF.toMeasure_apply_singleton]
  have hW : ∀ n, (∀ j h, 0 ≤ W n j h) ∧ ∀ j, ∑ h, W n j h = 1 := by
    intro n
    constructor
    · intro j h; exact Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg
    · intro j; rw [show (∑ h, W n j h) =
          ∏ k : Fin n, ∑ z, pmfRealMass (Output := fun _ : ℕ => Z) (i := 0) (K j) z from
        (Fintype.prod_sum _).symm]
      simp only [pmfRealMass_sum (Output := fun _ : ℕ => Z) (i := 0), Finset.prod_const_one]
  have hmass n (h : Fin n → Z) : μ.real (record n ⁻¹' {h}) =
      channelOutput (W n) d h := by
    have he : μ (record n ⁻¹' {h}) = ∑ j, ENNReal.ofReal (d j) * ∏ k, K j (h k) := by
      simp only [μ, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
        smul_eq_mul]
      apply Finset.sum_congr rfl; intro j _; rw [Measure.map_apply (by fun_prop) ((measurableSet_singleton h).preimage (hr n))]
      exact congrArg (ENNReal.ofReal (d j) * ·) (hprefix j n h)
    rw [Measure.real, he, ENNReal.toReal_sum (fun j _ => ENNReal.mul_ne_top
      ENNReal.ofReal_ne_top (ENNReal.prod_ne_top (fun _ _ => PMF.apply_ne_top _ _)))]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hd.1 _), ENNReal.toReal_prod,
      channelOutput, W, pmfRealMass]
  intro hpath; exact moving_support_posterior_limit μ record hr d q W r hd hq hW hmass
    hM hdom a b t hpath
private lemma fiber_recovery_identity {J I : Type*} [Fintype J] [Fintype I]
    (p q : J → ℝ) (r : J → I)
    (hp : (∀ j, 0 ≤ p j) ∧ ∑ j, p j = 1)
    (hq : (∀ j, 0 ≤ q j) ∧ ∑ j, q j = 1) (hac : ∀ j, q j = 0 → p j = 0) :
    let e := fun j => q j * (pushforward r p (r j) / pushforward r q (r j))
    klDivergence p e = klDivergence p q - klDivergence (pushforward r p) (pushforward r q) ∧
    (klDivergence p q - klDivergence (pushforward r p) (pushforward r q) = 0 ↔ p = e) := by classical
  let P := pushforward r p
  let Q := pushforward r q
  let e := fun j => q j * (P (r j) / Q (r j))
  have hP := D5.S3.Entropy.Forgetting.CompletionEntropyMinimality.pushforward_is_law p r hp
  have hQ := D5.S3.Entropy.Forgetting.CompletionEntropyMinimality.pushforward_is_law q r hq
  have hsum (v : J → ℝ) (f : I → ℝ) :
      ∑ i, pushforward r v i * f i = ∑ j, v j * f (r j) := by
    simpa +contextual [pushforward, Finset.sum_mul, Finset.sum_filter, ite_mul] using
      (Finset.sum_fiberwise (Finset.univ : Finset J) r (fun j => v j * f (r j)))
  have hle (v : J → ℝ) (hv : ∀ j, 0 ≤ v j) j : v j ≤ pushforward r v (r j) := by
    simpa only [pushforward, if_true] using
      (Finset.single_le_sum (f := fun k => if r k = r j then v k else 0)
        (fun k _ => by split_ifs <;> simp_all only [le_refl]) (Finset.mem_univ j))
  have hQzero i (hi : Q i = 0) : P i = 0 := by
    have hh := channel_output_absolute_continuity p q
      (fun j i => if r j = i then (1 : ℝ) else 0) hq.1 hac
      (fun j i => by split_ifs <;> norm_num) i
    simpa [channelOutput, pushforward, P, Q] using hh (by simpa [channelOutput, Q, pushforward] using hi)
  have heq : klDivergence p e = klDivergence p q - klDivergence P Q := by
    change (∑ j, p j * Real.log (p j / e j)) =
      (∑ j, p j * Real.log (p j / q j)) - ∑ i, P i * Real.log (P i / Q i)
    rw [hsum p (fun i => Real.log (P i / Q i)), ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _
    by_cases hj : p j = 0
    · simp [hj]
    have hpj := lt_of_le_of_ne (hp.1 j) (Ne.symm hj)
    have hqj : q j ≠ 0 := mt (hac j) hj
    have hPj : P (r j) ≠ 0 := (hpj.trans_le (hle p hp.1 j)).ne'
    have hQj : Q (r j) ≠ 0 := mt (hQzero _) hPj
    dsimp only [e]
    rw [Real.log_div hj (mul_ne_zero hqj (div_ne_zero hPj hQj)),
      Real.log_mul hqj (div_ne_zero hPj hQj), Real.log_div hj hqj]
    ring
  have he : (∀ j, 0 ≤ e j) ∧ ∑ j, e j = 1 := by
    refine ⟨fun j => mul_nonneg (hq.1 j) (div_nonneg (hP.1 _) (hQ.1 _)), ?_⟩
    rw [show (∑ j, e j) = ∑ i, Q i * (P i / Q i) from (hsum q (fun i => P i / Q i)).symm]
    convert hP.2 using 1
    apply Finset.sum_congr rfl; intro i _
    change Q i * (P i / Q i) = P i
    by_cases hi : Q i = 0
    · simp [hi, hQzero i hi]
    · field_simp
  have heac j (hj : e j = 0) : p j = 0 := by
    by_contra hn
    have hpj := lt_of_le_of_ne (hp.1 j) (Ne.symm hn)
    have hPj : P (r j) ≠ 0 := (hpj.trans_le (hle p hp.1 j)).ne'
    exact (mul_ne_zero (mt (hac j) hn) (div_ne_zero hPj (mt (hQzero _) hPj))) hj
  exact ⟨heq, heq ▸ D5.S3.Divergence.GibbsEquality.kl_divergence_eq_zero_iff p e hp he heac⟩
private lemma deterministic_output {J S : Type*} [Fintype J] [DecidableEq S]
    (p : J → ℝ) (s : J → S) :
    channelOutput (fun j c => if s j = c then (1 : ℝ) else 0) p = pushforward s p := by
  funext c
  simp only [channelOutput, pushforward, mul_ite, mul_one, mul_zero]
  apply Finset.sum_congr rfl; intro j _
  by_cases hj : s j = c <;> simp [hj]
private lemma class_mean_identity {J I S : Type*} [Fintype J] [Fintype I]
    [Fintype S] [DecidableEq S] (d q : J → ℝ) (r : J → I) (s : J → S)
    (hd : (∀ j, 0 ≤ d j) ∧ ∑ j, d j = 1) (hq : (∀ j, 0 < q j) ∧ ∑ j, q j = 1) :
    let C := fun j c => if s j = c then (1 : ℝ) else 0
    let u := fun j => (r j, s j)
    (∑ c, channelOutput C d c *
      (klDivergence (posterior C d c) (posterior C q c) -
        klDivergence (pushforward r (posterior C d c)) (pushforward r (posterior C q c)))) =
      klDivergence d (fun j => q j * (pushforward u d (u j) / pushforward u q (u j))) := by classical
  let C := fun j c => if s j = c then (1 : ℝ) else 0
  let u := fun j => (r j, s j)
  let V := fun (v : I × S) c => if v.2 = c then (1 : ℝ) else 0
  have hout (p : J → ℝ) : channelOutput V (pushforward u p) = channelOutput C p := by
    rw [deterministic_output, deterministic_output]
    exact D5.S3.Entropy.Forgetting.PushforwardComposition.pushforward_comp p u Prod.snd
  have hcoarse (p : J → ℝ) c i : pushforward r (posterior C p c) i =
      pushforward u p (i,c) / channelOutput C p c := by
    simp only [pushforward, posterior, Finset.sum_div, u, Prod.mk.injEq, C]
    apply Finset.sum_congr rfl; intro j _
    by_cases hj : r j = i <;> by_cases hc : s j = c <;> simp [hj, hc]
  have hpost (p : J → ℝ) c i b : posterior V (pushforward u p) c (i,b) =
      if b = c then pushforward r (posterior C p c) i else 0 := by
    simp only [posterior, hout, V]
    split_ifs with hb
    · subst b
      rw [mul_one, hcoarse]
    · simp
  have hkl c : klDivergence (posterior V (pushforward u d) c)
      (posterior V (pushforward u q) c) =
      klDivergence (pushforward r (posterior C d c)) (pushforward r (posterior C q c)) := by
    simp only [klDivergence, Fintype.sum_prod_type, hpost]
    apply Finset.sum_congr rfl; intro i _
    simp
  have hac j (hj : q j = 0) : d j = 0 := False.elim ((hq.1 j).ne' hj)
  have hc : (∀ j c, 0 ≤ C j c) ∧ ∀ j, ∑ c, C j c = 1 := by
    constructor
    · intro j c; dsimp [C]; split_ifs <;> norm_num
    · intro j; simp [C]
  have hv : (∀ v c, 0 ≤ V v c) ∧ ∀ v, ∑ c, V v c = 1 := by
    constructor
    · intro v c; dsimp [V]; split_ifs <;> norm_num
    · intro v; simp [V]
  have hp := D5.S3.Entropy.Forgetting.CompletionEntropyMinimality.pushforward_is_law d u hd
  have hq' := D5.S3.Entropy.Forgetting.CompletionEntropyMinimality.pushforward_is_law
    q u ⟨fun j => (hq.1 j).le, hq.2⟩
  have hac' v : pushforward u q v = 0 → pushforward u d v = 0 := by
    have hh := channel_output_absolute_continuity d q
      (fun j v => if u j = v then (1 : ℝ) else 0) (fun j => (hq.1 j).le) hac
      (fun j v => by split_ifs <;> norm_num) v
    rwa [deterministic_output, deterministic_output] at hh
  have h1 := classical_dpi_identity_zero_support d q C hd ⟨fun j => (hq.1 j).le, hq.2⟩ hac hc
  have h2 := classical_dpi_identity_zero_support (pushforward u d) (pushforward u q)
    V hp hq' hac' hv
  simp only [hout, hkl] at h2
  have he := (fiber_recovery_identity d q u hd ⟨fun j => (hq.1 j).le, hq.2⟩ hac).1
  dsimp only
  simp only [mul_sub, Finset.sum_sub_distrib]
  linarith
private lemma iid_class_integral {J S Z : Type*} [Fintype J] [Fintype S]
    [MeasurableSpace J] [MeasurableSingletonClass J] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (d : J → ℝ) (K : J → PMF Z) (s : J → S) (hd : ∀ j, 0 ≤ d j) (g : S → ℝ) :
    (∫ ω : J × (ℕ → Z), g (s ω.1) ∂(∑ j, ENNReal.ofReal (d j) •
      (productLaw (fun _ : ℕ => K j)).map (fun x => (j,x)))) =
      ∑ c, pushforward s d c * g c := by classical
  have hp j : IsProbabilityMeasure (productLaw (fun _ : ℕ => K j)) := by
    dsimp only [productLaw]; infer_instance
  have hi j : Integrable (fun ω : J × (ℕ → Z) => g (s ω.1))
      ((productLaw (fun _ : ℕ => K j)).map (fun x => (j,x))) := by
    rw [(measurableEmbedding_prodMk_left j).integrable_map_iff]
    dsimp only [Function.comp_def]; exact integrable_const _
  rw [integral_finsetSum_measure (fun j _ => (hi j).smul_measure ENNReal.ofReal_ne_top)]
  have hm j : (∫ ω : J × (ℕ → Z), g (s ω.1) ∂(ENNReal.ofReal (d j) •
      (productLaw (fun _ : ℕ => K j)).map (fun x => (j,x)))) = d j * g (s j) := by
    rw [integral_smul_measure, ENNReal.toReal_ofReal (hd j),
      (measurableEmbedding_prodMk_left j).integral_map]
    simp
  simp only [hm]
  symm
  simpa +contextual [pushforward, Finset.sum_mul, Finset.sum_filter, ite_mul] using
    (Finset.sum_fiberwise (Finset.univ : Finset J) s (fun j => d j * g (s j)))
/-- In the finite latent iid model the row class is decoded from the record under both
priors, both posteriors converge to the class-conditioned priors, and KL loss converges
almost surely and in L1. The coordinate limits and positive evidence-ratio limit are
conclusions of the actual model, with no convergence hypotheses. -/
theorem iid_moving_support_posterior_limit
    {J I Z S : Type*} [Fintype J] [Nonempty J] [Fintype I] [Fintype Z]
    [Fintype S] [DecidableEq S] [MeasurableSpace J] [MeasurableSingletonClass J]
    [MeasurableSpace Z] [MeasurableSingletonClass Z] [MeasurableSpace S] [MeasurableSingletonClass S]
    (d q : J → ℝ) (K : J → PMF Z) (r : J → I) (s : J → S)
    (hd : (∀ j, 0 ≤ d j) ∧ ∑ j, d j = 1) (hq : (∀ j, 0 < q j) ∧ ∑ j, q j = 1)
    (hs : ∀ j k, s j = s k ↔ K j = K k) :
    let μ := fun p : J → ℝ => ∑ j, ENNReal.ofReal (p j) •
      (productLaw (fun _ : ℕ => K j)).map (fun x => (j, x))
    let C := fun j c => if s j = c then (1 : ℝ) else 0
    let W := fun n j (h : Fin n → Z) => ∏ k, (K j (h k)).toReal
    let f := fun n (ω : J × (ℕ → Z)) => posteriorDefect d q (W n) r (fun k => ω.2 k)
    let a := fun (ω : J × (ℕ → Z)) => posterior C d (s ω.1)
    let b := fun (ω : J × (ℕ → Z)) => posterior C q (s ω.1)
    let g := fun ω => klDivergence (a ω) (b ω) -
      klDivergence (pushforward r (a ω)) (pushforward r (b ω))
    (∃ dec : (ℕ → Z) → S, Measurable dec ∧
      (∀ᵐ ω ∂μ d, dec ω.2 = s ω.1) ∧ (∀ᵐ ω ∂μ q, dec ω.2 = s ω.1)) ∧
    (∀ᵐ ω ∂μ d, 0 < channelOutput C d (s ω.1) ∧
      (∀ j, Tendsto (fun n => posterior (W n) d (fun k => ω.2 k) j) atTop (𝓝 (a ω j))) ∧
      (∀ j, Tendsto (fun n => posterior (W n) q (fun k => ω.2 k) j) atTop (𝓝 (b ω j)))) ∧
    (∀ᵐ ω ∂μ d, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) ∧
    UniformIntegrable f 1 (μ d) ∧ Integrable g (μ d) ∧
    Tendsto (fun n => eLpNorm (f n - g) 1 (μ d)) atTop (𝓝 0) ∧
    Tendsto (fun n => ∫ ω, f n ω ∂μ d) atTop (𝓝 (∫ ω, g ω ∂μ d)) ∧
    (∫ ω, g ω ∂μ d) = ∑ c, channelOutput C d c *
      (klDivergence (posterior C d c) (posterior C q c) -
        klDivergence (pushforward r (posterior C d c)) (pushforward r (posterior C q c))) ∧
    (∫ ω, g ω ∂μ d) = klDivergence d (fun j => q j *
      (pushforward (fun j => (r j,s j)) d (r j,s j) /
        pushforward (fun j => (r j,s j)) q (r j,s j))) ∧
    ∀ c, 0 < channelOutput C d c →
      (klDivergence (posterior C d c) (posterior C q c) -
        klDivergence (pushforward r (posterior C d c)) (pushforward r (posterior C q c)) = 0 ↔
        posterior C d c = fun j => posterior C q c j *
          (pushforward r (posterior C d c) (r j) / pushforward r (posterior C q c) (r j))) := by classical
  dsimp only
  let μ := fun p : J → ℝ => ∑ j, ENNReal.ofReal (p j) •
    (productLaw (fun _ : ℕ => K j)).map (fun x => (j, x))
  let C := fun j c => if s j = c then (1 : ℝ) else 0
  let W := fun n j (h : Fin n → Z) => ∏ k, (K j (h k)).toReal
  let a := fun (ω : J × (ℕ → Z)) => posterior C d (s ω.1)
  let b := fun (ω : J × (ℕ → Z)) => posterior C q (s ω.1)
  let t := fun (ω : J × (ℕ → Z)) => channelOutput C d (s ω.1) / channelOutput C q (s ω.1)
  have hc (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (k : J) (hk : 0 < p k) :
      0 < channelOutput C p (s k) := by
    apply hk.trans_le
    simpa only [C, channelOutput, if_true, mul_one] using
      (Finset.single_le_sum (f := fun j => p j * C j (s k))
        (fun j _ => mul_nonneg (hp j) (by dsimp [C]; split_ifs <;> norm_num))
        (Finset.mem_univ k))
  have hpath : ∀ᵐ ω ∂μ d, 0 < channelOutput C d (s ω.1) ∧ 0 < t ω ∧
      Tendsto (fun n => channelOutput (W n) d (fun k => ω.2 k) /
        channelOutput (W n) q (fun k => ω.2 k)) atTop (𝓝 (t ω)) ∧
      (∀ j, Tendsto (fun n => posterior (W n) d (fun k => ω.2 k) j) atTop (𝓝 (a ω j))) ∧
      (∀ j, Tendsto (fun n => posterior (W n) q (fun k => ω.2 k) j) atTop (𝓝 (b ω j))) := by
    rw [ae_finsetSum_measure_iff]
    intro k _
    by_cases hk : 0 < d k
    · apply Measure.ae_smul_measure
      rw [(measurableEmbedding_prodMk_left k).ae_map_iff]
      filter_upwards [iid_class_ratios K s hs k] with x hx
      have hdc := hc d hd.1 k hk
      have hqc := hc q (fun j => (hq.1 j).le) k (hq.1 k)
      have hdl := class_posterior_limit d s k (fun n j => W n j (fun i => x i))
        hx.1 hx.2 hdc.ne'
      have hql := class_posterior_limit q s k (fun n j => W n j (fun i => x i))
        hx.1 hx.2 hqc.ne'
      refine ⟨hdc, div_pos hdc hqc, ?_, hdl.2, hql.2⟩
      convert hdl.1.div hql.1 hqc.ne' using 1
      ext n
      exact (div_div_div_cancel_right₀ (hx.1 n).ne' _ _).symm
    · have hz : ENNReal.ofReal (d k) = 0 := ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hk)
      simp [hz]
  obtain ⟨dec, hdec, hdecrow⟩ := iid_class_decoder K s hs
  have hdecode (p : J → ℝ) : ∀ᵐ ω ∂μ p, dec ω.2 = s ω.1 := by
    rw [ae_finsetSum_measure_iff]
    intro k _
    apply Measure.ae_smul_measure
    rw [(measurableEmbedding_prodMk_left k).ae_map_iff]
    exact hdecrow k
  let M := 1 + ∑ j, d j / q j
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one
    (le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => div_nonneg (hd.1 j) (hq.1 j).le))
  have hdom j : d j ≤ M * q j := by
    rw [← div_le_iff₀ (hq.1 j)]
    exact (Finset.single_le_sum (fun i _ => div_nonneg (hd.1 i) (hq.1 i).le)
      (Finset.mem_univ j)).trans (le_add_of_nonneg_left zero_le_one)
  have h := iid_moving_support_posterior_limit_of_coordinates d q K r hd hq hM hdom a b t
    (hpath.mono fun _ h => h.2)
  have havg := iid_class_integral d K s hd.1 (fun c => klDivergence (posterior C d c) (posterior C q c) -
      klDivergence (pushforward r (posterior C d c)) (pushforward r (posterior C q c)))
  have hsum := class_mean_identity d q r s hd hq
  dsimp only at hsum
  rw [deterministic_output] at hsum
  refine ⟨⟨dec, hdec, hdecode d, hdecode q⟩,
    hpath.mono (fun _ h => ⟨h.1, h.2.2.2⟩), h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    h.2.2.2.2, ?_, havg.trans hsum, ?_⟩
  · simpa only [deterministic_output] using havg
  · intro c hdc
    have hC j c : 0 ≤ C j c := by dsimp [C]; split_ifs <;> norm_num
    have hqc : 0 < channelOutput C q c := by
      have hn : 0 ≤ channelOutput C q c := Finset.sum_nonneg fun j _ => mul_nonneg (hq.1 j).le (hC j c)
      apply lt_of_le_of_ne hn
      intro hz; exact hdc.ne' (channel_output_absolute_continuity d q C (fun j => (hq.1 j).le)
        (fun j hj => False.elim ((hq.1 j).ne' hj)) hC c hz.symm)
    have hac j (hj : posterior C q c j = 0) : posterior C d c j = 0 := by
      have hz : C j c = 0 := by
        simpa only [posterior, div_eq_zero_iff, mul_eq_zero, (hq.1 j).ne', hqc.ne',
          false_or, or_false] using hj
      simp [posterior, hz]
    exact (fiber_recovery_identity _ _ r (posterior_mass C hC c d hd.1 hdc)
      (posterior_mass C hC c q (fun j => (hq.1 j).le) hqc) hac).2
end D5.S3.DivergenceSupport.MovingSupportKLTransport
