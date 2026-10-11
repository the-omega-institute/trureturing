/- GID: D5/S3/DivergenceSupport/MovingSupportKLTransport
   generality: G
   mirror-B: D5/B/S3/DivergenceSupport/MovingSupportKLTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Common-record likelihood ratios transport moving-support posterior KL losses to uniform integrability and L1 convergence. -/

import D5.S3.DivergenceSupport.Garbling.DeterministicGarbling
import Mathlib.MeasureTheory.Function.UniformIntegrable

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
    (d q : J → ℝ) (W : J → H → ℝ) (r : J → I) (h : H) : ℝ :=
  if 0 < channelOutput W d h then
    klDivergence (posterior W d h) (posterior W q h) -
      klDivergence (pushforward r (posterior W d h))
        (pushforward r (posterior W q h))
  else 0

private lemma pushforward_mass {J I : Type*} [Fintype J] [Fintype I]
    (r : J → I) (p : J → ℝ) (hp : (∀ j, 0 ≤ p j) ∧ ∑ j, p j = 1) :
    (∀ i, 0 ≤ pushforward r p i) ∧ ∑ i, pushforward r p i = 1 := by
  classical
  constructor
  · intro i
    exact Finset.sum_nonneg fun j _ => by
      split_ifs <;> simp_all only [le_refl]
  · simp only [pushforward, Finset.sum_comm (f := fun i j => if r j = i then p j else 0)]
    simpa using hp.2

private lemma posterior_defect_bounds {J I H : Type*} [Fintype J] [Fintype I]
    (d q : J → ℝ) (W : J → H → ℝ) (r : J → I)
    (hd : (∀ j, 0 ≤ d j) ∧ ∑ j, d j = 1)
    (hq : ∀ j, 0 < q j) (hW : ∀ j h, 0 ≤ W j h)
    {M : ℝ} (hM : 0 < M) (hdom : ∀ j, d j ≤ M * q j)
    (h : H) (hD : 0 < channelOutput W d h) :
    0 < channelOutput W q h ∧ 0 ≤ posteriorDefect d q W r h ∧
      posteriorDefect d q W r h ≤
        Real.log (M / (channelOutput W d h / channelOutput W q h)) := by
  classical
  have hQnn : 0 ≤ channelOutput W q h :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hq j).le (hW j h)
  have hQ : 0 < channelOutput W q h := by
    refine lt_of_le_of_ne hQnn ?_
    intro he
    have := channel_output_absolute_continuity d q W (fun j => (hq j).le)
      (fun j hj => False.elim ((hq j).ne' hj)) hW h he.symm
    linarith
  have hpost (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
      (hP : 0 < channelOutput W p h) :
      (∀ j, 0 ≤ posterior W p h j) ∧ ∑ j, posterior W p h j = 1 := by
    refine ⟨fun j => div_nonneg (mul_nonneg (hp j) (hW j h)) hP.le, ?_⟩
    simpa only [posterior, ← Finset.sum_div, channelOutput] using div_self hP.ne'
  have hpd := hpost d hd.1 hD
  have hpq := hpost q (fun j => (hq j).le) hQ
  have hac : ∀ j, posterior W q h j = 0 → posterior W d h j = 0 := by
    intro j hj
    have hz : W j h = 0 := by
      simpa only [posterior, div_eq_zero_iff, mul_eq_zero, (hq j).ne', hQ.ne',
        false_or, or_false] using hj
    simp [posterior, hz]
  have hpushac : ∀ i, pushforward r (posterior W q h) i = 0 →
      pushforward r (posterior W d h) i = 0 := by
    intro i hi
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      show 0 ≤ (if r j = i then posterior W q h j else 0) from
        by split_ifs <;> simp_all only [le_refl])).mp hi
    apply Finset.sum_eq_zero
    intro j hj
    split_ifs with he
    · exact hac j (by simpa [he] using hz j hj)
    · rfl
  have hcoarse := kl_divergence_nonneg _ _ (pushforward_mass r _ hpd)
    (pushforward_mass r _ hpq) hpushac
  have hkl : klDivergence (posterior W d h) (posterior W q h) ≤
      Real.log (M / (channelOutput W d h / channelOutput W q h)) := by
    calc
      _ ≤ ∑ j, posterior W d h j *
          Real.log (M / (channelOutput W d h / channelOutput W q h)) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : posterior W d h j = 0
        · simp [hj]
        have hdp : 0 < posterior W d h j := lt_of_le_of_ne (hpd.1 j) (Ne.symm hj)
        have hqp : 0 < posterior W q h j :=
          lt_of_le_of_ne (hpq.1 j) (Ne.symm (mt (hac j) hj))
        apply mul_le_mul_of_nonneg_left _ hdp.le
        apply Real.log_le_log (div_pos hdp hqp)
        rw [div_le_iff₀ hqp]
        dsimp only [posterior]
        calc
          _ ≤ (M * q j * W j h) / channelOutput W d h :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hdom j) (hW j h)) hD.le
          _ = _ := by field_simp [hD.ne', hQ.ne']
      _ = _ := by rw [← Finset.sum_mul, hpd.2, one_mul]
  rw [posteriorDefect, if_pos hD]
  exact ⟨hQ, deterministic_forgetting_kl_loss_nonnegative _ _ r hpd hpq hac,
    (sub_le_self _ hcoarse).trans hkl⟩

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
        _ ≤ ((R + 1) * Real.exp (u - R)) * Real.exp (-u) :=
          mul_le_mul_of_nonneg_right hscalar (Real.exp_pos _).le
        _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2 <;> ring
    _ = _ := by ring

private lemma finite_record_integral {Ω H : Type*} [MeasurableSpace Ω]
    [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]
    (μ : Measure Ω) [IsFiniteMeasure μ] (record : Ω → H) (hr : Measurable record)
    (D : H → ℝ) (hmass : ∀ h, μ.real (record ⁻¹' {h}) = D h) (f : H → ℝ) :
    ∫ ω, f (record ω) ∂μ = ∑ h, D h * f h := by
  rw [← integral_map hr.aemeasurable (by exact .of_discrete),
    integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro h _
  rw [map_measureReal_apply hr (measurableSet_singleton h), hmass, smul_eq_mul]

private lemma finite_record_tail {Ω H : Type*} [MeasurableSpace Ω]
    [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]
    (μ : Measure Ω) [IsFiniteMeasure μ] (record : Ω → H) (hr : Measurable record)
    (D Q f : H → ℝ) (hmass : ∀ h, μ.real (record ⁻¹' {h}) = D h)
    (hD : ∀ h, 0 ≤ D h) (hQ : ∀ h, 0 ≤ Q h) (hQsum : ∑ h, Q h = 1)
    (hac : ∀ h, 0 < D h → 0 < Q h) {M : ℝ} (hM : 0 < M)
    (hf : ∀ h, 0 < D h → f h ≤ Real.log (M / (D h / Q h)))
    {R : ℝ} (hR : 0 ≤ R) :
    ∫ ω, ({ω | R ≤ f (record ω)}.indicator (fun ω => f (record ω))) ω ∂μ ≤
      M * (R + 1) * Real.exp (-R) := by
  classical
  rw [show (fun ω => ({ω | R ≤ f (record ω)}.indicator
      (fun ω => f (record ω))) ω) =
      (fun ω => (if R ≤ f (record ω) then f (record ω) else 0)) from rfl,
    finite_record_integral μ record hr D hmass (fun h => if R ≤ f h then f h else 0)]
  calc
    _ ≤ ∑ h, Q h * (M * (R + 1) * Real.exp (-R)) := by
      apply Finset.sum_le_sum
      intro h _
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
      Real.log (M / (D (record ω) / Q (record ω))) else 0} ≤ M * Real.exp (-v) := by
  classical
  let U : H → ℝ := fun h => if 0 < D h then Real.log (M / (D h / Q h)) else 0
  have hm : Measurable (fun ω => U (record ω)) := (measurable_of_countable U).comp hr
  change μ.real {ω | v < U (record ω)} ≤ _
  rw [← integral_indicator_one (measurableSet_lt measurable_const hm)]
  change (∫ ω, (if v < U (record ω) then (1 : ℝ) else 0) ∂μ) ≤ _
  rw [finite_record_integral μ record hr D hmass (fun h => if v < U h then 1 else 0)]
  calc
    _ ≤ ∑ h, Q h * (M * Real.exp (-v)) := by
      apply Finset.sum_le_sum
      intro h _
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
        have ht : D h < (Q h * M) / Real.exp v :=
          (lt_div_iff₀ (Real.exp_pos v)).mpr (by nlinarith)
        simpa only [Real.exp_neg, div_eq_mul_inv, mul_assoc] using ht.le
      · rw [if_neg hu, mul_zero]
        exact mul_nonneg (hQ h) (mul_nonneg hM.le (Real.exp_pos _).le)
    _ = _ := by rw [← Finset.sum_mul, hQsum, one_mul]

/-- A single actual law realizes all finite records. A fixed prior density bound gives
a uniform exponential tail bound for the moving-support KL defects. Consequently
every almost-sure limit is an L1 limit and its expectation is the limit of expectations.
The finite-record mass identity is explicit; no independence of the mixed records is assumed. -/
theorem posterior_defect_l1_of_ae_tendsto
    {J I Ω : Type*} {H : ℕ → Type*} [Fintype J] [Fintype I]
    [MeasurableSpace Ω] [∀ n, Fintype (H n)]
    [∀ n, MeasurableSpace (H n)] [∀ n, MeasurableSingletonClass (H n)]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (record : (n : ℕ) → Ω → H n) (hr : ∀ n, Measurable (record n))
    (d q : J → ℝ) (W : (n : ℕ) → J → H n → ℝ) (r : J → I)
    (hd : (∀ j, 0 ≤ d j) ∧ ∑ j, d j = 1)
    (hq : (∀ j, 0 < q j) ∧ ∑ j, q j = 1)
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
    Tendsto (fun n => ∫ ω, f n ω ∂μ) atTop (𝓝 (∫ ω, g ω ∂μ)) := by
  classical
  dsimp only
  let f := fun n ω => posteriorDefect d q (W n) r (record n ω)
  have hb n h (hh : 0 < channelOutput (W n) d h) :=
    posterior_defect_bounds d q (W n) r hd hq.1 (hW n).1 hM hdom h hh
  have hnonneg n ω : 0 ≤ f n ω := by
    by_cases hh : 0 < channelOutput (W n) d (record n ω)
    · exact (hb n _ hh).2.1
    · simp [f, posteriorDefect, hh]
  have hint n : Integrable (f n) μ :=
    (Integrable.of_finite (μ := μ.map (record n))
      (f := posteriorDefect d q (W n) r)).comp_measurable (hr n)
  have hfmeas n : Measurable (f n) :=
    (measurable_of_countable (posteriorDefect d q (W n) r)).comp (hr n)
  have hQnn n h : 0 ≤ channelOutput (W n) q h :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hq.1 j).le ((hW n).1 j h)
  have hQsum n : ∑ h, channelOutput (W n) q h = 1 := by
    simp only [channelOutput, Finset.sum_comm (f := fun h j => q j * W n j h),
      ← Finset.mul_sum, (hW n).2, mul_one, hq.2]
  have htail (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
      (∫ ω, ({ω | R ≤ f n ω}.indicator (f n)) ω ∂μ) ≤
        M * (R + 1) * Real.exp (-R) := by
    apply finite_record_tail μ (record n) (hr n)
      (channelOutput (W n) d) (channelOutput (W n) q)
      (posteriorDefect d q (W n) r) (hmass n)
    · intro h
      exact Finset.sum_nonneg fun j _ => mul_nonneg (hd.1 j) ((hW n).1 j h)
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
  intro v hv n
  exact finite_record_log_tail μ (record n) (hr n) _ _ (hmass n)
    (hQnn n) (hQsum n) (fun h hh => (hb n h hh).1) hM hv

#print axioms posterior_defect_l1_of_ae_tendsto

end D5.S3.DivergenceSupport.MovingSupportKLTransport
