/- GID: D5/S3/Analytic/Probability/UniformCDFConvergence
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/UniformCDFConvergence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Continuous limiting distribution functions upgrade pointwise convergence to uniform. -/

/- admission_basis: escape-witness
   Direct frozen dependencies: none.
   Module escape_witness: monotone_cdf_pointwise_to_uniform
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15743
   Template gap: No source-specific function-sequence arena or uniform-epsilon readout is supplied.
   Four-slot evidence missing: source-specific arenas and observation/readout maps,
     exact reconstruction and realization bridges, E1–E8, variation and sensitivity.
   DTR reading: 2 DTR-Unregistered findings (Observe); no Reg mirror is supplied.
   Gaussian conventions use gaussianPDFReal 0 1 and cdf (gaussianReal 0 1).
   They equal (sqrt (2*pi))^-1 * exp (-t^2/2) and its Iic integral.
   monotone_pointwise_uniform_on_compact: proof_shape: content; escape_witness: monotone_pointwise_uniform_on_compact;
     consumers: monotone_cdf_pointwise_to_uniform.
   monotone_cdf_pointwise_to_uniform: proof_shape: content; escape_witness: monotone_cdf_pointwise_to_uniform;
     consumers: weak_limit_uniform_cdf.
   continuous_cdf_of_noAtoms: proof_shape: bind-only; escape_witness: none;
     consumers: weak_limit_uniform_cdf.
   weak_limit_pointwise_cdf: proof_shape: bind-only; escape_witness: none;
     consumers: weak_limit_uniform_cdf.
   weak_limit_uniform_cdf: proof_shape: content; escape_witness: monotone_cdf_pointwise_to_uniform;
     consumers: charFun_limit_uniform_gaussian_cdf.
   gaussian_charFun_standard: proof_shape: bind-only; escape_witness: none;
     consumers: charFun_limit_uniform_gaussian_cdf.
   charFun_limit_uniform_gaussian_cdf: proof_shape: content; escape_witness: monotone_cdf_pointwise_to_uniform;
     consumers: bernoulli_array_uniform_gaussian_cdf.
-/

import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.LevyConvergence

noncomputable section
open Filter Real Topology Set MeasureTheory ProbabilityTheory
namespace D5.S3.Analytic.Probability.UniformCDFConvergence

private lemma monotone_pointwise_uniform_on_compact {F : ℕ → ℝ → ℝ} {G : ℝ → ℝ}
    (hF : ∀ n, Monotone (F n)) (hGm : Monotone G) (hGc : Continuous G)
    (hpoint : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (G x)))
    {K : Set ℝ} (hK : IsCompact K) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ x ∈ K, |F n x - G x| < ε := by
  intro ε hε
  have hε4 : 0 < ε/4 := by positivity
  have hlocal : ∀ x : ℝ, ∃ a b : ℝ, a < x ∧ x < b ∧ G b - G a < ε/2 := by
    intro x
    obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp hGc.continuousAt (ε/4) hε4
    refine ⟨x-δ/2,x+δ/2,by linarith,by linarith,?_⟩
    have ha : dist (x-δ/2) x < δ := by rw [Real.dist_eq]; rw [abs_of_nonpos (by linarith)]; linarith
    have hb : dist (x+δ/2) x < δ := by rw [Real.dist_eq]; rw [abs_of_nonneg (by linarith)]; linarith
    have hca := hclose ha
    have hcb := hclose hb
    rw [Real.dist_eq, abs_lt] at hca hcb
    linarith
  choose a b hab using hlocal
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover (fun x => Ioo (a x) (b x))
    (fun _ => isOpen_Ioo) (by intro x hx; simp only [mem_iUnion]; exact ⟨x,(hab x).1,(hab x).2.1⟩)
  have hev : ∀ x ∈ s, ∀ᶠ n in atTop,
      |F n (a x) - G (a x)| < ε/4 ∧ |F n (b x)-G (b x)| < ε/4 := by
    intro x hx
    have ha := Metric.tendsto_nhds.1 (hpoint (a x)) (ε/4) hε4
    have hb := Metric.tendsto_nhds.1 (hpoint (b x)) (ε/4) hε4
    simpa [Real.dist_eq] using ha.and hb
  have he := (Filter.eventually_all_finset s).2 hev
  filter_upwards [he] with n hn
  intro x hx
  obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.1 (hs hx)
  have hlo := hF n hxy.1.le
  have hhi := hF n hxy.2.le
  have hglo := hGm hxy.1.le
  have hghi := hGm hxy.2.le
  have hc := (hab y).2.2
  have hna := (abs_lt.1 (hn y hy).1)
  have hnb := (abs_lt.1 (hn y hy).2)
  apply abs_lt.2
  constructor <;> linarith

lemma monotone_cdf_pointwise_to_uniform {F : ℕ → ℝ → ℝ} {G : ℝ → ℝ}
    (hF : ∀ n, Monotone (F n)) (hGm : Monotone G) (hGc : Continuous G)
    (hFn : ∀ n x, 0 ≤ F n x) (hF1 : ∀ n x, F n x ≤ 1)
    (hGn : ∀ x, 0 ≤ G x) (hG1 : ∀ x, G x ≤ 1)
    (hbot : Tendsto G atBot (𝓝 0)) (htop : Tendsto G atTop (𝓝 1))
    (hpoint : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (G x))) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ x : ℝ, |F n x - G x| < ε := by
  intro ε hε
  have hε2 : 0 < ε/2 := by positivity
  obtain ⟨a,ha⟩ := ((tendsto_order.1 hbot).2 (ε/2) hε2).exists
  obtain ⟨b,hb⟩ := ((tendsto_order.1 htop).1 (1-ε/2) (by linarith)).exists
  have hpa : ∀ᶠ n in atTop, F n a < ε := (tendsto_order.1 (hpoint a)).2 ε (by linarith)
  have hpb : ∀ᶠ n in atTop, 1-ε < F n b := (tendsto_order.1 (hpoint b)).1 (1-ε) (by linarith)
  have hmid := monotone_pointwise_uniform_on_compact hF hGm hGc hpoint (isCompact_Icc (a := a) (b := b)) ε hε
  filter_upwards [hpa,hpb,hmid] with n hna hnb hnm
  intro x
  by_cases hxa : x < a
  · apply abs_lt.2
    have hf := hF n hxa.le
    have hg := hGm hxa.le
    constructor <;> linarith [hFn n x,hGn x]
  · by_cases hbx : b < x
    · apply abs_lt.2
      have hf := hF n hbx.le
      have hg := hGm hbx.le
      constructor <;> linarith [hF1 n x,hG1 x]
    · exact hnm x ⟨le_of_not_gt hxa,le_of_not_gt hbx⟩

private lemma continuous_cdf_of_noAtoms (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] : Continuous (cdf μ : ℝ → ℝ) := by
  apply continuous_iff_continuousAt.2
  intro t
  have hc : ContinuousOn (fun b => ∫ x in Iic b, (1:ℝ) ∂μ) (Iic (t+1)) :=
    (integrable_const (1:ℝ)).integrableOn.continuousOn_Iic_primitive_Iic
  have hca := (hc t (by simp)).continuousAt (Iic_mem_nhds (by linarith : t < t+1))
  have he : (fun b => ∫ x in Iic b, (1:ℝ) ∂μ) = (cdf μ : ℝ → ℝ) := by
    funext b
    simp [integral_const,cdf_eq_real,measureReal_def]
  rw [he] at hca
  exact hca

private lemma weak_limit_pointwise_cdf {μn : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    [NullSingletonClass (μ : Measure ℝ)] (hweak : Tendsto μn atTop (𝓝 μ)) (t : ℝ) :
    Tendsto (fun n => cdf (μn n : Measure ℝ) t) atTop (𝓝 (cdf (μ : Measure ℝ) t)) := by
  have hf : (μ : Measure ℝ) (frontier (Iic t)) = 0 := by rw [frontier_Iic]; simp
  have hm := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hweak hf
  have hr := (ENNReal.tendsto_toReal (measure_ne_top (μ : Measure ℝ) (Iic t))).comp hm
  simpa only [cdf_eq_real,measureReal_def,Function.comp_def] using hr

private lemma weak_limit_uniform_cdf {μn : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    [NullSingletonClass (μ : Measure ℝ)] (hweak : Tendsto μn atTop (𝓝 μ)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ t : ℝ,
      |cdf (μn n : Measure ℝ) t - cdf (μ : Measure ℝ) t| < ε := by
  exact monotone_cdf_pointwise_to_uniform
    (fun n => monotone_cdf _) (monotone_cdf _) (continuous_cdf_of_noAtoms _)
    (fun n t => cdf_nonneg _ _) (fun n t => cdf_le_one _ _)
    (cdf_nonneg _) (cdf_le_one _) (tendsto_cdf_atBot _) (tendsto_cdf_atTop _)
    (weak_limit_pointwise_cdf hweak)

private lemma gaussian_charFun_standard (u : ℝ) :
    charFun (gaussianReal 0 1) u = (Real.exp (-u^2/2):ℂ) := by
  rw [charFun_gaussianReal,Complex.ofReal_exp]
  congr 1
  push_cast
  ring

lemma charFun_limit_uniform_gaussian_cdf {μn : ℕ → ProbabilityMeasure ℝ}
    (hcf : ∀ u : ℝ, Tendsto (fun n => charFun (μn n : Measure ℝ) u) atTop
      (𝓝 (Real.exp (-u^2/2):ℂ))) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ t : ℝ,
      |cdf (μn n : Measure ℝ) t - cdf (gaussianReal 0 1) t| < ε := by
  let μ : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1,inferInstance⟩
  have hweak : Tendsto μn atTop (𝓝 μ) :=
    ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 (by
      intro u
      change Tendsto (fun n => charFun (μn n : Measure ℝ) u) atTop
        (𝓝 (charFun (gaussianReal 0 1) u))
      rw [gaussian_charFun_standard]
      exact hcf u)
  let : NullSingletonClass (μ : Measure ℝ) := nullSingletonClass_gaussianReal (by norm_num)
  have h := weak_limit_uniform_cdf hweak
  change ∀ ε > 0, ∀ᶠ n in atTop, ∀ t : ℝ,
    |cdf (μn n : Measure ℝ) t - cdf (gaussianReal 0 1) t| < ε at h
  exact h


end D5.S3.Analytic.Probability.UniformCDFConvergence
