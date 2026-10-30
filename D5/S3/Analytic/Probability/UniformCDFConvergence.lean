/- GID: D5/S3/Analytic/Probability/UniformCDFConvergence
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/UniformCDFConvergence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Continuous limiting distribution functions upgrade pointwise convergence to uniform. -/

/- admission_basis: escape-witness
   Direct frozen dependencies (declaration GID and declaration statement_id):
   F0: D5/S3/Zeros/Endpoints/BernoulliBridgeVariance.bernoulli_bridge_variance sha256:acf3515171050627eccee903208eb3f1d603d5d3ff4cc74a94c0c95259871d6f
   F1: D5/S3/Zeros/Endpoints/BernoulliBridgeVariance.bernoulli_bridge_variance_le_quarter sha256:d26843918e966727ef778f8c78682791d54fdc06c6a8b7c77e5a9601dd05c43e
   Module escape_witness: monotone_cdf_pointwise_to_uniform
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15743
   Template gap: No source-specific function-sequence arena or uniform-epsilon readout is supplied.
   Four-slot evidence missing: source-specific arenas and observation/readout maps,
     exact reconstruction and realization bridges, E1–E8, variation and sensitivity.
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
   bernoulli_third_moment_bound: proof_shape: bind-only; escape_witness: none;
     consumers: centered_bernoulli_single_gaussian_error.
   centeredBernoulli: proof_shape: bind-only; escape_witness: none;
     consumers: rowFourierCutoff, measurable_rowFourierCutoff, cutoff_bernoulli_gaussian_envelope, rowFourierCutoff_tendsto, centered_rowPhi, scaled_lattice_fourier_inversion, cutoff_lattice_fourier_inversion, standardizedRow_charFun, bernoulli_array_uniform_gaussian_cdf, centeredBernoulli_norm_le, centered_bernoulli_product_error_of_single, centered_bernoulli_product_gaussian_error_of_single, centered_bernoulli_single_gaussian_error, centered_bernoulli_charFun_tendsto, centeredBernoulli_eq_phase, centered_bernoulli_gaussian_envelope, centered_bernoulli_product_envelope, normalized_bernoulli_product_envelope.
   bernoulli_variance_bounds: proof_shape: bind-only; escape_witness: none;
     frozen_dependencies: F0, F1.
     consumers: centered_bernoulli_product_error_of_single, centered_bernoulli_single_gaussian_error.
   centeredBernoulli_norm_le: proof_shape: bind-only; escape_witness: none;
     consumers: centered_bernoulli_product_error_of_single.
   gaussian_factor_norm_le: proof_shape: bind-only; escape_witness: none;
     consumers: centered_bernoulli_product_error_of_single.
   product_norm_le_one: proof_shape: bind-only; escape_witness: none;
     consumers: product_difference_norm.
   product_difference_norm: proof_shape: bind-only; escape_witness: none;
     consumers: centered_bernoulli_product_error_of_single.
   centered_bernoulli_product_error_of_single: proof_shape: bind-only; escape_witness: none;
     frozen_dependencies: F0, F1.
     consumers: centered_bernoulli_product_gaussian_error_of_single.
   centered_bernoulli_product_gaussian_error_of_single: proof_shape: bind-only; escape_witness: none;
     frozen_dependencies: F0, F1.
     consumers: centered_bernoulli_product_gaussian_error.
   L4_Exp2: proof_shape: bind-only; escape_witness: none;
     consumers: centered_bernoulli_single_gaussian_error.
   L4_Taylor3: proof_shape: bind-only; escape_witness: none;
     consumers: centered_bernoulli_single_gaussian_error.
   centered_bernoulli_single_gaussian_error: proof_shape: bind-only; escape_witness: none;
     frozen_dependencies: F0, F1.
     consumers: centered_bernoulli_product_gaussian_error, centered_bernoulli_charFun_tendsto.
   centered_bernoulli_product_gaussian_error: proof_shape: bind-only; escape_witness: none;
     frozen_dependencies: F0, F1.
     consumers: centered_bernoulli_charFun_tendsto.
   centered_bernoulli_charFun_tendsto: proof_shape: bind-only; escape_witness: none;
     frozen_dependencies: F0, F1.
     consumers: rowFourierCutoff_tendsto, bernoulli_array_uniform_gaussian_cdf.
   centeredBernoulli_eq_phase: proof_shape: bind-only; escape_witness: none;
     consumers: centered_rowPhi, centered_bernoulli_gaussian_envelope.
   bernoulli_char_norm_sq: proof_shape: bind-only; escape_witness: none;
     consumers: centered_bernoulli_gaussian_envelope.
   centered_bernoulli_gaussian_envelope: proof_shape: bind-only; escape_witness: none;
     consumers: centered_bernoulli_product_envelope.
   centered_bernoulli_product_envelope: proof_shape: bind-only; escape_witness: none;
     consumers: normalized_bernoulli_product_envelope.
   normalized_bernoulli_product_envelope: proof_shape: bind-only; escape_witness: none;
     consumers: cutoff_bernoulli_gaussian_envelope.
   bernoulliWeight: proof_shape: bind-only; escape_witness: none;
     consumers: rowMass, rowPhi_expansion, finite_lattice_fourier_inversion, bernoulli_event_mass, bernoulli_pgf_expansion, bernoulli_coefficient_law, factorization_integer_mass, bernoulli_real_event, factorization_finite_cdf, bernoulli_atom.
   bernoulliSpace: proof_shape: bind-only; escape_witness: none;
     consumers: bernoulli_event_mass, bernoulli_coefficient_law, standardizedRow, standardizedRow_charFun, factorization_integer_mass, bernoulli_real_event, factorization_finite_cdf, factorization_standardized_cdf, bernoulliSpaceProbability, bernoulli_atom.
   bernoulliSpaceProbability: proof_shape: bind-only; escape_witness: none;
     consumers: bernoulli_event_mass, bernoulli_real_event.
   bernoulli_atom: proof_shape: bind-only; escape_witness: none;
     consumers: bernoulli_event_mass, bernoulli_real_event.
-/

import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.LevyConvergence
import D5.S3.Zeros.Endpoints.BernoulliBridgeVariance

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

lemma gaussian_charFun_standard (u : ℝ) :
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



private lemma bernoulli_third_moment_bound (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p*|1-p|^3+(1-p)*|p|^3 ≤ p*(1-p) := by
  rw [abs_of_nonneg (by linarith : 0≤1-p), abs_of_nonneg hp0]
  nlinarith [sq_nonneg (p*(1-p))]
open Finset Filter Real
open scoped BigOperators

def centeredBernoulli (p s : ℝ) : ℂ :=
  (1-p:ℝ)*Complex.exp ((-s*p:ℝ)*Complex.I) +
    (p:ℝ)*Complex.exp ((s*(1-p):ℝ)*Complex.I)

private lemma bernoulli_variance_bounds (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1) :
    0 ≤ (p * (1 - p)) ∧ (p * (1 - p)) ≤ 1/4 := by
  let t : unitInterval := ⟨p, hp0, hp1⟩
  constructor
  · exact mul_nonneg hp0 (by linarith)
  · simpa only [D5.S3.Zeros.Endpoints.BernoulliBridgeVariance.bernoulli_bridge_variance] using
      D5.S3.Zeros.Endpoints.BernoulliBridgeVariance.bernoulli_bridge_variance_le_quarter t

private lemma centeredBernoulli_norm_le (p s : ℝ) (hp0 : 0≤p) (hp1 : p≤1) :
    ‖centeredBernoulli p s‖ ≤ 1 := by
  unfold centeredBernoulli
  calc
    _ ≤ ‖(1-p:ℝ)*Complex.exp ((-s*p:ℝ)*Complex.I)‖ +
      ‖(p:ℝ)*Complex.exp ((s*(1-p):ℝ)*Complex.I)‖ := norm_add_le _ _
    _ = 1 := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_exp_ofReal_mul_I, mul_one, abs_of_nonneg hp0,
        abs_of_nonneg (by linarith : 0≤1-p)]
      ring

lemma gaussian_factor_norm_le (v s : ℝ) (hv : 0≤v) :
    ‖(Real.exp (-s^2*v/2):ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (by have := sq_nonneg s; nlinarith)

private lemma product_norm_le_one {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) : ‖∏ i ∈ s, f i‖ ≤ 1 := by
  rw [norm_prod]
  exact prod_le_one₀ (by intros; positivity) hf

private lemma product_difference_norm {ι : Type*} (s : Finset ι) (f h : ι → ℂ)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (hh : ∀ i ∈ s, ‖h i‖ ≤ 1) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, h i‖ ≤ ∑ i ∈ s, ‖f i-h i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hfi := hf i (by simp)
    have hhi := hh i (by simp)
    have hft : ∀ j ∈ s, ‖f j‖≤1 := by aesop
    have hht : ∀ j ∈ s, ‖h j‖≤1 := by aesop
    rw [prod_insert hi, prod_insert hi, sum_insert hi]
    have he : f i * (∏ j ∈ s, f j) - h i * (∏ j ∈ s, h j) =
      f i*((∏ j ∈ s, f j)-(∏ j ∈ s, h j)) +
        (f i-h i)*(∏ j ∈ s, h j) := by ring
    rw [he]
    calc
      _ ≤ ‖f i*((∏ j ∈ s, f j)-(∏ j ∈ s, h j))‖ +
        ‖(f i-h i)*(∏ j ∈ s, h j)‖ := norm_add_le _ _
      _ ≤ ‖(∏ j ∈ s, f j)-(∏ j ∈ s, h j)‖+‖f i-h i‖ := by
        simp only [norm_mul]
        exact add_le_add
          (mul_le_of_le_one_left (norm_nonneg _) hfi)
          (mul_le_of_le_one_right (norm_nonneg _) (product_norm_le_one s h hht))
      _ ≤ _ := by have := ih hft hht; linarith

private lemma centered_bernoulli_product_error_of_single {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ i, 0≤p i ∧ p i≤1) (s : ℝ)
    (hlocal : ∀ i, ‖centeredBernoulli (p i) s -
      (Real.exp (-s^2*(p i * (1 - p i))/2):ℂ)‖ ≤
      (p i * (1 - p i))*|s|^3/6 + (p i * (1 - p i))^2*s^4/8) :
    ‖(∏ i, centeredBernoulli (p i) s) -
      (Real.exp (-s^2*(∑ i, (p i * (1 - p i)))/2):ℂ)‖ ≤
      (∑ i, (p i * (1 - p i)))*|s|^3/6 +
        (∑ i, (p i * (1 - p i)))*s^4/32 := by
  have he : (Real.exp (-s^2*(∑ i, (p i * (1 - p i)))/2):ℂ) =
      ∏ i, (Real.exp (-s^2*(p i * (1 - p i))/2):ℂ) := by
    rw [← Complex.ofReal_prod, ← Real.exp_sum]
    congr 2
    simp only [sum_div, mul_sum]
  rw [he]
  calc
    _ ≤ ∑ i, ‖centeredBernoulli (p i) s -
        (Real.exp (-s^2*(p i * (1 - p i))/2):ℂ)‖ :=
      product_difference_norm univ _ _
        (fun i _ => centeredBernoulli_norm_le _ _ (hp i).1 (hp i).2)
        (fun i _ => gaussian_factor_norm_le _ _ (bernoulli_variance_bounds _ (hp i).1 (hp i).2).1)
    _ ≤ ∑ i, ((p i * (1 - p i))*|s|^3/6 + (p i * (1 - p i))*s^4/32) := by
      apply sum_le_sum
      intro i hi
      have hb := bernoulli_variance_bounds (p i) (hp i).1 (hp i).2
      have hs : 0 ≤ s^4 := by positivity
      have hsq : (p i * (1 - p i))^2 ≤ (p i * (1 - p i))/4 := by nlinarith
      have hterm := mul_le_mul_of_nonneg_right hsq hs
      linarith [hlocal i]
    _ = _ := by simp only [sum_add_distrib, sum_div, sum_mul]

private lemma centered_bernoulli_product_gaussian_error_of_single {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ i, 0≤p i ∧ p i≤1) (u : ℝ)
    (hV : 0 < ∑ i, (p i * (1 - p i)))
    (hlocal : ∀ i, ‖centeredBernoulli (p i) (u/√(∑ j, (p j * (1 - p j)))) -
      (Real.exp (-(u/√(∑ j, (p j * (1 - p j))))^2*(p i * (1 - p i))/2):ℂ)‖ ≤
      (p i * (1 - p i))*|u/√(∑ j, (p j * (1 - p j)))|^3/6 +
        (p i * (1 - p i))^2*(u/√(∑ j, (p j * (1 - p j))))^4/8) :
    ‖(∏ i, centeredBernoulli (p i) (u/√(∑ j, (p j * (1 - p j))))) -
      (Real.exp (-u^2/2):ℂ)‖ ≤
      |u|^3/(6*√(∑ j, (p j * (1 - p j)))) +
        u^4/(32*(∑ j, (p j * (1 - p j)))) := by
  let V := ∑ i, (p i * (1 - p i))
  have hVp : 0<V := hV
  have hs : 0<√V := Real.sqrt_pos.2 hVp
  have hsq : (√V)^2=V := Real.sq_sqrt hVp.le
  have he : -(u/√V)^2*V/2 = -u^2/2 := by field_simp; nlinarith [hsq]
  have hb := centered_bernoulli_product_error_of_single p hp (u/√V) hlocal
  change ‖(∏ i, centeredBernoulli (p i) (u/√V)) - (Real.exp (-u^2/2):ℂ)‖ ≤ _
  change ‖(∏ i, centeredBernoulli (p i) (u/√V)) -
    (Real.exp (-(u/√V)^2*V/2):ℂ)‖ ≤ V*|u/√V|^3/6+V*(u/√V)^4/32 at hb
  rw [he] at hb
  convert hb using 1
  change |u|^3/(6*√V)+u^4/(32*V) = V*|u/√V|^3/6+V*(u/√V)^4/32
  rw [abs_div, abs_of_pos hs]
  generalize √V = R at hs hsq ⊢
  rw [← hsq]
  field_simp
open Set Filter Real MeasureTheory
open scoped BigOperators Interval

private lemma L4_Exp2 (x : ℝ) (hx : 0 ≤ x) : |Real.exp (-x) - (1-x)| ≤ x^2/2 := by
  rcases le_or_gt x 1 with hx1 | hx1
  · have habs : |-x| ≤ 1 := by rw [abs_of_nonpos (by linarith)]; linarith
    have h := Real.exp_bound (x := -x) habs (n := 4) (by norm_num)
    have hsum : (∑ m ∈ Finset.range 4, (-x)^m / m.factorial) =
        1 - x + x^2/2 - x^3/6 := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
      ring
    rw [hsum] at h
    have hrem : |Real.exp (-x) - (1 - x + x^2/2 - x^3/6)| ≤
        x^4 * (5 / (24*4)) := by
      convert h using 1 <;> norm_num [abs_of_nonneg hx]
    have hupper : Real.exp (-x) - (1-x) ≤ x^2/2 := by
      have hpoly : Real.exp (-x) - (1-x) =
          (Real.exp (-x) - (1 - x + x^2/2 - x^3/6)) + (x^2/2 - x^3/6) := by ring
      rw [hpoly]
      have hrem' := le_trans (le_abs_self _) hrem
      have hpow : x^4 ≤ x^3 := by
        calc
          x^4 = x^3 * x := by ring
          _ ≤ x^3 * 1 := mul_le_mul_of_nonneg_left hx1 (by positivity)
          _ = x^3 := by ring
      nlinarith [hpow]
    have hnonneg : 0 ≤ Real.exp (-x) - (1-x) := by
      linarith [Real.one_sub_le_exp_neg x]
    rw [abs_of_nonneg hnonneg]
    exact hupper
  · have hexpmono : Real.exp (-x) ≤ Real.exp (-1) := by
      apply Real.exp_le_exp.mpr
      linarith
    have he2 : (2:ℝ) ≤ Real.exp 1 := by
      nlinarith [Real.add_one_le_exp 1]
    have heinv : Real.exp (-1) ≤ (1/2:ℝ) := by
      rw [Real.exp_neg]
      simpa [one_div] using (one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) he2)
    have hnonneg : 0 ≤ Real.exp (-x) - (1-x) := by
      linarith [Real.one_sub_le_exp_neg x]
    have hupper : Real.exp (-x) - (1-x) ≤ x^2/2 := by
      have hq : (1-x) + x^2/2 = 1/2 + (x-1)^2/2 := by ring
      calc
        Real.exp (-x) - (1-x) ≤ (1/2:ℝ) - (1-x) := by linarith
        _ ≤ x^2/2 := by nlinarith [sq_nonneg (x-1)]
    rw [abs_of_nonneg hnonneg]
    exact hupper



private lemma L4_Taylor3 (y : ℝ) :
    ‖Complex.exp ((y : ℂ) * Complex.I) -
      (1 + (y : ℂ) * Complex.I - (y : ℂ)^2 / 2)‖ ≤ |y|^3 / 6 := by
  let f : ℝ → ℂ := fun x => Complex.exp ((x : ℂ) * Complex.I)
  have hf : ContDiff ℝ 3 f := by
    dsimp [f]
    have hr : ContDiff ℝ 3 (fun x : ℝ => (x : ℂ)) := by
      change ContDiff ℝ 3 (Complex.ofRealCLM : ℝ → ℂ)
      exact Complex.ofRealCLM.contDiff
    have hi : ContDiff ℝ 3 (fun x : ℝ => (x : ℂ) * Complex.I) := by
      simpa [smul_eq_mul] using hr.smul_const Complex.I
    have he : ContDiff ℝ 3 (Complex.exp : ℂ → ℂ) := Complex.contDiff_exp
    simpa [Function.comp_def] using he.comp hi
  have hHasDeriv (x : ℝ) : HasDerivAt f (f x * Complex.I) x := by
    have hi : HasDerivAt (fun z : ℝ => (z : ℂ) * Complex.I) Complex.I x := by
      simpa [Complex.ofRealCLM_apply] using
        (Complex.ofRealCLM.hasDerivAt (x := x)).mul_const Complex.I
    have he := (Complex.hasDerivAt_exp ((x : ℂ) * Complex.I)).comp x hi
    simpa [f, Function.comp_def] using he
  have hderiv (x : ℝ) : deriv f x = f x * Complex.I := (hHasDeriv x).deriv
  have hderiv_mul (c : ℂ) : deriv (fun x : ℝ => f x * c) =
      fun x => f x * Complex.I * c := by
    funext x
    exact ((hHasDeriv x).mul_const c).deriv
  have hderiv_mul_mul (c d : ℂ) : deriv (fun x : ℝ => f x * c * d) =
      fun x => f x * Complex.I * c * d := by
    funext x
    exact (((hHasDeriv x).mul_const c).mul_const d).deriv
  have hi1 : iteratedDeriv 1 f = fun x => f x * Complex.I := by
    rw [iteratedDeriv_one]
    funext x
    exact hderiv x
  have hi2 : iteratedDeriv 2 f = fun x => f x * Complex.I * Complex.I := by
    rw [iteratedDeriv_succ, hi1]
    exact hderiv_mul Complex.I
  have hi3 : iteratedDeriv 3 f = fun x => f x * Complex.I * Complex.I * Complex.I := by
    rw [iteratedDeriv_succ, hi2]
    exact hderiv_mul_mul Complex.I Complex.I
  rcases eq_or_ne y 0 with rfl | hy
  · simp [f]
  have hu : UniqueDiffOn ℝ (Set.uIcc 0 y) := uniqueDiffOn_uIcc hy.symm
  have htw1 (x : ℝ) (hx : x ∈ Set.uIcc 0 y) :
      iteratedDerivWithin 1 f (Set.uIcc 0 y) x = iteratedDeriv 1 f x := by
    exact iteratedDerivWithin_eq_iteratedDeriv hu (hf.contDiffAt.of_le (by norm_num)) hx
  have htw2 (x : ℝ) (hx : x ∈ Set.uIcc 0 y) :
      iteratedDerivWithin 2 f (Set.uIcc 0 y) x = iteratedDeriv 2 f x := by
    exact iteratedDerivWithin_eq_iteratedDeriv hu (hf.contDiffAt.of_le (by norm_num)) hx
  have htw3 (x : ℝ) (hx : x ∈ Set.uIcc 0 y) :
      iteratedDerivWithin 3 f (Set.uIcc 0 y) x = iteratedDeriv 3 f x := by
    exact iteratedDerivWithin_eq_iteratedDeriv hu (hf.contDiffAt.of_le (by norm_num)) hx
  have ht := taylor_integral_remainder (f := f) (x := y) (x₀ := 0) (n := 2)
    (hf.contDiffOn)
  have htaylor : f y - (f 0 +
      ((1 : ℝ) * (Nat.factorial 0 : ℝ))⁻¹ * (y - 0)^1 • iteratedDerivWithin 1 f (Set.uIcc 0 y) 0 +
      (((2 : ℝ) * (Nat.factorial 1 : ℝ))⁻¹ * (y - 0)^2) • iteratedDerivWithin 2 f (Set.uIcc 0 y) 0) =
      ∫ t in 0..y, ((y-t)^2 / (2 : ℝ)) • iteratedDerivWithin 3 f (Set.uIcc 0 y) t := by
    convert ht using 1 <;> norm_num [taylorWithinEval_succ, taylor_within_zero_eval,
      Nat.factorial] <;> ring
  have htaylor' : f y - (1 + (y : ℂ) * Complex.I - (y : ℂ)^2 / 2) =
      ∫ t in 0..y, ((y-t)^2 / (2 : ℝ)) • (f t * Complex.I * Complex.I * Complex.I) := by
    have hleft : f y - (1 + (y : ℂ) * Complex.I - (y : ℂ)^2 / 2) =
        f y - (f 0 +
          ((1 : ℝ) * (Nat.factorial 0 : ℝ))⁻¹ * (y - 0)^1 • iteratedDerivWithin 1 f (Set.uIcc 0 y) 0 +
          (((2 : ℝ) * (Nat.factorial 1 : ℝ))⁻¹ * (y - 0)^2) • iteratedDerivWithin 2 f (Set.uIcc 0 y) 0) := by
      rw [htw1 0 (by simp), htw2 0 (by simp), hi1, hi2]
      simp [f, smul_eq_mul]
      ring
    calc
      _ = f y - (f 0 +
          ((1 : ℝ) * (Nat.factorial 0 : ℝ))⁻¹ * (y - 0)^1 • iteratedDerivWithin 1 f (Set.uIcc 0 y) 0 +
          (((2 : ℝ) * (Nat.factorial 1 : ℝ))⁻¹ * (y - 0)^2) • iteratedDerivWithin 2 f (Set.uIcc 0 y) 0) := hleft
      _ = ∫ t in 0..y, ((y-t)^2 / (2 : ℝ)) • iteratedDerivWithin 3 f (Set.uIcc 0 y) t := htaylor
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro t htmem
        change ((y-t)^2 / (2 : ℝ)) • iteratedDerivWithin 3 f (Set.uIcc 0 y) t =
          ((y-t)^2 / (2 : ℝ)) • (f t * Complex.I * Complex.I * Complex.I)
        rw [htw3 t htmem, hi3]
  have hnorm_integrand (t : ℝ) :
      ‖((y-t)^2 / (2 : ℝ)) • (f t * Complex.I * Complex.I * Complex.I)‖ =
        (y-t)^2 / 2 := by
    rw [norm_smul]
    have hcoef : 0 ≤ (y-t)^2 / (2 : ℝ) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hcoef]
    dsimp [f]
    simp [Complex.norm_exp_ofReal_mul_I]
  have hanti_raw (t : ℝ) : HasDerivAt (fun z : ℝ => -(y-z)^3/6)
      (3 * (y-t)^2/6) t := by
    simpa [Function.comp_def, id_eq] using
      (((hasDerivAt_id t).const_sub y).pow 3).neg.div_const 6
  have hanti (t : ℝ) : HasDerivAt (fun z : ℝ => -(y-z)^3/6) ((y-t)^2/2) t := by
    rw [show (y-t)^2/2 = 3 * (y-t)^2/6 by ring]
    exact hanti_raw t
  have hint : IntervalIntegrable (fun t : ℝ => (y-t)^2/2) volume 0 y := by
    exact (by fun_prop : Continuous (fun t : ℝ => (y-t)^2/2)).intervalIntegrable 0 y
  have hInt : (∫ t in 0..y, (y-t)^2/2) = y^3/6 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hanti t) hint]
    ring
  have hIntNeg : (∫ t in y..0, (y-t)^2/2) = (-y)^3/6 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hanti t)
      ((by fun_prop : Continuous (fun t : ℝ => (y-t)^2/2)).intervalIntegrable y 0)]
    ring
  by_cases hy0 : 0 ≤ y
  · rw [htaylor']
    calc
      ‖∫ t in 0..y, ((y-t)^2 / (2 : ℝ)) • (f t * Complex.I * Complex.I * Complex.I)‖ ≤
          ∫ t in 0..y, ‖((y-t)^2 / (2 : ℝ)) • (f t * Complex.I * Complex.I * Complex.I)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hy0
      _ = y^3/6 := by rw [intervalIntegral.integral_congr (fun t ht => hnorm_integrand t), hInt]
      _ = |y|^3/6 := by rw [abs_of_nonneg hy0]
  · have hy0' : y ≤ 0 := le_of_not_ge hy0
    rw [htaylor']
    calc
      ‖∫ t in 0..y, ((y-t)^2 / (2 : ℝ)) • (f t * Complex.I * Complex.I * Complex.I)‖ =
          ‖∫ t in y..0, ((y-t)^2 / (2 : ℝ)) • (f t * Complex.I * Complex.I * Complex.I)‖ := by
            rw [intervalIntegral.integral_symm]
            simp
      _ ≤ ∫ t in y..0, ‖((y-t)^2 / (2 : ℝ)) • (f t * Complex.I * Complex.I * Complex.I)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hy0'
      _ = (-y)^3/6 := by rw [intervalIntegral.integral_congr (fun t ht => hnorm_integrand t), hIntNeg]
      _ = |y|^3/6 := by rw [abs_of_nonpos hy0']
open Polynomial Finset Filter Real MeasureTheory
open scoped BigOperators

private lemma centered_bernoulli_single_gaussian_error (p s : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ‖centeredBernoulli p s -
      (Real.exp (-s^2 * (p * (1 - p)) / 2) : ℂ)‖ ≤
      (p * (1 - p)) * |s|^3 / 6 + (p * (1 - p)) ^ 2 * s^4 / 8 := by
  have hv := bernoulli_variance_bounds p hp0 hp1
  have hthird := bernoulli_third_moment_bound p hp0 hp1
  have ht1 := L4_Taylor3 (-s*p)
  have ht2 := L4_Taylor3 (s*(1-p))
  have hdecomp : centeredBernoulli p s -
      (1 - (p * (1 - p)) * s^2 / 2 : ℂ) =
      (1-p : ℂ) * (Complex.exp ((-s*p : ℝ) * Complex.I) -
        (1 + ((-s*p : ℝ) : ℂ) * Complex.I - ((-s*p : ℝ) : ℂ)^2 / 2)) +
      (p : ℂ) * (Complex.exp ((s*(1-p) : ℝ) * Complex.I) -
        (1 + ((s*(1-p) : ℝ) : ℂ) * Complex.I - ((s*(1-p) : ℝ) : ℂ)^2 / 2)) := by
    unfold centeredBernoulli
    push_cast
    ring
  have hrem : ‖centeredBernoulli p s -
      (1 - (p * (1 - p)) * s^2 / 2 : ℂ)‖ ≤
      (p * (1 - p)) * |s|^3 / 6 := by
    rw [hdecomp]
    calc
      _ ≤ ‖(1-p : ℂ) * (Complex.exp ((-s*p : ℝ) * Complex.I) -
          (1 + ((-s*p : ℝ) : ℂ) * Complex.I - ((-s*p : ℝ) : ℂ)^2 / 2))‖ +
          ‖(p : ℂ) * (Complex.exp ((s*(1-p) : ℝ) * Complex.I) -
          (1 + ((s*(1-p) : ℝ) : ℂ) * Complex.I - ((s*(1-p) : ℝ) : ℂ)^2 / 2))‖ := norm_add_le _ _
      _ = |1-p| * ‖Complex.exp ((-s*p : ℝ) * Complex.I) -
          (1 + ((-s*p : ℝ) : ℂ) * Complex.I - ((-s*p : ℝ) : ℂ)^2 / 2)‖ +
          |p| * ‖Complex.exp ((s*(1-p) : ℝ) * Complex.I) -
          (1 + ((s*(1-p) : ℝ) : ℂ) * Complex.I - ((s*(1-p) : ℝ) : ℂ)^2 / 2)‖ := by
            simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            congr 1
            · congr 1
              rw [show (1 : ℂ) - (p : ℂ) = ((1-p : ℝ) : ℂ) by norm_num]
              exact Complex.norm_real _
      _ ≤ |1-p| * (|-s*p|^3/6) + |p| * (|s*(1-p)|^3/6) := by
        gcongr
      _ = (p*|1-p|^3 + (1-p)*|p|^3) * |s|^3 / 6 := by
        simp only [abs_mul, abs_neg]
        have hpabs : |p| = p := abs_of_nonneg hp0
        have h1abs : |1-p| = 1-p := abs_of_nonneg (by linarith)
        rw [hpabs, h1abs]
        ring
      _ ≤ (p * (1 - p)) * |s|^3 / 6 := by
        have hh := mul_le_mul_of_nonneg_right hthird (by positivity : 0 ≤ |s|^3)
        nlinarith [hh]
  let x : ℝ := s^2 * (p * (1 - p)) / 2
  have hx : 0 ≤ x := by
    dsimp [x]
    positivity
  have hexp := L4_Exp2 x hx
  have hgauss : ‖(Real.exp (-x) : ℂ) - (1 - x : ℂ)‖ ≤ x^2/2 := by
    exact_mod_cast hexp
  calc
    ‖centeredBernoulli p s - (Real.exp (-s^2 * (p * (1 - p)) / 2) : ℂ)‖ ≤
        ‖centeredBernoulli p s - (1 - (p * (1 - p)) * s^2 / 2 : ℂ)‖ +
          ‖(1 - (p * (1 - p)) * s^2 / 2 : ℂ) -
            (Real.exp (-s^2 * (p * (1 - p)) / 2) : ℂ)‖ := by
      calc
        _ = ‖(centeredBernoulli p s - (1 - (p * (1 - p)) * s^2 / 2 : ℂ)) +
            ((1 - (p * (1 - p)) * s^2 / 2 : ℂ) -
              (Real.exp (-s^2 * (p * (1 - p)) / 2) : ℂ))‖ := by
          congr 1
          ring
        _ ≤ _ := norm_add_le _ _
    _ ≤ (p * (1 - p)) * |s|^3 / 6 + x^2/2 := by
      apply add_le_add hrem
      rw [norm_sub_rev]
      have hxeq : s^2 * (p * (1 - p)) / 2 = x := by
        dsimp [x]
      calc
        ‖(Real.exp (-s^2 * (p * (1 - p)) / 2) : ℂ) -
            (1 - (p * (1 - p)) * s^2 / 2 : ℂ)‖ =
            ‖(Real.exp (-x) : ℂ) - (1 - x : ℂ)‖ := by
              congr 1
              rw [← hxeq]
              norm_num
              ring
        _ ≤ x^2/2 := hgauss
    _ = (p * (1 - p)) * |s|^3 / 6 + (p * (1 - p)) ^ 2 * s^4 / 8 := by
      dsimp [x]
      ring_nf
open Polynomial Finset Filter Real MeasureTheory
open scoped BigOperators

private lemma centered_bernoulli_product_gaussian_error {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ i, 0≤p i ∧ p i≤1) (u : ℝ)
    (hV : 0 < ∑ i, (p i * (1 - p i))) :
    ‖(∏ i, centeredBernoulli (p i) (u/√(∑ j, (p j * (1 - p j))))) -
      (Real.exp (-u^2/2):ℂ)‖ ≤
      |u|^3/(6*√(∑ j, (p j * (1 - p j)))) +
        u^4/(32*(∑ j, (p j * (1 - p j)))) := by
  apply centered_bernoulli_product_gaussian_error_of_single p hp u hV
  intro i
  exact centered_bernoulli_single_gaussian_error (p i)
    (u/√(∑ j, (p j * (1 - p j)))) (hp i).1 (hp i).2
open Polynomial Finset Filter Real MeasureTheory Topology
open scoped BigOperators

lemma centered_bernoulli_charFun_tendsto {m : ℕ → ℕ} (p : ∀ n, Fin (m n) → ℝ)
    (V : ℕ → ℝ) (u : ℝ)
    (hvalid : ∀ᶠ n in atTop, (∀ i, 0 ≤ p n i ∧ p n i ≤ 1) ∧
      V n = ∑ i, (p n i * (1 - p n i)) ∧ 0 < V n)
    (hV : Tendsto V atTop atTop)
    (hVeq : ∀ n, V n = ∑ i, (p n i * (1 - p n i))) :
    Tendsto (fun n => ∏ i, centeredBernoulli (p n i) (u / √(V n))) atTop
      (𝓝 (Real.exp (-u^2 / 2) : ℂ)) := by
  have hsqrt : Tendsto (fun n => √(V n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hV
  have hinvsqrt : Tendsto (fun n => (√(V n))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  have hinv : Tendsto (fun n => (V n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hV
  have hterm1 : Tendsto (fun n => (|u|^3 / 6) * (√(V n))⁻¹) atTop (𝓝 0) := by
    simpa using (hinvsqrt.const_mul (|u|^3 / 6))
  have hterm2 : Tendsto (fun n => (u^4 / 32) * (V n)⁻¹) atTop (𝓝 0) := by
    simpa using (hinv.const_mul (u^4 / 32))
  have herr : Tendsto (fun n => (|u|^3 / (6 * √(V n))) + u^4 / (32 * V n)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => |u|^3 / (6 * √(V n))) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hterm1
    have h2 : Tendsto (fun n => u^4 / (32 * V n)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hterm2
    simpa using h1.add h2
  have hbound : ∀ᶠ n in atTop,
      ‖(∏ i, centeredBernoulli (p n i) (u / √(V n))) -
        (Real.exp (-u^2 / 2) : ℂ)‖ ≤
        (|u|^3 / (6 * √(V n))) + u^4 / (32 * V n) := by
    filter_upwards [hvalid] with n hn
    have hlocal : ∀ i, ‖centeredBernoulli (p n i) (u / √(V n)) -
        (Real.exp (-(u / √(V n))^2 * (p n i * (1 - p n i)) / 2) : ℂ)‖ ≤
        (p n i * (1 - p n i)) * |u / √(V n)|^3 / 6 +
          (p n i * (1 - p n i))^2 * (u / √(V n))^4 / 8 := by
      intro i
      exact centered_bernoulli_single_gaussian_error (p n i) (u / √(V n))
        (hn.1 i).1 (hn.1 i).2
    have hprod := centered_bernoulli_product_gaussian_error (p n) hn.1 u
      (by simpa [hVeq n] using hn.2)
    simpa [hVeq n] using hprod
  apply (tendsto_iff_norm_sub_tendsto_zero).2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds)
    herr
  · exact Eventually.of_forall (fun n => norm_nonneg _)
  · exact hbound
open Finset Real
open scoped BigOperators

lemma centeredBernoulli_eq_phase (p s : ℝ) :
    centeredBernoulli p s = Complex.exp ((-s*p : ℝ)*Complex.I) *
      ((1-p : ℝ) + (p:ℝ)*Complex.exp ((s:ℂ)*Complex.I)) := by
  unfold centeredBernoulli
  rw [mul_add]
  have he : Complex.exp ((-s*p : ℝ)*Complex.I) * Complex.exp ((s:ℂ)*Complex.I) =
      Complex.exp ((s*(1-p) : ℝ)*Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [show Complex.exp ((-s*p : ℝ)*Complex.I) * ((p:ℝ)*Complex.exp ((s:ℂ)*Complex.I)) =
    (p:ℝ)*(Complex.exp ((-s*p : ℝ)*Complex.I) * Complex.exp ((s:ℂ)*Complex.I)) by ring,he]
  ring

private lemma bernoulli_char_norm_sq (p s : ℝ) :
    ‖((1-p : ℝ):ℂ) + (p:ℝ)*Complex.exp ((s:ℂ)*Complex.I)‖^2 =
      1-4*(p * (1 - p)) * Real.sin (s/2)^2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.exp_mul_I, Complex.normSq_apply, Complex.add_re, Complex.mul_re,
    Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im,
    Complex.cos_ofReal_re, Complex.cos_ofReal_im]
  have htrig := Real.sin_sq_add_cos_sq s
  have hhalf := Real.cos_two_mul (s/2)
  have hs : 2*(s/2)=s := by ring
  rw [hs] at hhalf
  have hcos : Real.cos s = 1-2*Real.sin (s/2)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq (s/2)]
  simp only [mul_zero,zero_mul,mul_one,add_zero,zero_add,sub_zero]
  calc
    _ = (1-p)^2 + 2*(1-p)*p*Real.cos s +
      p^2*(Real.sin s^2+Real.cos s^2) := by ring
    _ = _ := by rw [htrig,hcos]; ring

private lemma centered_bernoulli_gaussian_envelope (p s : ℝ) :
    ‖centeredBernoulli p s‖ ≤ Real.exp (-2*(p * (1 - p)) * Real.sin (s/2)^2) := by
  rw [centeredBernoulli_eq_phase,norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
  have hsq := bernoulli_char_norm_sq p s
  have he := Real.add_one_le_exp (-4*(p * (1 - p)) * Real.sin (s/2)^2)
  have heq : Real.exp (-4*(p * (1 - p)) * Real.sin (s/2)^2) =
      Real.exp (-2*(p * (1 - p)) * Real.sin (s/2)^2)^2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [heq] at he
  nlinarith [norm_nonneg (((1-p : ℝ):ℂ)+(p:ℝ)*Complex.exp ((s:ℂ)*Complex.I)),
    Real.exp_pos (-2*(p * (1 - p)) * Real.sin (s/2)^2)]

private lemma centered_bernoulli_product_envelope {m : ℕ} (p : Fin m → ℝ) (s : ℝ) :
    ‖∏ i, centeredBernoulli (p i) s‖ ≤
      Real.exp (-2*(∑ i, (p i * (1 - p i)))*Real.sin (s/2)^2) := by
  rw [norm_prod]
  calc
    _ ≤ ∏ i, Real.exp (-2*(p i * (1 - p i))*Real.sin (s/2)^2) :=
      prod_le_prod₀ (by intro i hi; exact norm_nonneg _)
        (by intro i hi; exact centered_bernoulli_gaussian_envelope _ _)
    _ = _ := by rw [← Real.exp_sum]; congr 1; simp only [sum_mul,mul_sum]

lemma normalized_bernoulli_product_envelope {m : ℕ} (p : Fin m → ℝ) (V u : ℝ)
    (hV : 0 < V) (hVeq : V = ∑ i, (p i * (1 - p i)))
    (hu : |u| ≤ Real.pi*Real.sqrt V) :
    ‖∏ i, centeredBernoulli (p i) (u/Real.sqrt V)‖ ≤
      Real.exp (-2*u^2/Real.pi^2) := by
  have hs : 0 < √V := Real.sqrt_pos.2 hV
  have hpi := Real.pi_pos
  have hx0 : 0 ≤ |u/√V|/2 := by positivity
  have hx1 : |u/√V|/2 ≤ Real.pi/2 := by
    rw [abs_div,abs_of_pos hs]
    apply (div_le_div_iff_of_pos_right (by norm_num : (0:ℝ)<2)).2
    exact (div_le_iff₀ hs).2 hu
  have hsin := Real.mul_le_sin hx0 hx1
  have hsin0 := Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith)
  have heq : Real.sin ((u/√V)/2)^2 = Real.sin (|u/√V|/2)^2 := by
    have habs : |u/√V|/2 = |(u/√V)/2| := by
      rw [abs_div (u/√V) (2:ℝ), abs_of_pos (by norm_num : (0:ℝ)<2)]
    rw [habs]
    rcases le_total 0 ((u/√V)/2) with h|h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h,Real.sin_neg]; ring
  have hsquare : (2/Real.pi*(|u/√V|/2))^2 ≤ Real.sin (|u/√V|/2)^2 :=
    sq_le_sq₀ (by positivity) hsin0 |>.2 hsin
  have hcalc : V*(2/Real.pi*(|u/√V|/2))^2 = u^2/Real.pi^2 := by
    rw [abs_div,abs_of_pos hs]
    have hs2 := Real.sq_sqrt hV.le
    calc
      _ = (√V)^2*(2/Real.pi*(|u|/√V/2))^2 := by rw [hs2]
      _ = _ := by field_simp; rw [sq_abs]
  have hb := mul_le_mul_of_nonneg_left hsquare hV.le
  rw [hcalc,← heq] at hb
  calc
    _ ≤ Real.exp (-2*V*Real.sin ((u/√V)/2)^2) := by
      simpa [← hVeq] using centered_bernoulli_product_envelope p (u/√V)
    _ ≤ _ := Real.exp_le_exp.2 (by
      calc
        _ = -2*(V*Real.sin ((u/√V)/2)^2) := by ring
        _ ≤ -2*(u^2/Real.pi^2) := mul_le_mul_of_nonpos_left hb (by norm_num)
        _ = _ := by ring)
def bernoulliWeight {m : ℕ} (p : Fin m → unitInterval) (x : Fin m → Bool) : ℝ :=
  ∏ i, if x i then (p i:ℝ) else 1-(p i:ℝ)


def bernoulliSpace {m : ℕ} (p : Fin m → unitInterval) : Measure (Fin m → Bool) :=
  Measure.pi (fun i => bernoulliMeasure true false (p i))


instance bernoulliSpaceProbability {m : ℕ} (p : Fin m → unitInterval) : IsProbabilityMeasure (bernoulliSpace p) := by
  unfold bernoulliSpace
  infer_instance


lemma bernoulli_atom {m : ℕ} (p : Fin m → unitInterval) (x : Fin m → Bool) :
    (bernoulliSpace p).real {x} = bernoulliWeight p x := by
  simp only [bernoulliSpace, bernoulliWeight, measureReal_def, Measure.pi_singleton,
    ENNReal.toReal_prod]
  apply prod_congr rfl
  intro i hi
  cases hx : x i <;> simp [hx, bernoulliMeasure_real_apply, ← measureReal_def]


end D5.S3.Analytic.Probability.UniformCDFConvergence
