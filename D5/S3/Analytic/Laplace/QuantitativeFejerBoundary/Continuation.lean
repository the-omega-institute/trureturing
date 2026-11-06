/- GID: D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive Laplace transforms and paired pole sums admit analytic continuation on right strips. -/

import D5.S3.Analytic.Laplace.PairedPoleRegularity
import D5.S3.Analytic.Fourier.AngularFejerKernel
import D5.S3.Analytic.Laplace.AbscissaSingularity
import Mathlib.Analysis.Analytic.Uniqueness

/-! Positive Laplace transforms and paired pole sums admit analytic continuation on right strips. -/

namespace D5.S3.Analytic.Laplace.QuantitativeFejerBoundary

open D5.S3.Analytic.Fourier.AngularFejerKernel
  D5.S3.Analytic.Oscillation.OrdinateCounting
  D5.S3.Analytic.Laplace.PairedPoleRegularity
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

noncomputable section

def HasLogEnvelope (f : ℝ → ℝ) : Prop :=
  ∃ e kappa C : ℝ, |e| = 1 ∧ 0 ≤ kappa ∧ 0 ≤ C ∧
    ∀ u : ℝ, 0 ≤ u → e * f u ≤ kappa * ell u + C

def Admissible (g w : ℝ → ℝ) (b M : ℝ) : Prop :=
  (g = K b ∧ w = phi b ∧ b ≤ M) ∨
    ∃ U : ℝ, 2 * b < U ∧ g = H b U ∧ w = psi b U ∧ U + b ≤ M

def rayMeasure (q : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ici 0)).withDensity (fun u => ENNReal.ofReal (q u))

lemma ray_integrable_iff {q : ℝ → ℝ} (hq : Measurable q)
    (hpos : ∀ u : ℝ, 0 ≤ u → 0 ≤ q u) (t : ℝ) :
    Integrable (fun u : ℝ => Real.exp (t * u)) (rayMeasure q) ↔
      IntegrableOn (fun u => q u * Real.exp (t * u)) (Ici 0) := by
  rw [rayMeasure, integrable_withDensity_iff_integrable_smul'
    (hq.ennreal_ofReal) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
  simp [ENNReal.toReal_ofReal (hpos u hu), smul_eq_mul]

lemma ray_mgf {q : ℝ → ℝ} (hq : Measurable q)
    (hpos : ∀ u : ℝ, 0 ≤ u → 0 ≤ q u) (s : ℂ) :
    complexMGF id (rayMeasure q) (-s) = laplace q s := by
  rw [complexMGF, rayMeasure, integral_withDensity_eq_integral_toReal_smul
    hq.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
  simp [ENNReal.toReal_ofReal (hpos u hu), neg_mul]

lemma ray_nonneg (q : ℝ → ℝ) : ∀ᵐ u ∂rayMeasure q, 0 ≤ u :=
  (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem measurableSet_Ici)

lemma exp_integrable {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun u : ℝ => Real.exp (-σ * u)) (Ici 0) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact integrableOn_exp_mul_Ioi (by linarith) 0

private lemma exp_interior {σ : ℝ} (hσ : 0 < σ) :
    -σ ∈ interior (integrableExpSet id (volume.restrict (Ici (0 : ℝ)))) := by
  apply mem_interior.mpr
  refine ⟨Iio 0, ?_, isOpen_Iio, by simpa using neg_neg_of_pos hσ⟩
  intro t ht
  change IntegrableOn (fun u : ℝ => Real.exp (t * u)) (Ici 0)
  simpa using exp_integrable (σ := -t) (neg_pos.mpr ht)

lemma affine_integrable (a c : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun u : ℝ => (a * u + c) * Real.exp (-σ * u)) (Ici 0) := by
  have hu := integrable_pow_mul_exp_of_mem_interior_integrableExpSet (exp_interior hσ) 1
  simp only [id_eq, pow_one] at hu
  have heq : (fun u : ℝ => (a * u + c) * Real.exp (-σ * u)) =
      (fun u => a * (u * Real.exp (-σ * u)) + c * Real.exp (-σ * u)) := by
    funext u; ring
  rw [heq]
  exact (hu.const_mul a).add ((exp_integrable hσ).const_mul c)

lemma laplace_integrable {q : ℝ → ℝ} (hq : Measurable q) {s : ℂ}
    (hi : IntegrableOn (fun u : ℝ => q u * Real.exp (-s.re * u)) (Ici 0)) :
    IntegrableOn (fun u : ℝ => (q u : ℂ) * Complex.exp (-s * (u : ℂ))) (Ici 0) := by
  apply (integrable_norm_iff (by fun_prop)).mp
  convert hi.norm using 1
  ext u
  simp [norm_mul, Complex.norm_exp, Complex.mul_re]


def strip : Set ℂ := {s | 0 < s.re ∧ s.re < 1 ∧ |s.im| < 1}

private lemma strip_open : IsOpen strip :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt Complex.continuous_im.abs continuous_const))

private lemma strip_convex : Convex ℝ strip := by
  have heq : strip = {s : ℂ | 0 < s.re} ∩ {s | s.re < 1} ∩
      {s | -1 < s.im} ∩ {s | s.im < 1} := by
    ext s; simp [strip, abs_lt]; tauto
  rw [heq]
  exact (((convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)).inter
    (convex_halfSpace_im_gt (-1))).inter (convex_halfSpace_im_lt 1)

private lemma pole_differentiable (S : Spectrum) (j : S.index) :
    DifferentiableOn ℂ (poleTerm S j) strip := by
  intro s hs
  have hm : s - (S.gamma j : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    exact (ne_of_gt hs.1) hh
  have hp : s + (S.gamma j : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    exact (ne_of_gt hs.1) hh
  have hid : DifferentiableAt ℂ (fun z : ℂ => z) s := differentiableAt_id
  have hmder := hid.sub (differentiableAt_const ((S.gamma j : ℂ) * Complex.I))
  have hpder := hid.add (differentiableAt_const ((S.gamma j : ℂ) * Complex.I))
  exact ((((differentiableAt_const (1 : ℂ)).div hmder hm).add
    ((differentiableAt_const (1 : ℂ)).div hpder hp)).const_mul
    (S.mult j : ℂ)).differentiableWithinAt

private lemma pole_tail_bound (S : Spectrum) (j : S.index) (hj : 8 < S.gamma j)
    {s : ℂ} (hs : s ∈ strip) :
    ‖poleTerm S j s‖ ≤ 64 * ((S.mult j : ℝ) / (S.gamma j) ^ 2) := by
  have hn : ‖s‖ ≤ 2 := by
    have := Complex.norm_le_abs_re_add_abs_im s
    have hr : |s.re| < 1 := by rw [abs_of_pos hs.1]; exact hs.2.1
    linarith [hs.2.2]
  have hg := S.gamma_pos j
  have hgamma : ‖(S.gamma j : ℂ) * Complex.I‖ = S.gamma j := by
    simp [abs_of_pos hg]
  have hm := norm_sub_norm_le ((S.gamma j : ℂ) * Complex.I) s
  have hp := norm_sub_norm_le (-((S.gamma j : ℂ) * Complex.I)) s
  rw [hgamma, norm_sub_rev] at hm
  rw [norm_neg, hgamma, norm_sub_rev, sub_neg_eq_add] at hp
  have hm0 : s - (S.gamma j : ℂ) * Complex.I ≠ 0 := norm_pos_iff.mp (by linarith)
  have hp0 : s + (S.gamma j : ℂ) * Complex.I ≠ 0 := norm_pos_iff.mp (by linarith)
  have heq : poleTerm S j s = (S.mult j : ℂ) * (2 * s) /
      ((s - (S.gamma j : ℂ) * Complex.I) * (s + (S.gamma j : ℂ) * Complex.I)) := by
    unfold poleTerm
    field_simp
    ring
  rw [heq, norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_natCast]
  norm_num only [Complex.norm_ofNat]
  apply (div_le_iff₀ (mul_pos (norm_pos_iff.mpr hm0) (norm_pos_iff.mpr hp0))).mpr
  have hl : S.gamma j / 2 ≤ ‖s - (S.gamma j : ℂ) * Complex.I‖ := by linarith
  have hr : S.gamma j / 2 ≤ ‖s + (S.gamma j : ℂ) * Complex.I‖ := by linarith
  have hprod := mul_le_mul hl hr (by positivity) (norm_nonneg _)
  have he : (64 * ((S.mult j : ℝ) / (S.gamma j) ^ 2)) *
      ((S.gamma j / 2) * (S.gamma j / 2)) = 16 * (S.mult j : ℝ) := by
    field_simp
    ring
  have hh := mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ 64 * ((S.mult j : ℝ) / (S.gamma j) ^ 2) by positivity)
  rw [he] at hh
  nlinarith [show (0 : ℝ) ≤ (S.mult j : ℝ) from Nat.cast_nonneg _]

def continuation (S : Spectrum) (J : ℂ → ℂ) (s : ℂ) : ℂ :=
  -(1 / 2 : ℂ) * (∑ j ∈ S.cut 8, poleTerm S j s) + regularPart S J 4 s

lemma continuation_holomorphic (S : Spectrum) (hN : CountAsymptotic S)
    {f : ℝ → ℝ} {k : ℕ} (D : PairedLaplaceData S f k) :
    DifferentiableOn ℂ (continuation S D.J) strip := by
  obtain ⟨C, _, htail⟩ := inverse_square_tail S hN
  have ht : DifferentiableOn ℂ
      (fun s => ∑' j : {j : S.index // 2 * 4 < S.gamma j}, poleTerm S j.val s) strip := by
    apply Complex.differentiableOn_tsum_of_summable_norm
      (((htail (2 * 4) (by norm_num)).1).mul_left 64)
    · intro j
      exact pole_differentiable S j.val
    · exact strip_open
    · intro j s hs
      exact pole_tail_bound S j.val (by nlinarith [j.property]) hs
  have hJ : DifferentiableOn ℂ D.J strip := D.holomorphic.mono (by
    intro s hs
    exact ⟨by linarith [hs.1, D.eta_pos], hs.2.1⟩)
  have hfin : DifferentiableOn ℂ (fun s => ∑ j ∈ S.cut 8, poleTerm S j s) strip := by
    apply DifferentiableOn.fun_sum
    intro j _
    exact pole_differentiable S j
  unfold continuation regularPart
  exact (hfin.const_mul (-(1 / 2 : ℂ))).add (hJ.sub (ht.const_mul (1 / 2 : ℂ)))

lemma continuation_initial (S : Spectrum) (hN : CountAsymptotic S)
    {f : ℝ → ℝ} {k : ℕ} (D : PairedLaplaceData S f k)
    {s : ℂ} (h1 : 1 / 2 < s.re) (h2 : s.re < 1) :
    laplace f s = continuation S D.J s := by
  simpa only [continuation, show (2 : ℝ) * 4 = 8 by norm_num] using
    (laplace_eq_finite_poles_add_regular S hN D (M := 4) (by norm_num) h1 h2)

private lemma initial_interior {μ : Measure ℝ}
    (hc : ∀ σ : ℝ, 1 / 2 < σ → Integrable (fun u : ℝ => Real.exp (-σ * u)) μ)
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    -σ ∈ interior (integrableExpSet id μ) := by
  apply mem_interior.mpr
  refine ⟨Iio (-(1 / 2 : ℝ)), ?_, isOpen_Iio, by change -σ < -(1 / 2 : ℝ); linarith⟩
  intro t ht
  change Integrable (fun u : ℝ => Real.exp (t * u)) μ
  simpa only [neg_neg] using hc (-t) (by change t < -(1 / 2) at ht; linarith)

private lemma identity_on_convergence {μ : Measure ℝ}
    (hc : ∀ σ : ℝ, 1 / 2 < σ → Integrable (fun u : ℝ => Real.exp (-σ * u)) μ)
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F strip)
    (hi : ∀ s : ℂ, 1 / 2 < s.re → s ∈ strip → complexMGF id μ (-s) = F s)
    {s : ℂ} (hs : s ∈ strip)
    (hsi : (-s).re ∈ interior (integrableExpSet id μ)) :
    complexMGF id μ (-s) = F s := by
  let U : Set ℂ := {z : ℂ | (-z).re ∈ interior (integrableExpSet id μ)} ∩ strip
  have hU : IsOpen U :=
    (isOpen_interior.preimage (Complex.continuous_re.comp continuous_neg)).inter strip_open
  have hUc : IsPreconnected U :=
    ((convex_integrableExpSet.interior.linear_preimage (-Complex.reLm)).inter
      strip_convex).isPreconnected
  have hLa : AnalyticOnNhd ℂ (fun z => complexMGF id μ (-z)) U := by
    intro z hz
    exact (analyticAt_complexMGF hz.1).comp
      (show AnalyticAt ℂ (fun w : ℂ => -w) z by fun_prop)
  have hFa : AnalyticOnNhd ℂ F U := (hF.mono inter_subset_right).analyticOnNhd hU
  have hseed : ((3 / 4 : ℝ) : ℂ) ∈ U := by
    constructor
    · simpa using initial_interior hc (σ := 3 / 4) (by norm_num)
    · norm_num [strip]
  have hEq : (fun z => complexMGF id μ (-z)) =ᶠ[𝓝 ((3 / 4 : ℝ) : ℂ)] F := by
    filter_upwards [strip_open.mem_nhds hseed.2,
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (1 / 2 : ℝ) < (((3 / 4 : ℝ) : ℂ)).re by norm_num)] with z hz hzhalf
    exact hi z hzhalf hz
  exact hLa.eqOn_of_preconnected_of_eventuallyEq hFa hUc hseed hEq ⟨hsi, hs⟩

lemma positive_convergence {μ : Measure ℝ}
    (hpos : ∀ᵐ u ∂μ, 0 ≤ u)
    (hc : ∀ σ : ℝ, 1 / 2 < σ → Integrable (fun u : ℝ => Real.exp (-σ * u)) μ)
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F strip)
    (hi : ∀ s : ℂ, 1 / 2 < s.re → s ∈ strip → complexMGF id μ (-s) = F s) :
    ∀ σ : ℝ, 0 < σ → Integrable (fun u : ℝ => Real.exp (-σ * u)) μ := by
  let E := AbscissaSingularity.convergenceSet id μ
  have hupper {r t : ℝ} (hr : r ∈ E) (hrt : r ≤ t) : t ∈ E := by
    apply hr.mono' (by fun_prop)
    filter_upwards [hpos] with u hu
    simp only [Real.norm_eq_abs, Real.abs_exp]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hrt) hu)
  have hne : E.Nonempty := ⟨3 / 4, hc _ (by norm_num)⟩
  intro σ hσ
  by_contra hσbad
  have hbdd : BddBelow E := by
    refine ⟨σ, fun t ht => ?_⟩
    by_contra h
    exact hσbad (hupper ht (le_of_not_ge h))
  let c : ℝ := sInf E
  have hσc : σ ≤ c := le_csInf hne (fun t ht => by
    by_contra h
    exact hσbad (hupper ht (le_of_not_ge h)))
  have hcsmall : c ≤ 3 / 4 := csInf_le hbdd (hc _ (by norm_num))
  have hcpos : 0 < c := hσ.trans_le hσc
  have hcstrip : (c : ℂ) ∈ strip := by
    simp only [strip, mem_ofPred_eq, Complex.ofReal_re, Complex.ofReal_im, abs_zero]
    exact ⟨hcpos, by linarith, by norm_num⟩
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp strip_open (c : ℂ) hcstrip
  apply AbscissaSingularity.no_holomorphic_extension_at_abscissa
    (X := id) (by fun_prop) hpos hne hbdd hR
  refine ⟨hF.mono hball, ?_⟩
  intro z hz hzc
  apply (identity_on_convergence hc hF hi (hball hz) ?_).symm
  have hright : Iio (-c) ⊆ integrableExpSet id μ := by
    intro t ht
    change t < -c at ht
    obtain ⟨r, hr, hrt⟩ := exists_lt_of_csInf_lt hne (show c < -t by linarith)
    have hh := hupper hr hrt.le
    change Integrable (fun u : ℝ => Real.exp (t * u)) μ
    change Integrable (fun u : ℝ => Real.exp (-(-t) * u)) μ at hh
    simpa only [neg_neg] using hh
  apply mem_interior.mpr
  refine ⟨Iio (-c), hright, isOpen_Iio, ?_⟩
  change -z.re < -c
  exact neg_lt_neg hzc

lemma affine_mgf_holomorphic (a c : ℝ)
    (hpos : ∀ u : ℝ, 0 ≤ u → 0 ≤ a * u + c) :
    DifferentiableOn ℂ
      (fun s => complexMGF id (rayMeasure (fun u => a * u + c)) (-s)) strip := by
  intro s hs
  have hsi : (-s).re ∈ interior
      (integrableExpSet id (rayMeasure (fun u => a * u + c))) := by
    apply mem_interior.mpr
    refine ⟨Iio 0, ?_, isOpen_Iio, by simpa using neg_neg_of_pos hs.1⟩
    intro t ht
    apply (ray_integrable_iff (by fun_prop) hpos t).mpr
    simpa only [neg_neg] using affine_integrable a c (σ := -t) (neg_pos.mpr ht)
  exact ((analyticAt_complexMGF hsi).differentiableAt.comp s
    differentiable_neg.differentiableAt).differentiableWithinAt

lemma laplace_sub_const_mul {a f : ℝ → ℝ} (ha : Measurable a)
    (hf : Measurable f) (e : ℝ) {s : ℂ}
    (hia : IntegrableOn (fun u => a u * Real.exp (-s.re * u)) (Ici 0))
    (hif : IntegrableOn (fun u => f u * Real.exp (-s.re * u)) (Ici 0)) :
    laplace (fun u => a u - e * f u) s = laplace a s - (e : ℂ) * laplace f s := by
  unfold laplace
  rw [← integral_const_mul, ← integral_sub (laplace_integrable ha hia)
    ((laplace_integrable hf hif).const_mul (e : ℂ))]
  apply integral_congr_ae
  exact ae_of_all _ (fun u => by push_cast; ring)

set_option backward.isDefEq.respectTransparency false

def rightStrip : Set ℂ := {s | 0 < s.re ∧ s.re < 1}

lemma rightStrip_open : IsOpen rightStrip :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

lemma rightStrip_convex : Convex ℝ rightStrip :=
  (convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)

private lemma positive_laplace_holomorphic {q : ℝ → ℝ} (hq : Measurable q)
    (hpos : ∀ u : ℝ, 0 ≤ u → 0 ≤ q u)
    (hc : ∀ σ : ℝ, 0 < σ →
      IntegrableOn (fun u => q u * Real.exp (-σ * u)) (Ici 0)) :
    DifferentiableOn ℂ (laplace q) rightStrip := by
  have heq : laplace q = fun s => complexMGF id (rayMeasure q) (-s) := by
    funext s; exact (ray_mgf hq hpos s).symm
  rw [heq]
  intro s hs
  have hsi : (-s).re ∈ interior (integrableExpSet id (rayMeasure q)) := by
    apply mem_interior.mpr
    refine ⟨Iio 0, ?_, isOpen_Iio, by simpa using neg_neg_of_pos hs.1⟩
    intro t ht
    apply (ray_integrable_iff hq hpos t).mpr
    simpa using hc (-t) (neg_pos.mpr ht)
  exact ((analyticAt_complexMGF hsi).differentiableAt.comp s
    differentiable_neg.differentiableAt).differentiableWithinAt

lemma laplace_holomorphic {f : ℝ → ℝ} (hf : Measurable f)
    (hc : ∀ σ : ℝ, 0 < σ →
      IntegrableOn (fun u => f u * Real.exp (-σ * u)) (Ici 0)) :
    DifferentiableOn ℂ (laplace f) rightStrip := by
  let q : ℝ → ℝ := fun u => max (f u) 0
  let r : ℝ → ℝ := fun u => max (-f u) 0
  have hq : Measurable q := hf.max measurable_const
  have hr : Measurable r := hf.neg.max measurable_const
  have hqpos (u : ℝ) (_ : 0 ≤ u) : 0 ≤ q u := le_max_right _ _
  have hrpos (u : ℝ) (_ : 0 ≤ u) : 0 ≤ r u := le_max_right _ _
  have hqc (σ : ℝ) (hσ : 0 < σ) :
      IntegrableOn (fun u => q u * Real.exp (-σ * u)) (Ici 0) := by
    apply (hc σ hσ).norm.mono' (by fun_prop)
    filter_upwards [] with u
    simp only [Real.norm_eq_abs, abs_mul, Real.abs_exp, abs_of_nonneg (show 0 ≤ q u from le_max_right _ _)]
    exact mul_le_mul_of_nonneg_right (max_le (le_abs_self _) (abs_nonneg _))
      (Real.exp_nonneg _)
  have hrc (σ : ℝ) (hσ : 0 < σ) :
      IntegrableOn (fun u => r u * Real.exp (-σ * u)) (Ici 0) := by
    apply (hc σ hσ).norm.mono' (by fun_prop)
    filter_upwards [] with u
    simp only [Real.norm_eq_abs, abs_mul, Real.abs_exp, abs_of_nonneg (show 0 ≤ r u from le_max_right _ _)]
    exact mul_le_mul_of_nonneg_right (max_le (neg_le_abs _) (abs_nonneg _))
      (Real.exp_nonneg _)
  have heq : EqOn (laplace f) (fun s => laplace q s - laplace r s) rightStrip := by
    intro s hs
    have he : f = fun u => q u - 1 * r u := by
      funext u
      dsimp [q, r]
      by_cases hu : 0 ≤ f u
      · rw [max_eq_left hu, max_eq_right (neg_nonpos.mpr hu)]; ring
      · rw [max_eq_right (le_of_not_ge hu), max_eq_left (by linarith : 0 ≤ -f u)]; ring
    conv_lhs => rw [he]
    simpa using laplace_sub_const_mul hq hr 1 (hqc s.re hs.1) (hrc s.re hs.1)
  exact ((positive_laplace_holomorphic hq hqpos hqc).sub
    (positive_laplace_holomorphic hr hrpos hrc)).congr heq

private lemma pole_holomorphic (S : Spectrum) (j : S.index) :
    DifferentiableOn ℂ (poleTerm S j) rightStrip := by
  intro s hs
  have hm : s - (S.gamma j : ℂ) * Complex.I ≠ 0 := by
    intro h; have hh := congrArg Complex.re h
    simp at hh
    exact (ne_of_gt hs.1) hh
  have hp : s + (S.gamma j : ℂ) * Complex.I ≠ 0 := by
    intro h; have hh := congrArg Complex.re h
    simp at hh
    exact (ne_of_gt hs.1) hh
  have hid : DifferentiableAt ℂ (fun z : ℂ => z) s := differentiableAt_id
  exact ((((differentiableAt_const (1 : ℂ)).div
    (hid.sub (differentiableAt_const _)) hm).add
    ((differentiableAt_const (1 : ℂ)).div
      (hid.add (differentiableAt_const _)) hp)).const_mul
    (S.mult j : ℂ)).differentiableWithinAt

private lemma pole_comparison (S : Spectrum) (j : S.index) {s : ℂ}
    (hs : ‖s‖ ≤ 3 * S.gamma j / 4) :
    ‖poleTerm S j s‖ ≤ 32 * ‖s‖ * ((S.mult j : ℝ) / (S.gamma j) ^ 2) := by
  have hg := S.gamma_pos j
  have hn : ‖(S.gamma j : ℂ) * Complex.I‖ = S.gamma j := by
    simp [abs_of_pos hg]
  have hm := norm_sub_norm_le ((S.gamma j : ℂ) * Complex.I) s
  have hp := norm_sub_norm_le (-((S.gamma j : ℂ) * Complex.I)) s
  rw [hn, norm_sub_rev] at hm
  rw [norm_neg, hn, norm_sub_rev, sub_neg_eq_add] at hp
  have hl : S.gamma j / 4 ≤ ‖s - (S.gamma j : ℂ) * Complex.I‖ := by linarith
  have hr : S.gamma j / 4 ≤ ‖s + (S.gamma j : ℂ) * Complex.I‖ := by linarith
  have hm0 : s - (S.gamma j : ℂ) * Complex.I ≠ 0 := norm_pos_iff.mp (by linarith)
  have hp0 : s + (S.gamma j : ℂ) * Complex.I ≠ 0 := norm_pos_iff.mp (by linarith)
  have heq : poleTerm S j s = (S.mult j : ℂ) * (2 * s) /
      ((s - (S.gamma j : ℂ) * Complex.I) * (s + (S.gamma j : ℂ) * Complex.I)) := by
    unfold poleTerm; field_simp; ring
  rw [heq, norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_natCast]
  norm_num only [Complex.norm_ofNat]
  apply (div_le_iff₀ (mul_pos (norm_pos_iff.mpr hm0) (norm_pos_iff.mpr hp0))).mpr
  have hprod := mul_le_mul hl hr (by positivity) (norm_nonneg _)
  have he : (32 * ‖s‖ * ((S.mult j : ℝ) / (S.gamma j) ^ 2)) *
      ((S.gamma j / 4) * (S.gamma j / 4)) = (S.mult j : ℝ) * (2 * ‖s‖) := by
    field_simp; ring
  rw [← he]
  exact mul_le_mul_of_nonneg_left hprod (by positivity)

def cutComplement (S : Spectrum) (T : ℝ) :
    {j : S.index // j ∉ S.cut T} ≃ {j : S.index // T < S.gamma j} :=
  Equiv.subtypeEquivRight (fun j => by classical simp [Spectrum.cut])

lemma pole_tsum_summable (S : Spectrum) (hN : CountAsymptotic S) (s : ℂ) :
    Summable (fun j : S.index => poleTerm S j s) := by
  classical
  let T : ℝ := max 4 (2 * ‖s‖)
  obtain ⟨C, _, htail⟩ := inverse_square_tail S hN
  have ht : Summable (fun j : {j : S.index // T < S.gamma j} => poleTerm S j.val s) := by
    apply Summable.of_norm_bounded
      (((htail T (le_max_left _ _)).1).mul_left (32 * ‖s‖))
    intro j
    apply pole_comparison
    have hT := le_max_right 4 (2 * ‖s‖)
    have := j.property
    dsimp [T] at *
    nlinarith [norm_nonneg s]
  exact (S.cut T).summable_compl_iff.mp ((cutComplement S T).symm.summable_iff.mp ht)

lemma pole_tsum_holomorphic (S : Spectrum) (hN : CountAsymptotic S) :
    DifferentiableOn ℂ (fun s => ∑' j : S.index, poleTerm S j s) rightStrip := by
  classical
  intro s hs
  let M : ℝ := max 4 (|s.im| + 1)
  let U : Set ℂ := rightStrip ∩ {z : ℂ | |z.im| < M + 1}
  have hM : 4 ≤ M := le_max_left _ _
  have hU : IsOpen U := rightStrip_open.inter
    (isOpen_lt Complex.continuous_im.abs continuous_const)
  have hsU : s ∈ U := ⟨hs, by
    have := le_max_right 4 (|s.im| + 1)
    dsimp [M] at *; linarith⟩
  obtain ⟨C, _, htail⟩ := inverse_square_tail S hN
  have ht : DifferentiableOn ℂ
      (fun z => ∑' j : {j : S.index // 2 * M < S.gamma j}, poleTerm S j.val z) U := by
    apply Complex.differentiableOn_tsum_of_summable_norm
      (((htail (2 * M) (by linarith)).1).mul_left (32 * (M + 2)))
    · intro j; exact (pole_holomorphic S j.val).mono inter_subset_left
    · exact hU
    · intro j z hz
      change (0 < z.re ∧ z.re < 1) ∧ |z.im| < M + 1 at hz
      have hn : ‖z‖ ≤ M + 2 := by
        have := Complex.norm_le_abs_re_add_abs_im z
        rw [abs_of_pos hz.1.1] at this
        linarith [hz.1.2, hz.2]
      exact (pole_comparison S j.val (by linarith [j.property])).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hn (by norm_num)) (by positivity))
  have hf : DifferentiableOn ℂ
      (fun z => ∑ j ∈ S.cut (2 * M), poleTerm S j z) U :=
    DifferentiableOn.fun_sum (fun j _ => (pole_holomorphic S j).mono inter_subset_left)
  have he (z : ℂ) : (∑' j : S.index, poleTerm S j z) =
      (∑ j ∈ S.cut (2 * M), poleTerm S j z) +
        ∑' j : {j : S.index // 2 * M < S.gamma j}, poleTerm S j.val z := by
    have hh := (pole_tsum_summable S hN z).sum_add_tsum_subtype_compl (S.cut (2 * M))
    have heq : (∑' j : {j : S.index // j ∉ S.cut (2 * M)}, poleTerm S j.val z) =
        ∑' j : {j : S.index // 2 * M < S.gamma j}, poleTerm S j.val z :=
      (cutComplement S (2 * M)).tsum_eq (fun j => poleTerm S j.val z)
    rw [heq] at hh
    exact hh.symm
  have hd : DifferentiableAt ℂ (fun z => ∑' j : S.index, poleTerm S j z) s := by
    simp_rw [he]
    exact (hf.add ht).differentiableAt (hU.mem_nhds hsU)
  exact hd.differentiableWithinAt

end
end D5.S3.Analytic.Laplace.QuantitativeFejerBoundary
