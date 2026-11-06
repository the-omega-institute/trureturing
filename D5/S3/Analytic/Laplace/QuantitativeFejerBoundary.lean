/- GID: D5/S3/Analytic/Laplace/QuantitativeFejerBoundary
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/QuantitativeFejerBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Logarithmic one-sided envelopes give Laplace convergence and quantitative Fejer boundary formulas. -/

import D5.S3.Analytic.Laplace.PairedPoleRegularity
import D5.S3.Analytic.Fourier.AngularFejerKernel
import D5.S3.Analytic.Laplace.AbscissaSingularity
import Mathlib.Analysis.Analytic.Uniqueness

/-! Laplace convergence and a quantitative boundary formula under a one-sided logarithmic envelope. -/

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

private def rayMeasure (q : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ici 0)).withDensity (fun u => ENNReal.ofReal (q u))

private lemma ray_integrable_iff {q : ℝ → ℝ} (hq : Measurable q)
    (hpos : ∀ u : ℝ, 0 ≤ u → 0 ≤ q u) (t : ℝ) :
    Integrable (fun u : ℝ => Real.exp (t * u)) (rayMeasure q) ↔
      IntegrableOn (fun u => q u * Real.exp (t * u)) (Ici 0) := by
  rw [rayMeasure, integrable_withDensity_iff_integrable_smul'
    (hq.ennreal_ofReal) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
  simp [ENNReal.toReal_ofReal (hpos u hu), smul_eq_mul]

private lemma ray_mgf {q : ℝ → ℝ} (hq : Measurable q)
    (hpos : ∀ u : ℝ, 0 ≤ u → 0 ≤ q u) (s : ℂ) :
    complexMGF id (rayMeasure q) (-s) = laplace q s := by
  rw [complexMGF, rayMeasure, integral_withDensity_eq_integral_toReal_smul
    hq.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
  simp [ENNReal.toReal_ofReal (hpos u hu), neg_mul]

private lemma ray_nonneg (q : ℝ → ℝ) : ∀ᵐ u ∂rayMeasure q, 0 ≤ u :=
  (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem measurableSet_Ici)

private lemma exp_integrable {σ : ℝ} (hσ : 0 < σ) :
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

private lemma affine_integrable (a c : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun u : ℝ => (a * u + c) * Real.exp (-σ * u)) (Ici 0) := by
  have hu := integrable_pow_mul_exp_of_mem_interior_integrableExpSet (exp_interior hσ) 1
  simp only [id_eq, pow_one] at hu
  have heq : (fun u : ℝ => (a * u + c) * Real.exp (-σ * u)) =
      (fun u => a * (u * Real.exp (-σ * u)) + c * Real.exp (-σ * u)) := by
    funext u; ring
  rw [heq]
  exact (hu.const_mul a).add ((exp_integrable hσ).const_mul c)

private lemma laplace_integrable {q : ℝ → ℝ} (hq : Measurable q) {s : ℂ}
    (hi : IntegrableOn (fun u : ℝ => q u * Real.exp (-s.re * u)) (Ici 0)) :
    IntegrableOn (fun u : ℝ => (q u : ℂ) * Complex.exp (-s * (u : ℂ))) (Ici 0) := by
  apply (integrable_norm_iff (by fun_prop)).mp
  convert hi.norm using 1
  ext u
  simp [norm_mul, Complex.norm_exp, Complex.mul_re]


private def strip : Set ℂ := {s | 0 < s.re ∧ s.re < 1 ∧ |s.im| < 1}

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

private def continuation (S : Spectrum) (J : ℂ → ℂ) (s : ℂ) : ℂ :=
  -(1 / 2 : ℂ) * (∑ j ∈ S.cut 8, poleTerm S j s) + regularPart S J 4 s

private lemma continuation_holomorphic (S : Spectrum) (hN : CountAsymptotic S)
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

private lemma continuation_initial (S : Spectrum) (hN : CountAsymptotic S)
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

private lemma positive_convergence {μ : Measure ℝ}
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

private lemma affine_mgf_holomorphic (a c : ℝ)
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

private lemma laplace_sub_const_mul {a f : ℝ → ℝ} (ha : Measurable a)
    (hf : Measurable f) (e : ℝ) {s : ℂ}
    (hia : IntegrableOn (fun u => a u * Real.exp (-s.re * u)) (Ici 0))
    (hif : IntegrableOn (fun u => f u * Real.exp (-s.re * u)) (Ici 0)) :
    laplace (fun u => a u - e * f u) s = laplace a s - (e : ℂ) * laplace f s := by
  unfold laplace
  rw [← integral_const_mul, ← integral_sub (laplace_integrable ha hia)
    ((laplace_integrable hf hif).const_mul (e : ℂ))]
  apply integral_congr_ae
  exact ae_of_all _ (fun u => by push_cast; ring)

/-- A one-sided logarithmic envelope forces absolute convergence on the positive real ray. -/
theorem laplace_converges_of_log_envelope (S : Spectrum) (hN : CountAsymptotic S)
    {f : ℝ → ℝ} {k : ℕ} (D : PairedLaplaceData S f k) (hbound : HasLogEnvelope f) :
    ∀ σ : ℝ, 0 < σ → IntegrableOn (fun u => f u * Real.exp (-σ * u)) (Set.Ici 0) := by
  obtain ⟨e, a, C, he, ha, hC, henv⟩ := hbound
  let c : ℝ := a * Real.exp 1 + C
  let q : ℝ → ℝ := fun u => a * u + c
  let h : ℝ → ℝ := fun u => q u - e * f u
  have hq : Measurable q := by fun_prop
  have hh : Measurable h := hq.sub (measurable_const.mul D.measurable)
  have hqpos (u : ℝ) (hu : 0 ≤ u) : 0 ≤ q u := by dsimp [q, c]; positivity
  have hhpos (u : ℝ) (hu : 0 ≤ u) : 0 ≤ h u := by
    have hlog : ell u ≤ Real.exp 1 + u := Real.log_le_self (by positivity)
    have hle := mul_le_mul_of_nonneg_left hlog ha
    have henvu := henv u hu
    dsimp [h, q, c]
    linarith
  have hinit (σ : ℝ) (hσ : 1 / 2 < σ) :
      Integrable (fun u : ℝ => Real.exp (-σ * u)) (rayMeasure h) := by
    apply (ray_integrable_iff hh hhpos (-σ)).mpr
    have hia := affine_integrable a c (σ := σ) (by linarith)
    have hif := (D.initial_convergence σ hσ).const_mul e
    have heq : (fun u => h u * Real.exp (-σ * u)) =
        (fun u => q u * Real.exp (-σ * u) - e * (f u * Real.exp (-σ * u))) := by
      funext u; dsimp [h]; ring
    rw [heq]
    exact hia.sub hif
  let F : ℂ → ℂ := fun s => complexMGF id (rayMeasure q) (-s) -
    (e : ℂ) * continuation S D.J s
  have hF : DifferentiableOn ℂ F strip :=
    (affine_mgf_holomorphic a c hqpos).sub
      ((continuation_holomorphic S hN D).const_mul (e : ℂ))
  have hi (s : ℂ) (hs : 1 / 2 < s.re) (hstrip : s ∈ strip) :
      complexMGF id (rayMeasure h) (-s) = F s := by
    rw [ray_mgf hh hhpos, laplace_sub_const_mul hq D.measurable e
      (affine_integrable a c (by linarith)) (D.initial_convergence s.re hs),
      continuation_initial S hN D hs hstrip.2.1]
    dsimp only [F]
    rw [ray_mgf hq hqpos]
  have hconv := positive_convergence (ray_nonneg h) hinit hF hi
  intro σ hσ
  have hhi := (ray_integrable_iff hh hhpos (-σ)).mp (hconv σ hσ)
  have hia := affine_integrable a c hσ
  have he2 : e * e = 1 := by nlinarith [sq_abs e]
  have heq : (fun u => f u * Real.exp (-σ * u)) =
      (fun u => e * (q u * Real.exp (-σ * u) - h u * Real.exp (-σ * u))) := by
    funext u
    dsimp only [h]
    symm
    calc
      _ = (e * e) * (f u * Real.exp (-σ * u)) := by ring
      _ = _ := by rw [he2, one_mul]
  rw [heq]
  exact (hia.sub hhi).const_mul e


/-! ### Boundary formula: proved steps -/

set_option backward.isDefEq.respectTransparency false

private def rightStrip : Set ℂ := {s | 0 < s.re ∧ s.re < 1}

private lemma rightStrip_open : IsOpen rightStrip :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

private lemma rightStrip_convex : Convex ℝ rightStrip :=
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

private lemma laplace_holomorphic {f : ℝ → ℝ} (hf : Measurable f)
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

private def cutComplement (S : Spectrum) (T : ℝ) :
    {j : S.index // j ∉ S.cut T} ≃ {j : S.index // T < S.gamma j} :=
  Equiv.subtypeEquivRight (fun j => by classical simp [Spectrum.cut])

private lemma pole_tsum_summable (S : Spectrum) (hN : CountAsymptotic S) (s : ℂ) :
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

private lemma pole_tsum_holomorphic (S : Spectrum) (hN : CountAsymptotic S) :
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

private lemma laplace_eq_poles_full_strip (S : Spectrum) (hN : CountAsymptotic S)
    {f : ℝ → ℝ} {k : ℕ} (D : PairedLaplaceData S f k) (hbound : HasLogEnvelope f)
    {s : ℂ} (hs : s ∈ rightStrip) :
    laplace f s = -(1 / 2 : ℂ) * (∑' j : S.index, poleTerm S j s) + D.J s := by
  let F : ℂ → ℂ := fun z => -(1 / 2 : ℂ) * (∑' j : S.index, poleTerm S j z) + D.J z
  have hL := (laplace_holomorphic D.measurable
    (laplace_converges_of_log_envelope S hN D hbound)).analyticOnNhd rightStrip_open
  have hJ : DifferentiableOn ℂ D.J rightStrip := D.holomorphic.mono (by
    intro z hz; exact ⟨by linarith [hz.1, D.eta_pos], hz.2⟩)
  have hF : AnalyticOnNhd ℂ F rightStrip :=
    (((pole_tsum_holomorphic S hN).const_mul (-(1 / 2 : ℂ))).add hJ).analyticOnNhd
      rightStrip_open
  have hseed : ((3 / 4 : ℝ) : ℂ) ∈ rightStrip := by norm_num [rightStrip]
  have he : laplace f =ᶠ[𝓝 ((3 / 4 : ℝ) : ℂ)] F := by
    filter_upwards [rightStrip_open.mem_nhds hseed,
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (1 / 2 : ℝ) < (((3 / 4 : ℝ) : ℂ)).re by norm_num)] with z hz hzhalf
    exact D.identity z hzhalf hz.2
  exact hL.eqOn_of_preconnected_of_eventuallyEq hF rightStrip_convex.isPreconnected
    hseed he hs

private lemma laplace_eq_finite_poles_full_strip (S : Spectrum) (hN : CountAsymptotic S)
    {f : ℝ → ℝ} {k : ℕ} (D : PairedLaplaceData S f k) (hbound : HasLogEnvelope f)
    (M : ℝ) {s : ℂ} (hs : 0 < s.re ∧ s.re < 1) :
    laplace f s = -(1 / 2 : ℂ) * (∑ j ∈ S.cut (2 * M), poleTerm S j s) +
      regularPart S D.J M s := by
  classical
  have hsplit := (pole_tsum_summable S hN s).sum_add_tsum_subtype_compl (S.cut (2 * M))
  have heq : (∑' j : {j : S.index // j ∉ S.cut (2 * M)}, poleTerm S j.val s) =
      ∑' j : {j : S.index // 2 * M < S.gamma j}, poleTerm S j.val s :=
    (cutComplement S (2 * M)).tsum_eq (fun j => poleTerm S j.val s)
  rw [heq] at hsplit
  rw [laplace_eq_poles_full_strip S hN D hbound hs, ← hsplit, regularPart]
  ring


private lemma aft_cyclic (g : ℝ → ℝ) (t : ℝ) :
    aft g t = FourierTransform.fourier (fun v => (g v : ℂ)) (t / (2 * Real.pi)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with v
  simp only [smul_eq_mul]
  have he : (((-2 * Real.pi * v * (t / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I) =
      -Complex.I * (t : ℂ) * (v : ℂ) := by
    push_cast; field_simp
  rw [he, mul_comm]

private lemma angular_inversion {g w : ℝ → ℝ} (hg : Continuous g)
    (hgi : Integrable g) (hwi : Integrable w)
    (hft : ∀ t : ℝ, aft g t = (w t : ℂ)) (v : ℝ) :
    (g v : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t : ℝ, (w t : ℂ) * Complex.exp (Complex.I * (t : ℂ) * (v : ℂ)) := by
  have hp : 0 < 2 * Real.pi := by positivity
  have he (t : ℝ) : FourierTransform.fourier (fun u => (g u : ℂ)) t =
      (w (2 * Real.pi * t) : ℂ) := by
    have hh := hft (2 * Real.pi * t)
    rw [aft_cyclic] at hh
    simpa only [mul_div_cancel_left₀ _ hp.ne'] using hh
  have hfi : Integrable (FourierTransform.fourier (fun u => (g u : ℂ))) := by
    exact (hwi.ofReal.comp_mul_left' hp.ne').congr
      (Eventually.of_forall (fun t => (he t).symm))
  have hv := hgi.ofReal.fourierInv_fourier_eq hfi
    (Complex.continuous_ofReal.comp hg).continuousAt (v := v)
  rw [Real.fourierInv_eq'] at hv
  simp only [Real.inner_apply, smul_eq_mul] at hv
  have hphase (t : ℝ) :
      Complex.exp (((2 * Real.pi * (t * v) : ℝ) : ℂ) * Complex.I) *
        FourierTransform.fourier (fun u => (g u : ℂ)) t =
      (w (2 * Real.pi * t) : ℂ) *
        Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) * (v : ℂ)) := by
    rw [he, mul_comm]
    congr 2
    push_cast; ring
  simp_rw [hphase] at hv
  have hc := Measure.integral_comp_mul_left
    (fun t : ℝ => (w t : ℂ) * Complex.exp (Complex.I * (t : ℂ) * (v : ℂ)))
    (2 * Real.pi)
  rw [hc] at hv
  simpa only [abs_of_pos (inv_pos.mpr hp), Complex.real_smul, one_div] using hv.symm

private lemma phi_continuous (b : ℝ) : Continuous (phi b) := by
  unfold phi; fun_prop

private lemma phi_eq_zero {b t : ℝ} (hb : 0 < b) (ht : b ≤ |t|) : phi b t = 0 := by
  exact max_eq_left ((sub_nonpos.mpr ((le_div_iff₀ hb).mpr (by simpa using ht))))

private lemma admissible_laws {g w : ℝ → ℝ} {b M : ℝ} (hb : 0 < b)
    (had : Admissible g w b M) :
    Continuous g ∧ Continuous w ∧ (∀ v, 0 ≤ g v) ∧ Integrable g ∧ Integrable w ∧
      (∀ t, aft g t = (w t : ℂ)) ∧ (∀ t, M < |t| → w t = 0) := by
  have hK (b : ℝ) : Continuous (K b) := by
    unfold K
    exact continuous_const.mul ((Real.continuous_sinc.comp (by fun_prop)).pow 2)
  have hH (b U : ℝ) : Continuous (H b U) := by
    unfold H; exact (hK b).mul (continuous_const.sub (Real.continuous_cos.comp (by fun_prop)))
  have hphi : Integrable (phi b) := by
    apply (phi_continuous b).integrable_of_hasCompactSupport
    apply HasCompactSupport.intro (isCompact_Icc (a := -b) (b := b))
    intro t ht
    apply phi_eq_zero hb
    have hh : ¬ (-b ≤ t ∧ t ≤ b) := ht
    rw [← abs_le] at hh
    exact (lt_of_not_ge hh).le
  rcases had with ⟨rfl, rfl, hbM⟩ | ⟨U, hU, rfl, rfl, hUM⟩
  · obtain ⟨hpos, hgi, _, hft, _⟩ := fejer_law hb
    exact ⟨hK b, phi_continuous b, hpos, hgi, hphi, hft,
      fun t ht => phi_eq_zero hb (by linarith)⟩
  · obtain ⟨hpos, hgi, _, hft, _⟩ := notched_fejer_law hb hU
    have hw : Continuous (psi b U) := by
      unfold psi
      exact ((phi_continuous b).sub (((phi_continuous b).comp
        (continuous_id.sub continuous_const)).div_const 2)).sub
        (((phi_continuous b).comp (continuous_id.add continuous_const)).div_const 2)
    refine ⟨hH b U, hw, fun v => (hpos v).1, hgi, ?_, hft, ?_⟩
    · exact (hphi.sub ((hphi.comp_sub_right U).div_const 2)).sub
        ((hphi.comp_add_right U).div_const 2)
    · intro t ht
      have hu : 0 < U := by linarith
      have h1 : b ≤ |t| := by linarith
      have h2 : b ≤ |t - U| := by
        have := abs_sub_abs_le_abs_sub t U
        rw [abs_of_pos hu] at this
        linarith
      have h3 : b ≤ |t + U| := by
        have := abs_sub_abs_le_abs_sub t (-U)
        rw [abs_neg, abs_of_pos hu, sub_neg_eq_add] at this
        linarith
      simp [psi, phi_eq_zero hb h1, phi_eq_zero hb h2, phi_eq_zero hb h3]

private lemma damped_fubini {q g w : ℝ → ℝ}
    (hg : Continuous g) (hgi : Integrable g) (hwi : Integrable w)
    (hft : ∀ t : ℝ, aft g t = (w t : ℂ))
    (σ y : ℝ) (hi : IntegrableOn (fun u => q u * Real.exp (-σ * u)) (Ici 0)) :
    (∫ u in Ici 0, (q u : ℂ) * Complex.exp (-(σ : ℂ) * (u : ℂ)) * (g (y-u) : ℂ)) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, (w t : ℂ) * laplace q ((σ : ℂ) + (t : ℂ) * Complex.I) *
          Complex.exp (Complex.I * (t : ℂ) * (y : ℂ)) := by
  let F : ℝ → ℝ → ℂ := fun u t =>
    ((q u * Real.exp (-σ * u) : ℝ) : ℂ) * (w t : ℂ) *
      Complex.exp (Complex.I * (t : ℂ) * ((y - u : ℝ) : ℂ))
  have hFi : Integrable (Function.uncurry F)
      ((volume.restrict (Ici 0)).prod volume) := by
    apply (hi.ofReal.mul_prod hwi.ofReal).mul_bdd (c := 1)
    · have hc : Continuous (fun p : ℝ × ℝ =>
          Complex.exp (Complex.I * (p.2 : ℂ) * ((y-p.1 : ℝ) : ℂ))) := by fun_prop
      exact hc.aestronglyMeasurable
    · filter_upwards [] with p
      simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have he1 (u : ℝ) : (∫ t, F u t) =
      ((q u * Real.exp (-σ*u) : ℝ) : ℂ) *
        ∫ t : ℝ, (w t : ℂ) * Complex.exp (Complex.I * (t : ℂ) * ((y-u : ℝ) : ℂ)) := by
    simp only [F, mul_assoc, integral_const_mul]
  have he2 (t : ℝ) : (∫ u in Ici 0, F u t) =
      (w t : ℂ) * laplace q ((σ : ℂ) + (t : ℂ) * Complex.I) *
        Complex.exp (Complex.I * (t : ℂ) * (y : ℂ)) := by
    unfold laplace
    rw [← integral_const_mul, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with u
    dsimp [F]
    rw [Complex.ofReal_mul, Complex.ofReal_exp]
    have hex : Complex.exp (((-σ * u : ℝ) : ℂ)) *
        Complex.exp (Complex.I * (t : ℂ) * ((y-u : ℝ) : ℂ)) =
        Complex.exp (-((σ : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ)) *
          Complex.exp (Complex.I * (t : ℂ) * (y : ℂ)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1; push_cast; ring
    calc
      _ = (w t : ℂ) * (q u : ℂ) *
          (Complex.exp (((-σ * u : ℝ) : ℂ)) *
            Complex.exp (Complex.I * (t : ℂ) * ((y-u : ℝ) : ℂ))) := by ring
      _ = _ := by rw [hex]; ring
  calc
    _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ u in Ici 0, ∫ t, F u t := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with u
      rw [he1, angular_inversion hg hgi hwi hft (y-u)]
      rw [Complex.ofReal_mul, Complex.ofReal_exp]
      push_cast
      ring
    _ = _ := by rw [integral_integral_swap hFi]; simp_rw [he2]


private def polePolynomial (S : Spectrum) (M : ℝ) (u : ℝ) : ℝ :=
  -∑ j ∈ S.cut (2 * M), (S.mult j : ℝ) * Real.cos (S.gamma j * u)

private lemma polePolynomial_continuous (S : Spectrum) (M : ℝ) :
    Continuous (polePolynomial S M) := by
  classical
  unfold polePolynomial
  fun_prop

private lemma cosine_laplace (γ : ℝ) {s : ℂ} (hs : 0 < s.re) :
    laplace (fun u => Real.cos (γ * u)) s =
      (1 / 2 : ℂ) * (1 / (s - (γ : ℂ) * Complex.I) +
        1 / (s + (γ : ℂ) * Complex.I)) := by
  have hm : ((γ : ℂ) * Complex.I - s).re < 0 := by simp; linarith
  have hp : (-(γ : ℂ) * Complex.I - s).re < 0 := by simp; linarith
  have he (u : ℝ) : (Real.cos (γ*u) : ℂ) * Complex.exp (-s * (u : ℂ)) =
      (Complex.exp (((γ : ℂ) * Complex.I - s) * (u : ℂ)) +
        Complex.exp ((-(γ : ℂ) * Complex.I - s) * (u : ℂ))) / 2 := by
    rw [Complex.ofReal_cos]
    change ((Complex.exp _ + Complex.exp _) / 2) * _ = _
    have h1 : ((γ*u : ℝ) : ℂ) * Complex.I + -s * (u : ℂ) =
        ((γ : ℂ) * Complex.I - s) * (u : ℂ) := by push_cast; ring
    have h2 : -((γ*u : ℝ) : ℂ) * Complex.I + -s * (u : ℂ) =
        (-(γ : ℂ) * Complex.I - s) * (u : ℂ) := by push_cast; ring
    rw [add_div, add_mul, div_mul_eq_mul_div, div_mul_eq_mul_div,
      ← Complex.exp_add, ← Complex.exp_add, h1, h2, ← add_div]
  unfold laplace
  simp_rw [he]
  rw [integral_Ici_eq_integral_Ioi, integral_div,
    integral_add (integrableOn_exp_mul_complex_Ioi hm 0)
      (integrableOn_exp_mul_complex_Ioi hp 0),
    integral_exp_mul_complex_Ioi hm 0, integral_exp_mul_complex_Ioi hp 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have h1 : (γ : ℂ) * Complex.I - s = -(s - (γ : ℂ) * Complex.I) := by ring
  have h2 : -(γ : ℂ) * Complex.I - s = -(s + (γ : ℂ) * Complex.I) := by ring
  rw [h1, h2, neg_div_neg_eq, neg_div_neg_eq]
  ring

private lemma polePolynomial_convergence (S : Spectrum) (M : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun u => polePolynomial S M u * Real.exp (-σ*u)) (Ici 0) := by
  classical
  have hi (j : S.index) : IntegrableOn
      (fun u => (S.mult j : ℝ) * Real.cos (S.gamma j*u) * Real.exp (-σ*u)) (Ici 0) := by
    have hh : IntegrableOn (fun u => Real.exp (-σ*u) * Real.cos (S.gamma j*u)) (Ici 0) := by
      apply (exp_integrable hσ).mul_bdd (c := 1) (by fun_prop)
      filter_upwards [] with u
      exact Real.abs_cos_le_one _
    exact (hh.const_mul (S.mult j : ℝ)).congr (ae_of_all _ (fun u => by ring))
  have hh := (integrable_finsetSum (S.cut (2*M)) (fun j _ => hi j)).neg
  exact hh.congr (ae_of_all _ (fun u => by
    simp only [polePolynomial, neg_mul, Finset.sum_mul, Pi.neg_apply]))

private lemma polePolynomial_laplace (S : Spectrum) (M : ℝ) {s : ℂ} (hs : 0 < s.re) :
    laplace (polePolynomial S M) s =
      -(1 / 2 : ℂ) * ∑ j ∈ S.cut (2*M), poleTerm S j s := by
  classical
  have hi (j : S.index) : IntegrableOn
      (fun u => (S.mult j : ℂ) * (Real.cos (S.gamma j*u) : ℂ) *
        Complex.exp (-s * (u : ℂ))) (Ici 0) := by
    apply (laplace_integrable (q := fun u => (S.mult j : ℝ) * Real.cos (S.gamma j*u))
      (by fun_prop) ?_).congr
    · exact ae_of_all _ (fun u => by push_cast; rfl)
    have hh : IntegrableOn (fun u => Real.exp (-s.re*u) * Real.cos (S.gamma j*u)) (Ici 0) := by
      apply (exp_integrable hs).mul_bdd (c := 1) (by fun_prop)
      filter_upwards [] with u
      exact Real.abs_cos_le_one _
    exact (hh.const_mul (S.mult j : ℝ)).congr (ae_of_all _ (fun u => by ring))
  have he (u : ℝ) : (polePolynomial S M u : ℂ) * Complex.exp (-s * (u : ℂ)) =
      -∑ j ∈ S.cut (2*M), (S.mult j : ℂ) * (Real.cos (S.gamma j*u) : ℂ) *
        Complex.exp (-s * (u : ℂ)) := by
    simp [polePolynomial, Finset.sum_mul]
  unfold laplace
  simp_rw [he]
  rw [integral_neg, integral_finsetSum _ (fun j _ => hi j)]
  have hj (j : S.index) :
      (∫ u in Ici 0, (S.mult j : ℂ) * (Real.cos (S.gamma j*u) : ℂ) *
        Complex.exp (-s * (u : ℂ))) = (1 / 2 : ℂ) * poleTerm S j s := by
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    change (S.mult j : ℂ) * laplace (fun u => Real.cos (S.gamma j*u)) s = _
    rw [cosine_laplace _ hs]
    unfold poleTerm
    ring
  simp_rw [hj]
  rw [← Finset.mul_sum]
  ring

private lemma damped_boundary_identity (S : Spectrum) (hN : CountAsymptotic S)
    {f : ℝ → ℝ} {k : ℕ} (D : PairedLaplaceData S f k) (hbound : HasLogEnvelope f)
    {g w : ℝ → ℝ} {b M : ℝ} (hb : 0 < b) (had : Admissible g w b M)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) (y : ℝ) :
    (∫ u in Ici 0, ((f u - polePolynomial S M u : ℝ) : ℂ) *
      Complex.exp (-(σ : ℂ) * (u : ℂ)) * (g (y-u) : ℂ)) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t in Icc (-M) M, (w t : ℂ) *
          regularPart S D.J M ((σ : ℂ) + (t : ℂ) * Complex.I) *
            Complex.exp (Complex.I * (t : ℂ) * (y : ℂ)) := by
  obtain ⟨hg, hw, _, hgi, hwi, hft, hsupport⟩ := admissible_laws hb had
  have hp := polePolynomial_continuous S M
  have hc := laplace_converges_of_log_envelope S hN D hbound σ hσ
  have hi := hc.sub (polePolynomial_convergence S M hσ)
  have hres (t : ℝ) : laplace (fun u => f u - polePolynomial S M u)
      ((σ : ℂ) + (t : ℂ) * Complex.I) =
      regularPart S D.J M ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
    have hh := laplace_sub_const_mul D.measurable hp.measurable 1
      (s := (σ : ℂ) + (t : ℂ) * Complex.I)
      (by simpa [hre] using hc) (by simpa [hre] using polePolynomial_convergence S M hσ)
    simp only [one_mul, Complex.ofReal_one] at hh
    rw [hh, laplace_eq_finite_poles_full_strip S hN D hbound M
      (by simpa [hre] using And.intro hσ hσ1),
      polePolynomial_laplace S M (by simpa [hre] using hσ)]
    ring
  have hF := damped_fubini (q := fun u => f u - polePolynomial S M u)
    hg hgi hwi hft σ y
    (hi.congr (ae_of_all _ (fun u => by dsimp; ring)))
  refine hF.trans ?_
  simp_rw [hres]
  congr 1
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  have ht' : M < |t| := by
    by_contra hn
    exact ht (abs_le.mp (le_of_not_gt hn))
  simp [hsupport t ht']


private def damping (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1) / 2

private lemma damping_pos (n : ℕ) : 0 < damping n := by unfold damping; positivity

private lemma damping_lt_one (n : ℕ) : damping n < 1 := by
  unfold damping
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hh : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  linarith

private lemma damping_tendsto : Tendsto damping atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => 1 / ((n : ℝ)+1) / 2) atTop (𝓝 0)
  simpa only [zero_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const (2 : ℝ)

private lemma damping_antitone : Antitone damping := by
  intro n m hnm
  unfold damping
  exact div_le_div_of_nonneg_right
    (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1))
    (by norm_num)

private lemma damped_tendsto (u : ℝ) :
    Tendsto (fun n => Real.exp (-damping n * u)) atTop (𝓝 1) := by
  have ht : Tendsto (fun n => -damping n * u) atTop (𝓝 (0 : ℝ)) := by
    simpa only [neg_zero, zero_mul] using damping_tendsto.neg.mul_const u
  convert (Real.continuous_exp.tendsto 0).comp ht using 1
  · funext n; congr 1
  · simp

private lemma integrable_of_damped_tendsto {q : ℝ → ℝ} (hq : Measurable q)
    (hpos : ∀ u : ℝ, 0 ≤ u → 0 ≤ q u)
    (hi : ∀ n : ℕ, IntegrableOn (fun u => q u * Real.exp (-damping n*u)) (Ici 0))
    {L : ℝ} (hlim : Tendsto (fun n => ∫ u in Ici 0, q u * Real.exp (-damping n*u))
      atTop (𝓝 L)) : IntegrableOn q (Ici 0) := by
  let μ := volume.restrict (Ici (0 : ℝ))
  have hnn (n : ℕ) : 0 ≤ᵐ[μ] fun u => q u * Real.exp (-damping n*u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    exact mul_nonneg (hpos u hu) (Real.exp_nonneg _)
  have hmt : Tendsto (fun n => ∫⁻ u, ENNReal.ofReal (q u * Real.exp (-damping n*u)) ∂μ)
      atTop (𝓝 (∫⁻ u, ENNReal.ofReal (q u) ∂μ)) := by
    apply lintegral_tendsto_of_tendsto_of_monotone
    · intro n; exact (hi n).aemeasurable.ennreal_ofReal
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu n m hnm
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ (hpos u hu)
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (neg_le_neg (damping_antitone hnm)) hu
    · exact ae_of_all _ (fun u => ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (by simpa using (damped_tendsto u).const_mul (q u)))
  have hfin : (∫⁻ u, ENNReal.ofReal (q u) ∂μ) = ENNReal.ofReal L := by
    apply tendsto_nhds_unique hmt
    convert ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim using 1
    funext n
    exact (ofReal_integral_eq_lintegral_ofReal (hi n) (hnn n)).symm
  have hqnn : 0 ≤ᵐ[μ] q := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu using hpos u hu
  exact (lintegral_ofReal_ne_top_iff_integrable hq.aestronglyMeasurable hqnn).mp
    (by rw [hfin]; finiteness)

private lemma damped_integral_tendsto {q : ℝ → ℝ}
    (hi : IntegrableOn q (Ici 0)) :
    Tendsto (fun n => ∫ u in Ici 0, q u * Real.exp (-damping n*u)) atTop
      (𝓝 (∫ u in Ici 0, q u)) := by
  apply tendsto_integral_of_dominated_convergence (fun u => |q u|)
  · intro n; exact hi.aestronglyMeasurable.mul (by fun_prop)
  · exact hi.abs
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
    apply mul_le_of_le_one_right (abs_nonneg _)
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith [damping_pos n]) hu)
  · exact ae_of_all _ (fun u => by simpa using (damped_tendsto u).const_mul (q u))


private lemma admissible_log_integrable {g w : ℝ → ℝ} {b M y : ℝ}
    (hb : 0 < b) (hy : 1 ≤ y) (had : Admissible g w b M) :
    IntegrableOn (fun u => g (y-u) * ell u) (Ici 0) := by
  rcases had with ⟨rfl, rfl, _⟩ | ⟨U, hU, rfl, rfl, _⟩
  · obtain ⟨C, _, hlog⟩ := fejer_log_average
    by_cases hb1 : 1 ≤ b
    · exact (hlog b y hb1 hy).1
    have hbsmall : b < 1 := lt_of_not_ge hb1
    let Y : ℝ := b*y+1
    let F : ℝ → ℝ := (Ici (1 : ℝ)).indicator (fun x => K 1 (Y-x) * ell x)
    have hiF : Integrable F := by
      apply (integrable_indicator_iff measurableSet_Ici).mpr
      exact ((hlog 1 Y le_rfl (by dsimp [Y]; nlinarith)).1).mono_set
        (Ici_subset_Ici.mpr (by norm_num))
    have hscale := ((hiF.comp_add_right 1).comp_mul_left' hb.ne').integrableOn
      (s := Ici (0 : ℝ))
    have hscaled : IntegrableOn
        (fun u => b * (K 1 (b*(y-u)) * ell (b*u+1))) (Ici 0) := by
      apply (hscale.const_mul b).congr
      filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
      change 0 ≤ u at hu
      have hx : b*u+1 ∈ Ici (1 : ℝ) := by change 1 ≤ b*u+1; nlinarith
      dsimp only [F]
      rw [indicator_of_mem hx]
      congr 2
      dsimp [Y]
      ring
    have hgi := (fejer_law hb).2.1.comp_sub_left y
    have hk (v : ℝ) : K b v = b * K 1 (b*v) := by
      simp only [K, one_mul]
      ring
    have hmajor : IntegrableOn
        (fun u => b * (K 1 (b*(y-u)) * ell (b*u+1)) + |Real.log b| * K b (y-u))
        (Ici 0) := hscaled.add (hgi.integrableOn.const_mul _)
    apply hmajor.mono'
      (hgi.aestronglyMeasurable.mul (show Measurable ell by unfold ell; fun_prop).aestronglyMeasurable).restrict
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    change 0 ≤ u at hu
    have hell : 0 ≤ ell u := Real.log_nonneg (by
      have he := Real.add_one_le_exp (1 : ℝ)
      linarith)
    have hg0 := (fejer_law hb).1 (y-u)
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hg0 hell)]
    have harg : Real.exp 1 + u ≤ (Real.exp 1 + (b*u+1))/b := by
      apply (le_div_iff₀ hb).mpr
      nlinarith [Real.exp_pos (1 : ℝ)]
    have hh := Real.log_le_log (by positivity : 0 < Real.exp 1 + u) harg
    rw [Real.log_div (by positivity : Real.exp 1 + (b*u+1) ≠ 0) hb.ne'] at hh
    have henv : ell u ≤ ell (b*u+1) + |Real.log b| := by
      dsimp [ell]
      linarith [neg_le_abs (Real.log b)]
    calc
      _ ≤ K b (y-u) * (ell (b*u+1) + |Real.log b|) :=
        mul_le_mul_of_nonneg_left henv hg0
      _ = _ := by rw [hk]; ring
  · obtain ⟨C, _, hlog⟩ := notched_log_average hb
    exact (hlog U y hU hy).1

private lemma regular_integral_tendsto (S : Spectrum) (hN : CountAsymptotic S)
    {f : ℝ → ℝ} {k : ℕ} (D : PairedLaplaceData S f k)
    {w : ℝ → ℝ} (hw : Continuous w) {M : ℝ} (hM : 4 ≤ M) (y : ℝ) :
    Tendsto (fun n => ∫ t in Icc (-M) M, (w t : ℂ) *
      regularPart S D.J M ((damping n : ℂ) + (t : ℂ) * Complex.I) *
        Complex.exp (Complex.I * (t : ℂ) * (y : ℂ))) atTop
      (𝓝 (∫ t in Icc (-M) M, (w t : ℂ) *
        regularPart S D.J M ((t : ℂ) * Complex.I) *
          Complex.exp (Complex.I * (t : ℂ) * (y : ℂ)))) := by
  let R : Set ℂ := {s | |s.re| < D.eta ∧ |s.im| < M+1}
  have hR : IsOpen R := (isOpen_lt Complex.continuous_re.abs continuous_const).inter
    (isOpen_lt Complex.continuous_im.abs continuous_const)
  have hG := regularPart_differentiableOn S hN D hM
  let P : Set (ℝ × ℝ) := Icc (0 : ℝ) (D.eta/2) ×ˢ Icc (-M) M
  have hPc : IsCompact P := isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => regularPart S D.J M ((p.1 : ℂ) + (p.2 : ℂ)*Complex.I)) P := by
    apply hG.continuousOn.comp (by fun_prop)
    intro p hp
    change (0 ≤ p.1 ∧ p.1 ≤ D.eta/2) ∧ (-M ≤ p.2 ∧ p.2 ≤ M) at hp
    change |((p.1 : ℂ) + (p.2 : ℂ)*Complex.I).re| < D.eta ∧
      |((p.1 : ℂ) + (p.2 : ℂ)*Complex.I).im| < M+1
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, sub_zero, add_zero,
      Complex.add_im, Complex.mul_im, mul_one, zero_add, abs_of_nonneg hp.1.1]
    exact ⟨by linarith [hp.1.2, D.eta_pos], by
      have := abs_le.mpr hp.2
      linarith⟩
  obtain ⟨B, hB⟩ := hPc.exists_bound_of_continuousOn hcont
  have hevent : ∀ᶠ n : ℕ in atTop, damping n ≤ D.eta/2 :=
    (damping_tendsto.eventually (gt_mem_nhds (show (0 : ℝ) < D.eta/2 by linarith [D.eta_pos]))).mono
      (fun _ hn => hn.le)
  apply tendsto_integral_filter_of_dominated_convergence (fun t => |w t| * B)
  · filter_upwards [hevent] with n hn
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Icc
    apply (((Complex.continuous_ofReal.comp hw).continuousOn).mul ?_).mul (by fun_prop)
    apply hG.continuousOn.comp (by fun_prop)
    intro t ht
    have ht' := abs_le.mpr ht
    change |((damping n : ℂ) + (t : ℂ)*Complex.I).re| < D.eta ∧
      |((damping n : ℂ) + (t : ℂ)*Complex.I).im| < M+1
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, sub_zero, add_zero,
      Complex.add_im, Complex.mul_im, mul_one, zero_add,
      abs_of_pos (damping_pos n)]
    exact ⟨by linarith [D.eta_pos], by linarith⟩
  · filter_upwards [hevent] with n hn
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hh := hB (damping n,t) ⟨⟨(damping_pos n).le, hn⟩, ht⟩
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, mul_zero, sub_self,
      Real.exp_zero, mul_one]
    exact mul_le_mul_of_nonneg_left hh (abs_nonneg _)
  · exact ((hw.abs.continuousOn.integrableOn_Icc).mul_const B)
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hz : (t : ℂ)*Complex.I ∈ R := by
      have ht' := abs_le.mpr ht
      simp only [R, mem_setOf_eq, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, mul_zero, sub_self, abs_zero,
        Complex.mul_im, mul_one, zero_add, add_zero]
      exact ⟨D.eta_pos, by linarith⟩
    have hinput : Tendsto (fun n => (damping n : ℂ) + (t : ℂ)*Complex.I)
        atTop (𝓝 ((t : ℂ)*Complex.I)) := by
      simpa only [Complex.ofReal_zero, zero_add] using
        damping_tendsto.ofReal.add_const ((t : ℂ)*Complex.I)
    have hlim := (hG.continuousOn.continuousAt (hR.mem_nhds hz)).tendsto.comp hinput
    simpa using (hlim.const_mul (w t : ℂ)).mul_const
      (Complex.exp (Complex.I * (t : ℂ) * (y : ℂ)))


private lemma admissible_bounded {g w : ℝ → ℝ} {b M : ℝ} (hb : 0 < b)
    (had : Admissible g w b M) (v : ℝ) : |g v| ≤ b / Real.pi := by
  have hK : K b v ≤ b / (2*Real.pi) := by
    have hs := Real.abs_sinc_le_one (b*v/2)
    have hsq : Real.sinc (b*v/2)^2 ≤ 1 := by
      obtain ⟨hl, hr⟩ := abs_le.mp hs
      nlinarith
    unfold K
    nlinarith [div_pos hb (mul_pos (by norm_num : (0 : ℝ)<2) Real.pi_pos)]
  rcases had with ⟨rfl, _, _⟩ | ⟨U, hU, rfl, _, _⟩
  · rw [abs_of_nonneg ((fejer_law hb).1 v)]
    have hpos : 0 ≤ b / (2*Real.pi) := by positivity
    have he : b / Real.pi = 2 * (b / (2*Real.pi)) := by ring
    rw [he]; linarith
  · obtain ⟨hpos, hle⟩ := (notched_fejer_law hb hU).1 v
    rw [abs_of_nonneg hpos]
    have he : b / Real.pi = 2 * (b / (2*Real.pi)) := by ring
    rw [he]
    linarith

private lemma polePolynomial_bound (S : Spectrum) (M u : ℝ) :
    |polePolynomial S M u| ≤ (S.N (2*M) : ℝ) := by
  classical
  rw [polePolynomial, abs_neg]
  calc
    _ ≤ ∑ j ∈ S.cut (2*M), |(S.mult j : ℝ) * Real.cos (S.gamma j*u)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ S.cut (2*M), (S.mult j : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) (Real.abs_cos_le_one _)
    _ = _ := by simp [Spectrum.N]

private lemma damped_cast_integral (q g : ℝ → ℝ) (σ y : ℝ) :
    (∫ u in Ici 0, (q u : ℂ) * Complex.exp (-(σ : ℂ)*(u : ℂ)) * (g (y-u) : ℂ)) =
      ((∫ u in Ici 0, q u * Real.exp (-σ*u) * g (y-u) : ℝ) : ℂ) := by
  calc
    _ = ∫ u in Ici 0, ((q u * Real.exp (-σ*u) * g (y-u) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with u
      push_cast
      rfl
    _ = _ := integral_ofReal

private lemma integrable_of_one_sided_damping {q a : ℝ → ℝ}
    (hq : Measurable q) (ha : Measurable a) (hia : IntegrableOn a (Ici 0))
    {e : ℝ} (he : |e| = 1) (henv : ∀ u : ℝ, 0 ≤ u → e*q u ≤ a u)
    (hi : ∀ n : ℕ, IntegrableOn (fun u => q u * Real.exp (-damping n*u)) (Ici 0))
    {L : ℝ} (hlim : Tendsto (fun n => ∫ u in Ici 0, q u * Real.exp (-damping n*u))
      atTop (𝓝 L)) : IntegrableOn q (Ici 0) := by
  let h : ℝ → ℝ := fun u => a u - e*q u
  have hh : Measurable h := ha.sub (measurable_const.mul hq)
  have hia' (n : ℕ) : IntegrableOn (fun u => a u * Real.exp (-damping n*u)) (Ici 0) := by
    apply hia.mul_bdd (c := 1) (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    rw [Real.norm_eq_abs, Real.abs_exp]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (by linarith [damping_pos n]) hu)
  have hhi (n : ℕ) : IntegrableOn (fun u => h u * Real.exp (-damping n*u)) (Ici 0) :=
    ((hia' n).sub ((hi n).const_mul e)).congr (ae_of_all _ (fun u => by dsimp [h]; ring))
  have heq (n : ℕ) : (∫ u in Ici 0, h u * Real.exp (-damping n*u)) =
      (∫ u in Ici 0, a u * Real.exp (-damping n*u)) -
        e*(∫ u in Ici 0, q u * Real.exp (-damping n*u)) := by
    rw [← integral_const_mul, ← integral_sub (hia' n) ((hi n).const_mul e)]
    apply integral_congr_ae
    exact ae_of_all _ (fun u => by dsimp [h]; ring)
  have hlimh : Tendsto (fun n => ∫ u in Ici 0, h u * Real.exp (-damping n*u)) atTop
      (𝓝 ((∫ u in Ici 0, a u) - e*L)) := by
    simp_rw [heq]
    exact (damped_integral_tendsto hia).sub (hlim.const_mul e)
  have hhi0 : IntegrableOn h (Ici 0) := integrable_of_damped_tendsto hh
    (fun u hu => sub_nonneg.mpr (henv u hu)) hhi hlimh
  have he2 : e*e=1 := by nlinarith [sq_abs e]
  exact ((hia.sub hhi0).const_mul e).congr (ae_of_all _ (fun u => by
    dsimp [h]
    calc
      e*(a u - (a u-e*q u)) = (e*e)*q u := by ring
      _ = q u := by rw [he2, one_mul]))


private lemma cosine_convolution {g w : ℝ → ℝ} (hgi : Integrable g)
    (hft : ∀ t : ℝ, aft g t = (w t : ℂ)) (γ y : ℝ) :
    (∫ u : ℝ, Real.cos (γ*u)*g (y-u)) = w γ * Real.cos (γ*y) := by
  let E : ℝ → ℂ := fun u => (g (y-u) : ℂ)*Complex.exp (Complex.I*(γ : ℂ)*(u : ℂ))
  have hi : Integrable E := by
    apply (hgi.comp_sub_left y).ofReal.mul_bdd (c := 1) (by fun_prop)
    filter_upwards [] with u
    simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have he (u : ℝ) : E u = Complex.exp (Complex.I*(γ : ℂ)*(y : ℂ)) *
      ((g (y-u) : ℂ)*Complex.exp (-Complex.I*(γ : ℂ)*((y-u : ℝ) : ℂ))) := by
    dsimp [E]
    rw [mul_left_comm, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast; ring
  have hf : (∫ u, E u) = Complex.exp (Complex.I*(γ : ℂ)*(y : ℂ)) * (w γ : ℂ) := by
    simp_rw [he]
    rw [integral_const_mul]
    congr 1
    calc
      _ = ∫ u : ℝ, (g u : ℂ)*Complex.exp (-Complex.I*(γ : ℂ)*(u : ℂ)) :=
        integral_sub_left_eq_self
          (fun u : ℝ => (g u : ℂ)*Complex.exp (-Complex.I*(γ : ℂ)*(u : ℂ))) volume y
      _ = _ := hft γ
  have hre (u : ℝ) : (E u).re = Real.cos (γ*u)*g (y-u) := by
    dsimp [E]
    have hex : Complex.I*(γ : ℂ)*(u : ℂ) = ((γ*u : ℝ) : ℂ)*Complex.I := by
      push_cast; ring
    rw [hex]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero, Complex.exp_ofReal_mul_I_re]
    ring
  have hex : Complex.I*(γ : ℂ)*(y : ℂ) = ((γ*y : ℝ) : ℂ)*Complex.I := by
    push_cast; ring
  calc
    _ = ∫ u : ℝ, (E u).re := by simp_rw [hre]
    _ = (∫ u : ℝ, E u).re := integral_re hi
    _ = _ := by
      rw [hf, hex]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero, Complex.exp_ofReal_mul_I_re]
      ring

private lemma polePolynomial_convolution (S : Spectrum) (M : ℝ)
    {g w : ℝ → ℝ} (hgi : Integrable g) (hft : ∀ t : ℝ, aft g t = (w t : ℂ))
    (y : ℝ) :
    (∫ u : ℝ, polePolynomial S M u*g (y-u)) =
      -∑ j ∈ S.cut (2*M), (S.mult j : ℝ)*w (S.gamma j)*Real.cos (S.gamma j*y) := by
  classical
  have hi (j : S.index) : Integrable
      (fun u => (S.mult j : ℝ)*Real.cos (S.gamma j*u)*g (y-u)) := by
    have hh := (hgi.comp_sub_left y).bdd_mul (c := 1) (by fun_prop)
      (ae_of_all _ (fun u => Real.abs_cos_le_one (S.gamma j*u)))
    exact (hh.const_mul (S.mult j : ℝ)).congr (ae_of_all _ (fun u => by ring))
  simp only [polePolynomial, neg_mul, Finset.sum_mul]
  rw [integral_neg, integral_finsetSum _ (fun j _ => hi j)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [mul_assoc]
  rw [integral_const_mul, cosine_convolution hgi hft]

private lemma kernel_negative_ray {g : ℝ → ℝ} (y : ℝ) :
    (∫ u in Iio (0 : ℝ), g (y-u)) = ∫ v in Ici y, g v := by
  rw [integral_Ici_eq_integral_Ioi]
  have he (u : ℝ) : (Iio (0 : ℝ)).indicator (fun u => g (y-u)) u =
      (Ioi y).indicator g (y-u) := by
    by_cases hu : u < 0
    · rw [indicator_of_mem (show u ∈ Iio (0 : ℝ) from hu),
        indicator_of_mem (show y-u ∈ Ioi y by change y < y-u; linarith)]
    · rw [indicator_of_notMem (show u ∉ Iio (0 : ℝ) from hu),
        indicator_of_notMem (show y-u ∉ Ioi y by change ¬y < y-u; linarith)]
  rw [← integral_indicator measurableSet_Iio, ← integral_indicator measurableSet_Ioi]
  simp_rw [he]
  exact integral_sub_left_eq_self _ volume y

private lemma polePolynomial_truncation_error (S : Spectrum) {g w : ℝ → ℝ}
    {b M y : ℝ} (hb : 0 < b) (hy : 0 < y) (had : Admissible g w b M) :
    |(∫ u in Ici 0, polePolynomial S M u*g (y-u)) +
      ∑ j ∈ S.cut (2*M), (S.mult j : ℝ)*w (S.gamma j)*Real.cos (S.gamma j*y)|
      ≤ (S.N (2*M) : ℝ) * (4 / (Real.pi*b*y)) := by
  obtain ⟨_, _, hgpos, hgi, _, hft, _⟩ := admissible_laws hb had
  have hi : Integrable (fun u => polePolynomial S M u*g (y-u)) := by
    exact (hgi.comp_sub_left y).bdd_mul
      (polePolynomial_continuous S M).aestronglyMeasurable
      (ae_of_all _ (fun u => polePolynomial_bound S M u))
  have htail : (∫ v in Ici y, g v) ≤ 4 / (Real.pi*b*y) := by
    rcases had with ⟨rfl, _, _⟩ | ⟨U, hU, rfl, _, _⟩
    · exact ((fejer_law hb).2.2.2.2 y hy).trans
        (div_le_div_of_nonneg_right (by norm_num) (by positivity))
    · exact (notched_fejer_law hb hU).2.2.2.2 y hy
  have hs := intervalIntegral.integral_Iio_add_Ici (b := (0 : ℝ)) hi.integrableOn hi.integrableOn
  rw [polePolynomial_convolution S M hgi hft y] at hs
  have he : (∫ u in Ici 0, polePolynomial S M u*g (y-u)) +
      ∑ j ∈ S.cut (2*M), (S.mult j : ℝ)*w (S.gamma j)*Real.cos (S.gamma j*y) =
      -(∫ u in Iio 0, polePolynomial S M u*g (y-u)) := by linarith
  rw [he, abs_neg]
  calc
    _ ≤ ∫ u in Iio 0, |polePolynomial S M u*g (y-u)| :=
      by simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (fun u => polePolynomial S M u*g (y-u))
          (μ := volume.restrict (Iio 0)))
    _ ≤ ∫ u in Iio 0, (S.N (2*M) : ℝ)*g (y-u) := by
      apply integral_mono_ae hi.integrableOn.abs
        ((hgi.comp_sub_left y).integrableOn.const_mul _)
      exact ae_of_all _ (fun u => by
        dsimp only
        rw [abs_mul, abs_of_nonneg (hgpos _)]
        exact mul_le_mul_of_nonneg_right (polePolynomial_bound S M u) (hgpos _))
    _ = (S.N (2*M) : ℝ)*(∫ v in Ici y, g v) := by
      rw [integral_const_mul, kernel_negative_ray]
    _ ≤ _ := mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg _)

private lemma boundary_integrable_and_identity (S : Spectrum) (hN : CountAsymptotic S)
    {f : ℝ → ℝ} {k : ℕ} (D : PairedLaplaceData S f k) (hbound : HasLogEnvelope f)
    {g w : ℝ → ℝ} {b M y : ℝ} (hb : 0 < b) (hM : 4 ≤ M) (hy : 1 ≤ y)
    (had : Admissible g w b M) :
    IntegrableOn (fun u => f u*g (y-u)) (Ici 0) ∧
      ((∫ u in Ici 0, (f u-polePolynomial S M u)*g (y-u) : ℝ) : ℂ) =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t in Icc (-M) M, (w t : ℂ) * regularPart S D.J M ((t : ℂ)*Complex.I) *
            Complex.exp (Complex.I * (t : ℂ) * (y : ℂ)) := by
  obtain ⟨hg, hw, hgpos, hgi, _, _, _⟩ := admissible_laws hb had
  let q : ℝ → ℝ := fun u => f u*g (y-u)
  let p : ℝ → ℝ := fun u => polePolynomial S M u*g (y-u)
  let R : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t in Icc (-M) M, (w t : ℂ) * regularPart S D.J M ((t : ℂ)*Complex.I) *
      Complex.exp (Complex.I * (t : ℂ) * (y : ℂ))
  have hq : Measurable q := D.measurable.mul (hg.comp (by fun_prop)).measurable
  have hpi : IntegrableOn p (Ici 0) := by
    apply (hgi.comp_sub_left y).integrableOn.bdd_mul
      ((polePolynomial_continuous S M).aestronglyMeasurable) (c := (S.N (2*M) : ℝ))
    exact ae_of_all _ (fun u => polePolynomial_bound S M u)
  have hqi (n : ℕ) : IntegrableOn (fun u => q u*Real.exp (-damping n*u)) (Ici 0) := by
    have hconv := laplace_converges_of_log_envelope S hN D hbound (damping n) (damping_pos n)
    have hh := hconv.mul_bdd (c := b/Real.pi)
      ((hg.comp (by fun_prop)).aestronglyMeasurable)
      (ae_of_all _ (fun u => admissible_bounded hb had (y-u)))
    exact hh.congr (ae_of_all _ (fun u => by dsimp [q]; ring))
  have hpdi (n : ℕ) : IntegrableOn (fun u => p u*Real.exp (-damping n*u)) (Ici 0) := by
    apply hpi.mul_bdd (c := 1) (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    rw [Real.norm_eq_abs, Real.abs_exp]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (by linarith [damping_pos n]) hu)
  have hid (n : ℕ) :
      ((∫ u in Ici 0, (q u-p u)*Real.exp (-damping n*u) : ℝ) : ℂ) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t in Icc (-M) M, (w t : ℂ) *
          regularPart S D.J M ((damping n : ℂ)+(t : ℂ)*Complex.I) *
            Complex.exp (Complex.I * (t : ℂ) * (y : ℂ)) := by
    rw [← damped_boundary_identity S hN D hbound hb had (damping_pos n) (damping_lt_one n) y,
      damped_cast_integral]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ (fun u => by dsimp [q,p]; ring)
  have hrlim : Tendsto (fun n => ∫ u in Ici 0, (q u-p u)*Real.exp (-damping n*u))
      atTop (𝓝 R.re) := by
    have ht := (regular_integral_tendsto S hN D hw hM y).const_mul
      (((1 / (2 * Real.pi) : ℝ) : ℂ))
    have ht' := Complex.continuous_re.tendsto R |>.comp ht
    simpa only [Function.comp_def, ← hid, Complex.ofReal_re] using ht'
  have hlim : Tendsto (fun n => ∫ u in Ici 0, q u*Real.exp (-damping n*u))
      atTop (𝓝 (R.re + ∫ u in Ici 0, p u)) := by
    have heq (n : ℕ) : (∫ u in Ici 0, q u*Real.exp (-damping n*u)) =
        (∫ u in Ici 0, (q u-p u)*Real.exp (-damping n*u)) +
          (∫ u in Ici 0, p u*Real.exp (-damping n*u)) := by
      rw [← integral_add
        (((hqi n).sub (hpdi n)).congr (ae_of_all _ (fun u => by dsimp only [Pi.sub_apply]; ring))) (hpdi n)]
      apply integral_congr_ae
      exact ae_of_all _ (fun u => by ring)
    simp_rw [heq]
    exact hrlim.add (damped_integral_tendsto hpi)
  obtain ⟨e, κ, C, he, _, _, henv⟩ := hbound
  let a : ℝ → ℝ := fun u => (κ*ell u+C)*g (y-u)
  have ha : Measurable a := by
    exact (((show Measurable ell by unfold ell; fun_prop).const_mul κ).add_const C).mul
      (hg.comp (by fun_prop)).measurable
  have hai : IntegrableOn a (Ici 0) := by
    exact (((admissible_log_integrable hb hy had).const_mul κ).add
      ((hgi.comp_sub_left y).integrableOn.const_mul C)).congr
        (ae_of_all _ (fun u => by dsimp [a]; ring))
  have hqi0 : IntegrableOn q (Ici 0) := integrable_of_one_sided_damping hq ha hai he
    (fun u hu => by
      dsimp [q,a]
      have hh := mul_le_mul_of_nonneg_right (henv u hu) (hgpos (y-u))
      nlinarith) hqi hlim
  refine ⟨hqi0, ?_⟩
  have hres : IntegrableOn (fun u => q u-p u) (Ici 0) := hqi0.sub hpi
  have hl := (damped_integral_tendsto hres).ofReal
  have hr := (regular_integral_tendsto S hN D hw hM y).const_mul
    (((1 / (2 * Real.pi) : ℝ) : ℂ))
  have heql := tendsto_nhds_unique hl (hr.congr' (Eventually.of_forall (fun n => (hid n).symm)))
  convert heql using 1
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun u => by dsimp [q,p]; ring)


private lemma oscillatory_interval_bound {a c y B C : ℝ} {F F' : ℝ → ℂ}
    (hac : a ≤ c) (hy : 0 < y)
    (hF' : ContinuousOn F' (uIcc a c))
    (hder : ∀ t ∈ uIcc a c, HasDerivAt F (F' t) t)
    (hFa : ‖F a‖ ≤ B) (hFc : ‖F c‖ ≤ B)
    (hbound : ∀ t ∈ uIcc a c, ‖F' t‖ ≤ C) :
    ‖∫ t in a..c, F t * Complex.exp ((t : ℂ)*(y : ℂ)*Complex.I)‖
      ≤ (2*B+C*(c-a))/y := by
  let E : ℝ → ℂ := fun t => Complex.exp ((t : ℂ)*(y : ℂ)*Complex.I)
  have hE (t : ℝ) : HasDerivAt E (E t * ((y : ℂ)*Complex.I)) t := by
    simpa [E, mul_assoc] using
      (((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (y : ℂ)).mul_const Complex.I).cexp
  have hcE : Continuous E := by dsimp [E]; fun_prop
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hder (fun t _ => hE t) hF'.intervalIntegrable
    ((hcE.mul continuous_const).intervalIntegrable a c)
  have he : (∫ t in a..c, F t * E t) * ((y : ℂ)*Complex.I) =
      F c * E c - F a * E a - ∫ t in a..c, F' t * E t := by
    rw [← intervalIntegral.integral_mul_const]
    simpa only [mul_assoc] using hi
  have hnE (t : ℝ) : ‖E t‖ = 1 := by
    simpa [E, ← Complex.ofReal_mul] using Complex.norm_exp_ofReal_mul_I (t*y)
  have hInt : ‖∫ t in a..c, F' t * E t‖ ≤ C*(c-a) := by
    simpa [abs_of_nonneg (sub_nonneg.mpr hac)] using
      intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun t => F' t * E t) (a := a) (b := c)
        (fun t ht => by rw [norm_mul, hnE, mul_one]; exact hbound t (uIoc_subset_uIcc ht))
  have hb : ‖∫ t in a..c, F t * E t‖ * y ≤ 2*B+C*(c-a) := by
    have hh := norm_sub_le (F c*E c-F a*E a) (∫ t in a..c, F' t*E t)
    rw [← he, norm_mul] at hh
    have hyN : ‖(y : ℂ)*Complex.I‖ = y := by simp [abs_of_pos hy]
    rw [hyN] at hh
    have hh2 := norm_sub_le (F c*E c) (F a*E a)
    simp only [norm_mul, hnE, mul_one] at hh2
    linarith
  exact (le_div_iff₀ hy).mpr hb

private lemma affine_oscillatory_bound {a c α β b y B : ℝ} {Q Q' : ℝ → ℂ}
    (hb : 0 < b) (hy : 0 < y) (hlen : c-a=b) (hB : 0 ≤ B)
    (hQ' : ContinuousOn Q' (uIcc a c))
    (hder : ∀ t ∈ uIcc a c, HasDerivAt Q (Q' t) t)
    (hQ : ∀ t ∈ uIcc a c, ‖Q t‖+‖Q' t‖ ≤ B)
    (hα : |α| ≤ 1/b) (hA : ∀ t ∈ uIcc a c, |α*t+β| ≤ 1) :
    ‖∫ t in a..c, ((α*t+β : ℝ) : ℂ)*Q t*
      Complex.exp ((t : ℂ)*(y : ℂ)*Complex.I)‖ ≤ (3+b)*B/y := by
  have hac : a ≤ c := by linarith
  have hcQ : ContinuousOn Q (uIcc a c) :=
    fun t ht => (hder t ht).continuousAt.continuousWithinAt
  let F : ℝ → ℂ := fun t => ((α*t+β : ℝ) : ℂ)*Q t
  let F' : ℝ → ℂ := fun t => (α : ℂ)*Q t+((α*t+β : ℝ) : ℂ)*Q' t
  have hcF' : ContinuousOn F' (uIcc a c) := by
    exact (continuous_const.continuousOn.mul hcQ).add
      ((by fun_prop : Continuous (fun t : ℝ => ((α*t+β : ℝ) : ℂ))).continuousOn.mul hQ')
  have hdF (t : ℝ) (ht : t ∈ uIcc a c) : HasDerivAt F (F' t) t := by
    have ha : HasDerivAt (fun t : ℝ => ((α*t+β : ℝ) : ℂ)) (α : ℂ) t := by
      simpa using (((hasDerivAt_id t).const_mul α).add_const β).ofReal_comp
    exact ha.mul (hder t ht)
  have hQ0 (t : ℝ) (ht : t ∈ uIcc a c) : ‖Q t‖ ≤ B := by
    linarith [hQ t ht, norm_nonneg (Q' t)]
  have hQ1 (t : ℝ) (ht : t ∈ uIcc a c) : ‖Q' t‖ ≤ B := by
    linarith [hQ t ht, norm_nonneg (Q t)]
  have hf (t : ℝ) (ht : t ∈ uIcc a c) : ‖F t‖ ≤ B := by
    calc
      _ = |α*t+β| * ‖Q t‖ := by simp only [F, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 1*B := mul_le_mul (hA t ht) (hQ0 t ht) (norm_nonneg _) (by norm_num)
      _ = B := one_mul _
  have hf' (t : ℝ) (ht : t ∈ uIcc a c) : ‖F' t‖ ≤ (1/b+1)*B := by
    calc
      _ ≤ ‖(α : ℂ)*Q t‖+‖((α*t+β : ℝ) : ℂ)*Q' t‖ := norm_add_le _ _
      _ = |α| * ‖Q t‖+|α*t+β| * ‖Q' t‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ (1/b)*B+1*B := add_le_add
        (mul_le_mul hα (hQ0 t ht) (norm_nonneg _) (by positivity))
        (mul_le_mul (hA t ht) (hQ1 t ht) (norm_nonneg _) (by norm_num))
      _ = (1/b+1)*B := by ring
  have h := oscillatory_interval_bound hac hy hcF' hdF
    (hf a left_mem_uIcc) (hf c right_mem_uIcc) hf'
  have he : (2*B+((1/b+1)*B)*(c-a))/y=(3+b)*B/y := by
    rw [hlen]
    field_simp [hb.ne']
    <;> ring
  rw [he] at h
  exact h

private lemma shifted_phi_zero {b d t : ℝ} (hb : 0 < b)
    (ht : t ∉ Icc (d-b) (d+b)) : phi b (t-d)=0 := by
  apply phi_eq_zero hb
  by_contra h
  have hh : |t-d| < b := lt_of_not_ge h
  have := abs_lt.mp hh
  exact ht ⟨by linarith, by linarith⟩

private lemma tent_weighted_integrable {b d : ℝ} {Q : ℝ → ℂ} (hb : 0 < b)
    (hQ : ContinuousOn Q (Icc (d-b) (d+b))) :
    Integrable (fun t => (phi b (t-d) : ℂ)*Q t) := by
  have hc : ContinuousOn (fun t => (phi b (t-d) : ℂ)*Q t) (Icc (d-b) (d+b)) :=
    ((Complex.continuous_ofReal.comp ((phi_continuous b).comp
      (continuous_id.sub continuous_const))).continuousOn).mul hQ
  apply hc.integrableOn_Icc.integrable_of_forall_notMem_eq_zero
  intro t ht
  simp [shifted_phi_zero hb ht]

private lemma tent_oscillatory_bound {b d y B : ℝ} {Q Q' : ℝ → ℂ}
    (hb : 0 < b) (hy : 0 < y) (hB : 0 ≤ B)
    (hQ' : ContinuousOn Q' (Icc (d-b) (d+b)))
    (hder : ∀ t ∈ Icc (d-b) (d+b), HasDerivAt Q (Q' t) t)
    (hQ : ∀ t ∈ Icc (d-b) (d+b), ‖Q t‖+‖Q' t‖ ≤ B) :
    ‖∫ t, (phi b (t-d) : ℂ)*Q t*
      Complex.exp ((t : ℂ)*(y : ℂ)*Complex.I)‖ ≤ 6*(1+b)*B/y := by
  let E : ℝ → ℂ := fun t => Complex.exp ((t : ℂ)*(y : ℂ)*Complex.I)
  have hcQ : ContinuousOn Q (Icc (d-b) (d+b)) :=
    fun t ht => (hder t ht).continuousAt.continuousWithinAt
  have hc : ContinuousOn (fun t => (phi b (t-d) : ℂ)*Q t*E t)
      (Icc (d-b) (d+b)) := by
    exact (((Complex.continuous_ofReal.comp ((phi_continuous b).comp
      (continuous_id.sub continuous_const))).continuousOn).mul hcQ).mul
      (by dsimp [E]; fun_prop : Continuous E).continuousOn
  have hleft : uIcc (d-b) d ⊆ Icc (d-b) (d+b) := by
    rw [uIcc_of_le (by linarith)]
    intro t ht; exact ⟨ht.1, by linarith [ht.2]⟩
  have hright : uIcc d (d+b) ⊆ Icc (d-b) (d+b) := by
    rw [uIcc_of_le (by linarith)]
    intro t ht; exact ⟨by linarith [ht.1], ht.2⟩
  have hL := affine_oscillatory_bound (Q := Q) (Q' := Q')
    (a := d-b) (c := d) (α := 1/b) (β := 1-d/b) hb hy (by ring) hB
    (hQ'.mono hleft) (fun t ht => hder t (hleft ht)) (fun t ht => hQ t (hleft ht))
    (by rw [abs_of_pos (by positivity : 0 < 1/b)]) (by
      intro t ht
      rw [uIcc_of_le (by linarith)] at ht
      rw [abs_le]
      have h0 : 0 ≤ (t-(d-b))/b := div_nonneg (by linarith [ht.1]) hb.le
      have h1 : (t-(d-b))/b ≤ 1 := (div_le_one hb).mpr (by linarith [ht.2])
      have he : (1/b)*t+(1-d/b)=(t-(d-b))/b := by field_simp [hb.ne']; ring
      constructor <;> linarith)
  have hR := affine_oscillatory_bound (Q := Q) (Q' := Q')
    (a := d) (c := d+b) (α := -(1/b)) (β := 1+d/b) hb hy (by ring) hB
    (hQ'.mono hright) (fun t ht => hder t (hright ht)) (fun t ht => hQ t (hright ht))
    (by rw [abs_neg, abs_of_pos (by positivity : 0 < 1/b)]) (by
      intro t ht
      rw [uIcc_of_le (by linarith)] at ht
      rw [abs_le]
      have h0 : 0 ≤ ((d+b)-t)/b := div_nonneg (by linarith [ht.2]) hb.le
      have h1 : ((d+b)-t)/b ≤ 1 := (div_le_one hb).mpr (by linarith [ht.1])
      have he : -(1/b)*t+(1+d/b)=((d+b)-t)/b := by field_simp [hb.ne']; ring
      constructor <;> linarith)
  have hφL (t : ℝ) (ht : t ∈ uIcc (d-b) d) :
      phi b (t-d)=(1/b)*t+(1-d/b) := by
    rw [uIcc_of_le (by linarith)] at ht
    have ha : t-d ≤ 0 := by linarith [ht.2]
    unfold phi
    rw [abs_of_nonpos ha, max_eq_right (by
      apply sub_nonneg.mpr
      exact (div_le_one hb).mpr (by linarith [ht.1]))]
    ring
  have hφR (t : ℝ) (ht : t ∈ uIcc d (d+b)) :
      phi b (t-d)=-(1/b)*t+(1+d/b) := by
    rw [uIcc_of_le (by linarith)] at ht
    have ha : 0 ≤ t-d := by linarith [ht.1]
    unfold phi
    rw [abs_of_nonneg ha, max_eq_right (by
      apply sub_nonneg.mpr
      exact (div_le_one hb).mpr (by linarith [ht.2]))]
    ring
  have he : (∫ t, (phi b (t-d) : ℂ)*Q t*E t) =
      (∫ t in (d-b)..d, (((1/b)*t+(1-d/b) : ℝ) : ℂ)*Q t*E t)+
      ∫ t in d..(d+b), ((-(1/b)*t+(1+d/b) : ℝ) : ℂ)*Q t*E t := by
    have hz (t : ℝ) (ht : t ∉ Icc (d-b) (d+b)) :
        (phi b (t-d) : ℂ)*Q t*E t=0 := by simp [shifted_phi_zero hb ht]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hc.mono hleft).intervalIntegrable (hc.mono hright).intervalIntegrable]
    congr 1
    · exact intervalIntegral.integral_congr (fun t ht => by rw [hφL t ht])
    · exact intervalIntegral.integral_congr (fun t ht => by rw [hφR t ht])
  change ‖∫ t, (phi b (t-d) : ℂ)*Q t*E t‖ ≤ _
  rw [he]
  have hn := norm_add_le
    (∫ t in (d-b)..d, (((1/b)*t+(1-d/b) : ℝ) : ℂ)*Q t*E t)
    (∫ t in d..(d+b), ((-(1/b)*t+(1+d/b) : ℝ) : ℂ)*Q t*E t)
  calc
    _ ≤ 2*((3+b)*B/y) := by linarith
    _ ≤ 6*(1+b)*B/y := by
      rw [← mul_div_assoc]
      apply (div_le_div_iff_of_pos_right hy).mpr
      nlinarith

private lemma admissible_oscillatory_bound {g w : ℝ → ℝ} {b M y B : ℝ}
    {Q Q' : ℝ → ℂ} (hb : 0 < b) (hy : 0 < y) (hB : 0 ≤ B)
    (had : Admissible g w b M)
    (hQ' : ContinuousOn Q' (Icc (-M) M))
    (hder : ∀ t ∈ Icc (-M) M, HasDerivAt Q (Q' t) t)
    (hQ : ∀ t ∈ Icc (-M) M, ‖Q t‖+‖Q' t‖ ≤ B) :
    ‖∫ t in Icc (-M) M, (w t : ℂ)*Q t*
      Complex.exp ((t : ℂ)*(y : ℂ)*Complex.I)‖ ≤ 12*(1+b)*B/y := by
  let E : ℝ → ℂ := fun t => Complex.exp ((t : ℂ)*(y : ℂ)*Complex.I)
  have hcE : Continuous E := by dsimp [E]; fun_prop
  have hcQ : ContinuousOn Q (Icc (-M) M) :=
    fun t ht => (hder t ht).continuousAt.continuousWithinAt
  have hsub (d : ℝ) (hd : |d|+b ≤ M) : Icc (d-b) (d+b) ⊆ Icc (-M) M := by
    intro t ht
    exact ⟨by linarith [ht.1, neg_le_abs d], by linarith [ht.2, le_abs_self d]⟩
  have ht (d : ℝ) (hd : |d|+b ≤ M) :
      ‖∫ t, (phi b (t-d) : ℂ)*Q t*E t‖ ≤ 6*(1+b)*B/y :=
    tent_oscillatory_bound hb hy hB (hQ'.mono (hsub d hd))
      (fun t ht => hder t (hsub d hd ht)) (fun t ht => hQ t (hsub d hd ht))
  have hi (d : ℝ) (hd : |d|+b ≤ M) :
      Integrable (fun t => (phi b (t-d) : ℂ)*Q t*E t) := by
    simpa only [Pi.mul_apply, mul_assoc] using tent_weighted_integrable hb
      ((hcQ.mono (hsub d hd)).mul hcE.continuousOn)
  have hwzero (t : ℝ) (ht : t ∉ Icc (-M) M) : w t=0 := by
    have htm : M < |t| := by
      by_contra h
      exact ht (abs_le.mp (le_of_not_gt h))
    exact (admissible_laws hb had).2.2.2.2.2.2 t htm
  have heq : (∫ t in Icc (-M) M, (w t : ℂ)*Q t*E t) =
      ∫ t, (w t : ℂ)*Q t*E t :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => by simp [hwzero t ht])
  change ‖∫ t in Icc (-M) M, (w t : ℂ)*Q t*E t‖ ≤ _
  rw [heq]
  rcases had with ⟨_, rfl, hbM⟩ | ⟨U, hU, _, rfl, hUM⟩
  · have hh := ht 0 (by simpa using hbM)
    simp only [sub_zero] at hh
    exact hh.trans (by apply div_le_div_of_nonneg_right _ hy.le; nlinarith)
  · have hU0 : 0 < U := by linarith
    have hbM : b ≤ M := by linarith
    have h0 : |(0 : ℝ)|+b ≤ M := by simpa
    have hpos : |U|+b ≤ M := by rwa [abs_of_pos hU0]
    have hneg : |-U|+b ≤ M := by simpa only [abs_neg] using hpos
    let F₀ : ℝ → ℂ := fun t => (phi b (t-0) : ℂ)*Q t*E t
    let F₁ : ℝ → ℂ := fun t => (phi b (t-U) : ℂ)*Q t*E t
    let F₂ : ℝ → ℂ := fun t => (phi b (t-(-U)) : ℂ)*Q t*E t
    have hi0 : Integrable F₀ := hi 0 h0
    have hi1 : Integrable F₁ := hi U hpos
    have hi2 : Integrable F₂ := hi (-U) hneg
    have hfun : (fun t => (psi b U t : ℂ)*Q t*E t) =
        fun t => F₀ t-F₁ t/2-F₂ t/2 := by
      funext t
      dsimp [F₀, F₁, F₂, psi]
      simp only [sub_zero, sub_neg_eq_add]
      push_cast
      ring
    rw [hfun]
    have hs := integral_sub (hi0.sub (hi1.div_const 2)) (hi2.div_const 2)
    simp only [Pi.sub_apply] at hs
    rw [hs, integral_sub hi0 (hi1.div_const 2), integral_div, integral_div]
    have hn := norm_sub_le ((∫ t, F₀ t)-(∫ t, F₁ t)/2) ((∫ t, F₂ t)/2)
    have hn' := norm_sub_le (∫ t, F₀ t) ((∫ t, F₁ t)/2)
    simp only [norm_div, Complex.norm_ofNat] at hn hn'
    have hb0 := ht 0 h0
    have hb1 := ht U hpos
    have hb2 := ht (-U) hneg
    change ‖∫ t, F₀ t‖ ≤ _ at hb0
    change ‖∫ t, F₁ t‖ ≤ _ at hb1
    change ‖∫ t, F₂ t‖ ≤ _ at hb2
    have htwo : 12*(1+b)*B/y=2*(6*(1+b)*B/y) := by ring
    rw [htwo]
    linarith only [hn, hn', hb0, hb1, hb2]

private lemma boundary_regular_integral_bound (S : Spectrum) (hN : CountAsymptotic S)
    {f : ℝ → ℝ} {k : ℕ} (D : PairedLaplaceData S f k) :
    ∃ A : ℝ, 0 < A ∧ ∀ (g w : ℝ → ℝ) (b M y : ℝ),
      0 < b → 4 ≤ M → 1 ≤ y → Admissible g w b M →
      ‖(((1/(2*Real.pi) : ℝ) : ℂ) *
        ∫ t in Icc (-M) M, (w t : ℂ)*regularPart S D.J M ((t : ℂ)*Complex.I)*
          Complex.exp (Complex.I*(t : ℂ)*(y : ℂ)))‖ ≤
        A*((1+b)*M^(max k 1)/y) := by
  obtain ⟨B, hB, hbound⟩ := regularized_boundary_bound S hN D
  refine ⟨12*B, by positivity, ?_⟩
  intro g w b M y hb hM hy had
  let R : Set ℂ := {s | |s.re| < D.eta ∧ |s.im| < M+1}
  have hR : IsOpen R := (isOpen_lt Complex.continuous_re.abs continuous_const).inter
    (isOpen_lt Complex.continuous_im.abs continuous_const)
  let G : ℂ → ℂ := regularPart S D.J M
  have hG : DifferentiableOn ℂ G R := regularPart_differentiableOn S hN D hM
  let Q : ℝ → ℂ := fun t => G ((t : ℂ)*Complex.I)
  let Q' : ℝ → ℂ := fun t => deriv G ((t : ℂ)*Complex.I)*Complex.I
  have hmap (t : ℝ) (ht : t ∈ Icc (-M) M) : (t : ℂ)*Complex.I ∈ R := by
    change |((t : ℂ)*Complex.I).re| < D.eta ∧ |((t : ℂ)*Complex.I).im| < M+1
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im, mul_zero, sub_self, abs_zero, Complex.mul_im, mul_one, add_zero]
    exact ⟨D.eta_pos, by linarith [abs_le.mpr ht]⟩
  have hcQ' : ContinuousOn Q' (Icc (-M) M) :=
    (((hG.deriv hR).continuousOn.comp (by fun_prop) hmap).mul continuous_const.continuousOn)
  have hdQ (t : ℝ) (ht : t ∈ Icc (-M) M) : HasDerivAt Q (Q' t) t := by
    have hdG := (hG.differentiableAt (hR.mem_nhds (hmap t ht))).hasDerivAt
    have hdI : HasDerivAt (fun z : ℂ => z*Complex.I) Complex.I (t : ℂ) := by
      simpa using (hasDerivAt_id (t : ℂ)).mul_const Complex.I
    exact (hdG.comp (t : ℂ) hdI).comp_ofReal
  have hQQ' (t : ℝ) (ht : t ∈ Icc (-M) M) : ‖Q t‖+‖Q' t‖ ≤ B*M^(max k 1) := by
    simpa only [Q, Q', G, norm_mul, Complex.norm_I, mul_one] using
      hbound M t hM (abs_le.mpr ht)
  have hosc := admissible_oscillatory_bound hb (by linarith : 0 < y)
    (show 0 ≤ B*M^(max k 1) by positivity) had hcQ' hdQ hQQ'
  have hc : ‖((1/(2*Real.pi) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply (div_le_one (by positivity : 0 < 2*Real.pi)).mpr
    linarith [Real.two_le_pi]
  rw [norm_mul]
  calc
    _ ≤ ‖∫ t in Icc (-M) M, (w t : ℂ)*regularPart S D.J M ((t : ℂ)*Complex.I)*
        Complex.exp (Complex.I*(t : ℂ)*(y : ℂ))‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hc
    _ = ‖∫ t in Icc (-M) M, (w t : ℂ)*Q t*
        Complex.exp ((t : ℂ)*(y : ℂ)*Complex.I)‖ := by
      congr 1
      apply integral_congr_ae
      exact ae_of_all _ (fun t => by dsimp [Q,G]; congr 2 <;> ring)
    _ ≤ 12*(1+b)*(B*M^(max k 1))/y := hosc
    _ = (12*B)*((1+b)*M^(max k 1)/y) := by ring

/-- The one-sided logarithmic envelope permits undamping, with a uniform quantitative error. -/
theorem quantitative_boundary_formula (S : Spectrum) (hN : CountAsymptotic S)
    {f : ℝ → ℝ} {k : ℕ} (D : PairedLaplaceData S f k) :
    ∃ A : ℝ, 0 < A ∧ ∀ (g w : ℝ → ℝ) (b M y : ℝ),
      0 < b → 4 ≤ M → 1 ≤ y → Admissible g w b M → HasLogEnvelope f →
      IntegrableOn (fun u => f u * g (y - u)) (Set.Ici 0) ∧
      |(∫ u in Set.Ici 0, f u * g (y - u)) +
        ∑ j ∈ S.cut (2 * M), (S.mult j : ℝ) * w (S.gamma j) * Real.cos (S.gamma j * y)|
        ≤ A * ((1 + b) * M ^ (max k 1) / y + (S.N (2 * M) : ℝ) / (b * y)) := by
  obtain ⟨B, hB, hregular⟩ := boundary_regular_integral_bound S hN D
  refine ⟨B+4, by positivity, ?_⟩
  intro g w b M y hb hM hy had hbound
  have hM0 : 0 ≤ M := by linarith
  obtain ⟨hfi, hid⟩ := boundary_integrable_and_identity S hN D hbound hb hM hy had
  obtain ⟨_, _, _, hgi, _, _, _⟩ := admissible_laws hb had
  have hpi : IntegrableOn (fun u => polePolynomial S M u*g (y-u)) (Ici 0) := by
    exact ((hgi.comp_sub_left y).bdd_mul
      (polePolynomial_continuous S M).aestronglyMeasurable
      (ae_of_all _ (fun u => polePolynomial_bound S M u))).integrableOn
  have hsub : (∫ u in Ici 0, (f u-polePolynomial S M u)*g (y-u)) =
      (∫ u in Ici 0, f u*g (y-u)) - (∫ u in Ici 0, polePolynomial S M u*g (y-u)) := by
    rw [← integral_sub hfi hpi]
    apply integral_congr_ae
    exact ae_of_all _ (fun u => by dsimp only [Pi.sub_apply]; ring)
  have hreg : |(∫ u in Ici 0, f u*g (y-u)) -
      (∫ u in Ici 0, polePolynomial S M u*g (y-u))| ≤ B*((1+b)*M^(max k 1)/y) := by
    have hh := hregular g w b M y hb hM hy had
    rw [← hid] at hh
    simpa only [Complex.norm_real, Real.norm_eq_abs, hsub] using hh
  have hy0 : 0 < y := by linarith
  have hby : 0 < b*y := mul_pos hb hy0
  have htail := polePolynomial_truncation_error S hb hy0 had
  have htail' : |(∫ u in Ici 0, polePolynomial S M u*g (y-u)) +
      ∑ j ∈ S.cut (2*M), (S.mult j : ℝ)*w (S.gamma j)*Real.cos (S.gamma j*y)|
      ≤ 4*((S.N (2*M) : ℝ)/(b*y)) := htail.trans (by
    calc
      (S.N (2*M) : ℝ)*(4/(Real.pi*b*y)) ≤ (S.N (2*M) : ℝ)*(4/(b*y)) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply div_le_div_of_nonneg_left (by norm_num) hby
        calc
          b*y = 1*(b*y) := by ring
          _ ≤ Real.pi*(b*y) := mul_le_mul_of_nonneg_right
            (by linarith [Real.two_le_pi]) hby.le
          _ = Real.pi*b*y := by ring
      _ = _ := by ring)
  refine ⟨hfi, ?_⟩
  calc
    _ ≤ |(∫ u in Ici 0, f u*g (y-u)) - (∫ u in Ici 0, polePolynomial S M u*g (y-u))| +
        |(∫ u in Ici 0, polePolynomial S M u*g (y-u)) +
          ∑ j ∈ S.cut (2*M), (S.mult j : ℝ)*w (S.gamma j)*Real.cos (S.gamma j*y)| := by
      convert abs_add_le
        ((∫ u in Ici 0, f u*g (y-u)) - (∫ u in Ici 0, polePolynomial S M u*g (y-u)))
        ((∫ u in Ici 0, polePolynomial S M u*g (y-u)) +
          ∑ j ∈ S.cut (2*M), (S.mult j : ℝ)*w (S.gamma j)*Real.cos (S.gamma j*y)) using 1
      congr 1
      ring
    _ ≤ B*((1+b)*M^(max k 1)/y) + 4*((S.N (2*M) : ℝ)/(b*y)) := add_le_add hreg htail'
    _ ≤ (B+4)*((1+b)*M^(max k 1)/y + (S.N (2*M) : ℝ)/(b*y)) := by
      have hx : 0 ≤ (1+b)*M^(max k 1)/y := by positivity
      have hn : 0 ≤ (S.N (2*M) : ℝ)/(b*y) := by positivity
      nlinarith

#print axioms laplace_converges_of_log_envelope

end
end D5.S3.Analytic.Laplace.QuantitativeFejerBoundary
