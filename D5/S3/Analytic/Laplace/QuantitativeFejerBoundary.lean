/- GID: D5/S3/Analytic/Laplace/QuantitativeFejerBoundary
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/QuantitativeFejerBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Logarithmic one-sided envelopes give absolute Laplace convergence. -/

import D5.S3.Analytic.Laplace.PairedPoleRegularity
import D5.S3.Analytic.Fourier.AngularFejerKernel
import D5.S3.Analytic.Laplace.AbscissaSingularity
import Mathlib.Analysis.Analytic.Uniqueness

/-! Laplace convergence under a one-sided logarithmic envelope. -/

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


#print axioms laplace_converges_of_log_envelope

end
end D5.S3.Analytic.Laplace.QuantitativeFejerBoundary
