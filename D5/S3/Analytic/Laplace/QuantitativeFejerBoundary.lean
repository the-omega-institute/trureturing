/- GID: D5/S3/Analytic/Laplace/QuantitativeFejerBoundary
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/QuantitativeFejerBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Logarithmic one-sided envelopes give Laplace convergence and quantitative Fejer boundary formulas. -/

import D5.S3.Analytic.Laplace.QuantitativeFejerBoundary.Continuation
import D5.S3.Analytic.Laplace.QuantitativeFejerBoundary.DampedIdentity
import D5.S3.Analytic.Laplace.QuantitativeFejerBoundary.BoundaryEstimate

/-! Laplace convergence and a quantitative boundary formula under a one-sided logarithmic envelope. -/

namespace D5.S3.Analytic.Laplace.QuantitativeFejerBoundary

open D5.S3.Analytic.Fourier.AngularFejerKernel
  D5.S3.Analytic.Oscillation.OrdinateCounting
  D5.S3.Analytic.Laplace.PairedPoleRegularity
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

noncomputable section

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
set_option backward.isDefEq.respectTransparency false

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
  rw [laplace_eq_poles_full_strip S hN D hbound hs, pole_sum_split S hN (2 * M) s,
    regularPart]
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


private lemma boundary_integrable_and_identity (S : Spectrum) (hN : CountAsymptotic S)
    {f : ℝ → ℝ} {k : ℕ} (D : PairedLaplaceData S f k) (hbound : HasLogEnvelope f)
    {g w : ℝ → ℝ} {b M y : ℝ} (hb : 0 < b) (hM : 1 ≤ M) (hy : 1 ≤ y)
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


/-- The one-sided logarithmic envelope permits undamping, with a uniform quantitative error. -/
theorem quantitative_boundary_formula (S : Spectrum) (hN : CountAsymptotic S)
    {f : ℝ → ℝ} {k : ℕ} (D : PairedLaplaceData S f k) :
    ∃ A : ℝ, 0 < A ∧ ∀ (g w : ℝ → ℝ) (b M y : ℝ),
      0 < b → 1 ≤ M → 1 ≤ y → Admissible g w b M → HasLogEnvelope f →
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

end
end D5.S3.Analytic.Laplace.QuantitativeFejerBoundary
