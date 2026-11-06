/- GID: D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fourier inversion and damping limits control convolutions with admissible Fejer kernels. -/

import D5.S3.Analytic.Laplace.QuantitativeFejerBoundary.Continuation

/-! Fourier inversion and damping limits control convolutions with admissible Fejer kernels. -/

namespace D5.S3.Analytic.Laplace.QuantitativeFejerBoundary

open D5.S3.Analytic.Fourier.AngularFejerKernel
  D5.S3.Analytic.Oscillation.OrdinateCounting
  D5.S3.Analytic.Laplace.PairedPoleRegularity
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

noncomputable section

set_option backward.isDefEq.respectTransparency false

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

lemma phi_continuous (b : ℝ) : Continuous (phi b) := by
  unfold phi; fun_prop

lemma phi_eq_zero {b t : ℝ} (hb : 0 < b) (ht : b ≤ |t|) : phi b t = 0 := by
  exact max_eq_left ((sub_nonpos.mpr ((le_div_iff₀ hb).mpr (by simpa using ht))))

lemma admissible_laws {g w : ℝ → ℝ} {b M : ℝ} (hb : 0 < b)
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

lemma damped_fubini {q g w : ℝ → ℝ}
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


def polePolynomial (S : Spectrum) (M : ℝ) (u : ℝ) : ℝ :=
  -∑ j ∈ S.cut (2 * M), (S.mult j : ℝ) * Real.cos (S.gamma j * u)

lemma polePolynomial_continuous (S : Spectrum) (M : ℝ) :
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

lemma polePolynomial_convergence (S : Spectrum) (M : ℝ) {σ : ℝ} (hσ : 0 < σ) :
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

lemma polePolynomial_laplace (S : Spectrum) (M : ℝ) {s : ℂ} (hs : 0 < s.re) :
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

def damping (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1) / 2

lemma damping_pos (n : ℕ) : 0 < damping n := by unfold damping; positivity

lemma damping_lt_one (n : ℕ) : damping n < 1 := by
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

lemma damped_integral_tendsto {q : ℝ → ℝ}
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


lemma admissible_log_integrable {g w : ℝ → ℝ} {b M y : ℝ}
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

lemma regular_integral_tendsto (S : Spectrum) (hN : CountAsymptotic S)
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


lemma admissible_bounded {g w : ℝ → ℝ} {b M : ℝ} (hb : 0 < b)
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

lemma polePolynomial_bound (S : Spectrum) (M u : ℝ) :
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

lemma damped_cast_integral (q g : ℝ → ℝ) (σ y : ℝ) :
    (∫ u in Ici 0, (q u : ℂ) * Complex.exp (-(σ : ℂ)*(u : ℂ)) * (g (y-u) : ℂ)) =
      ((∫ u in Ici 0, q u * Real.exp (-σ*u) * g (y-u) : ℝ) : ℂ) := by
  calc
    _ = ∫ u in Ici 0, ((q u * Real.exp (-σ*u) * g (y-u) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with u
      push_cast
      rfl
    _ = _ := integral_ofReal

lemma integrable_of_one_sided_damping {q a : ℝ → ℝ}
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

lemma polePolynomial_truncation_error (S : Spectrum) {g w : ℝ → ℝ}
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

end
end D5.S3.Analytic.Laplace.QuantitativeFejerBoundary
