/- GID: D5/S3/MeasureTheory/AffineStrongContinuity
   generality: G
   mirror-B: none(waiver:covered-by-hyperfinite-type-ii1-factor-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Schwartz decay gives a locally uniform square-integrable envelope for the real affine action and its dilation derivative. -/

import D5.S3.MeasureTheory.RealAffineRepresentation
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
Omega original.

Schwartz decay gives a locally uniform square-integrable envelope for the real affine
action and its dilation derivative. The action is strongly continuous on all of
Lebesgue L².
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Omega.RealAffine

open scoped NNReal ENNReal SchwartzMap Topology FourierTransform
open MeasureTheory Filter Set

private theorem tendsto_L2_of_representatives
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {q : ι → PositionL2} {g : PositionL2}
    {F : ι → ℝ → ℂ} (hF : ∀ a, ⇑(q a - g) =ᵐ[volume] F a)
    {M : ℝ → ℝ} (hM : MemLp M 2 volume)
    (hbound : ∀ᶠ a in l, ∀ᵐ x ∂volume, ‖F a x‖ ≤ ‖M x‖)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun a => F a x) l (𝓝 0)) : Tendsto q l (𝓝 g) := by
  have hFm (a : ι) : MemLp (F a) 2 volume :=
    (memLp_congr_ae (hF a)).mp (Lp.memLp _)
  have hMt := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hM.eLpNorm_lt_top
  have hInt : Tendsto (fun a : ι => ∫⁻ x, ‖F a x‖ₑ ^ (2 : ℝ)) l (𝓝 0) := by
    have h := tendsto_lintegral_filter_of_dominated_convergence'
      (l := l) (F := fun a x => ‖F a x‖ₑ ^ (2 : ℝ)) (f := fun _ : ℝ => (0 : ℝ≥0∞))
      (μ := volume) (fun x => ‖M x‖ₑ ^ (2 : ℝ))
      (Eventually.of_forall fun a => (hFm a).aestronglyMeasurable.enorm.pow_const _)
      (hbound.mono fun a ha => ha.mono fun x hx => by
        apply ENNReal.rpow_le_rpow _ (by norm_num)
        simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal hx)
      (by simpa using hMt.ne)
      (hlim.mono fun x hx => by
        simpa [Function.comp_def] using
          (ENNReal.continuous_rpow_const (y := 2)).continuousAt.tendsto.comp
            ((continuous_enorm.continuousAt (x := 0)).tendsto.comp hx))
    simpa using h
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have he (a : ι) : ‖q a - g‖ = ((∫⁻ x, ‖F a x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)).toReal := by
    rw [Lp.norm_def, eLpNorm_congr_ae (hF a),
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
        (hFm a).aestronglyMeasurable]
    norm_num
  simp_rw [he]
  have hr := (ENNReal.continuous_rpow_const (y := 1 / 2)).continuousAt.tendsto.comp hInt
  have hr₀ : Tendsto (fun a : ι => (∫⁻ x, ‖F a x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) l (𝓝 0) := by
    simpa [Function.comp_def] using hr
  simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hr₀

private theorem decay_memLp (C : ℝ) : MemLp (fun x : ℝ => C / (1 + ‖x‖)) 2 volume := by
  have hcont : Continuous (fun x : ℝ => C / (1 + ‖x‖)) :=
    continuous_const.div (continuous_const.add continuous_norm) (fun _ => by positivity)
  apply (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).mpr
  have h : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(2 : ℝ))) volume :=
    integrable_one_add_norm (by simp : (Module.finrank ℝ ℝ : ℝ) < 2)
  convert h.const_mul (C ^ 2) using 1
  funext x
  rw [div_pow, Real.rpow_neg (by positivity), Real.rpow_two, div_eq_mul_inv]

private theorem schwartz_decay (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, (1 + ‖x‖) * ‖f x‖ ≤ C := by
  refine ⟨SchwartzMap.seminorm ℂ 0 0 f + SchwartzMap.seminorm ℂ 1 0 f, by positivity, ?_⟩
  intro x
  have h0 := SchwartzMap.norm_le_seminorm ℂ f x
  have h1 := SchwartzMap.norm_pow_mul_le_seminorm ℂ f 1 x
  simp only [pow_one] at h1
  linarith only [h0, h1]

private def representative {c : ℝ} (g : Affine c) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  weight g * f (coord g x)

private theorem representative_schwartz_ae {c : ℝ} (g : Affine c) (f : 𝓢(ℝ, ℂ)) :
    ⇑(affineUnitary c g (f.toLp 2)) =ᵐ[volume] representative g f := by
  have hmeas : Measurable (coord g) := by unfold coord; fun_prop
  have hq : QuasiMeasurePreserving (coord g) volume volume := by
    refine ⟨hmeas, ?_⟩
    rw [affine_map_volume]
    exact Measure.AbsolutelyContinuous.smul_left .rfl _
  have hf := hq.tendsto_ae.eventually (f.coeFn_toLp 2 volume)
  filter_upwards [affineUnitary_ae g (f.toLp 2), hf] with x h₁ h₂
  unfold representative
  rw [h₁, weight_eq]
  exact congrArg (fun z : ℂ => ((Real.sqrt (scale g))⁻¹ : ℝ) * z) h₂

private theorem representative_bound {c : ℝ} (g : Affine c) (f : ℝ → ℂ)
    {C : ℝ} (hf : ∀ y : ℝ, (1 + ‖y‖) * ‖f y‖ ≤ C)
    {A B W : ℝ} (hA : ‖g.a‖ ≤ A) (hB : scale g ≤ B) (hW : ‖weight g‖ ≤ W) (x : ℝ) :
    ‖representative g f x‖ ≤ W * ((1 + A + B) * C) / (1 + ‖x‖) := by
  have hA₀ := (norm_nonneg g.a).trans hA
  have hB₀ := (scale_pos g).le.trans hB
  have hW₀ := (norm_nonneg (weight g)).trans hW
  have hx : x = scale g * coord g x - g.a := by
    unfold coord
    rw [mul_comm, div_mul_cancel₀ _ (scale_pos g).ne']
    ring
  have hb : 1 + ‖x‖ ≤ (1 + A + B) * (1 + ‖coord g x‖) := by
    conv_lhs => rw [hx]
    have h := norm_sub_le (scale g * coord g x) g.a
    rw [norm_mul, Real.norm_of_nonneg (scale_pos g).le] at h
    calc
      _ ≤ 1 + scale g * ‖coord g x‖ + ‖g.a‖ := by linarith only [h]
      _ ≤ 1 + B * ‖coord g x‖ + A := by gcongr
      _ ≤ _ := by
        have hm := mul_nonneg (show 0 ≤ 1 + A by positivity) (norm_nonneg (coord g x))
        nlinarith only [hB₀, hm]
  rw [le_div_iff₀ (by positivity), representative, norm_mul]
  calc
    _ ≤ (W * ‖f (coord g x)‖) * ((1 + A + B) * (1 + ‖coord g x‖)) := by gcongr
    _ = W * ((1 + A + B) * ((1 + ‖coord g x‖) * ‖f (coord g x)‖)) := by ring
    _ ≤ _ := by gcongr; exact hf _

private theorem continuous_representative (c : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Continuous (fun p : ℝ × ℝ => representative (⟨p.1, p.2⟩ : Affine c) f x) := by
  have hf := f.continuous
  unfold representative weight coord scale
  have hscale : Continuous (fun p : ℝ × ℝ => Real.exp (c * p.1)) := by fun_prop
  have hcoord : Continuous (fun p : ℝ × ℝ => (x + p.2) / Real.exp (c * p.1)) :=
    (continuous_const.add continuous_snd).div hscale (fun _ => (Real.exp_pos _).ne')
  fun_prop

private theorem representative_local_decay (c : ℝ) (f : 𝓢(ℝ, ℂ)) (p : ℝ × ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ᶠ q in 𝓝 p, ∀ x, ‖representative (⟨q.1, q.2⟩ : Affine c) f x‖ ≤ M / (1 + ‖x‖)) ∧
      ∀ x, ‖representative (⟨p.1, p.2⟩ : Affine c) f x‖ ≤ M / (1 + ‖x‖) := by
  obtain ⟨C, hC, hdecay⟩ := schwartz_decay f
  let A := ‖p.2‖ + 1
  let B := scale (⟨p.1, p.2⟩ : Affine c) + 1
  let W := ‖weight (⟨p.1, p.2⟩ : Affine c)‖ + 1
  let M := W * ((1 + A + B) * C)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; linarith [scale_pos (⟨p.1, p.2⟩ : Affine c)]
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hcontA : Continuous (fun q : ℝ × ℝ => ‖q.2‖) := continuous_snd.norm
  have hcontB : Continuous (fun q : ℝ × ℝ => scale (⟨q.1, q.2⟩ : Affine c)) := by
    unfold scale
    fun_prop
  have hcontW : Continuous (fun q : ℝ × ℝ => ‖weight (⟨q.1, q.2⟩ : Affine c)‖) := by
    unfold weight
    fun_prop
  have h₁ : ∀ᶠ q : ℝ × ℝ in 𝓝 p, ‖q.2‖ < A :=
    hcontA.continuousAt.eventually_lt continuousAt_const (lt_add_one _)
  have h₂ : ∀ᶠ q : ℝ × ℝ in 𝓝 p, scale (⟨q.1, q.2⟩ : Affine c) < B :=
    hcontB.continuousAt.eventually_lt continuousAt_const (lt_add_one _)
  have h₃ : ∀ᶠ q : ℝ × ℝ in 𝓝 p, ‖weight (⟨q.1, q.2⟩ : Affine c)‖ < W :=
    hcontW.continuousAt.eventually_lt continuousAt_const (lt_add_one _)
  refine ⟨M, by dsimp [M]; positivity, ?_, ?_⟩
  · filter_upwards [h₁, h₂, h₃] with q qa qb qw x
    exact representative_bound _ f hdecay qa.le qb.le qw.le x
  · exact representative_bound _ f hdecay (lt_add_one _).le (lt_add_one _).le (lt_add_one _).le

private theorem affineUnitary_schwartz_continuous (c : ℝ) (f : 𝓢(ℝ, ℂ)) :
    Continuous (fun p : ℝ × ℝ => affineUnitary c ⟨p.1, p.2⟩ (f.toLp 2)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨M, hM, hb, hp⟩ := representative_local_decay c f p
  apply tendsto_L2_of_representatives
    (F := fun q x => representative (⟨q.1, q.2⟩ : Affine c) f x -
      representative (⟨p.1, p.2⟩ : Affine c) f x)
    (M := fun x => 2 * M / (1 + ‖x‖))
  · intro q
    filter_upwards [Lp.coeFn_sub (affineUnitary c ⟨q.1, q.2⟩ (f.toLp 2))
      (affineUnitary c ⟨p.1, p.2⟩ (f.toLp 2)), representative_schwartz_ae ⟨q.1, q.2⟩ f,
      representative_schwartz_ae ⟨p.1, p.2⟩ f] with x h₁ h₂ h₃
    rw [h₁, Pi.sub_apply, h₂, h₃]
  · exact decay_memLp _
  · filter_upwards [hb] with q hq
    exact Eventually.of_forall fun x => calc
      _ ≤ ‖representative (⟨q.1, q.2⟩ : Affine c) f x‖ +
          ‖representative (⟨p.1, p.2⟩ : Affine c) f x‖ := norm_sub_le _ _
      _ ≤ M / (1 + ‖x‖) + M / (1 + ‖x‖) := add_le_add (hq x) (hp x)
      _ = _ := by
        rw [Real.norm_of_nonneg (show 0 ≤ 2 * M / (1 + ‖x‖) by positivity), two_mul, add_div]
  · exact Eventually.of_forall fun x => by
      simpa only [sub_self] using ((continuous_representative c f x).continuousAt (x := p)).tendsto.sub_const
        (representative (⟨p.1, p.2⟩ : Affine c) f x)

private theorem continuous_isometric_family_of_dense {X E D : Type*}
    [PseudoMetricSpace X] [MetricSpace E] {u : X → E → E} {j : D → E}
    (hisom : ∀ x, Isometry (u x)) (hdense : DenseRange j)
    (hj : ∀ d, Continuous (fun x => u x (j d))) (f : E) :
    Continuous (fun x => u x f) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hε₃ : 0 < ε / 3 := by positivity
  obtain ⟨d, hd⟩ := hdense.exists_dist_lt f hε₃
  obtain ⟨δ, hδ, hloc⟩ := Metric.continuousAt_iff.mp ((hj d).continuousAt (x := p)) (ε / 3) hε₃
  refine ⟨δ, hδ, fun q hq => ?_⟩
  have h₁ := dist_triangle (u q f) (u q (j d)) (u p f)
  have h₂ := dist_triangle (u q (j d)) (u p (j d)) (u p f)
  rw [(hisom q).dist_eq] at h₁
  rw [(hisom p).dist_eq, dist_comm (j d) f] at h₂
  have h₃ := hloc hq
  linarith only [h₁, h₂, h₃, hd]

/-- Joint strong continuity in the dilation and translation parameters on all of L². -/
theorem affineUnitary_strongContinuous (c : ℝ) (f : PositionL2) :
    Continuous (fun p : ℝ × ℝ => affineUnitary c ⟨p.1, p.2⟩ f) := by
  apply continuous_isometric_family_of_dense
    (u := fun p : ℝ × ℝ => (affineUnitary c ⟨p.1, p.2⟩ : PositionL2 → PositionL2))
    (j := SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 volume)
  · exact fun p => (affineUnitary c ⟨p.1, p.2⟩).isometry
  · exact SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  · exact affineUnitary_schwartz_continuous c

private def dilationRepresentative (c : ℝ) (f : 𝓢(ℝ, ℂ)) (s x : ℝ) : ℂ :=
  representative (dilation c (-s)) f x

private theorem dilationRepresentative_eq (c : ℝ) (f : 𝓢(ℝ, ℂ)) (s x : ℝ) :
    dilationRepresentative c f s x = (Real.exp (c * s / 2) : ℂ) * f (Real.exp (c * s) * x) := by
  unfold dilationRepresentative representative weight coord dilation scale
  simp [mul_neg, neg_neg, Real.exp_neg, div_eq_inv_mul]

private def dilationDerivative (c : ℝ) (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  -Complex.I • schwartzK c f

private theorem dilationRepresentative_hasDerivAt (c : ℝ) (f : 𝓢(ℝ, ℂ)) (s x : ℝ) :
    HasDerivAt (fun t => dilationRepresentative c f t x)
      (dilationRepresentative c (dilationDerivative c f) s x) s := by
  simp_rw [dilationRepresentative_eq]
  have hw : HasDerivAt (fun t : ℝ => (Real.exp (c * t / 2) : ℂ))
      (↑(Real.exp (c * s / 2) * (c / 2)) : ℂ) s := by
    simpa using (Real.hasDerivAt_exp _ |>.comp s (((hasDerivAt_id s).const_mul c).div_const 2)
      |>.ofReal_comp)
  have harg : HasDerivAt (fun t : ℝ => Real.exp (c * t) * x) (Real.exp (c * s) * c * x) s := by
    simpa using ((Real.hasDerivAt_exp _).comp s ((hasDerivAt_id s).const_mul c)).mul_const x
  have hcomp : HasDerivAt (fun t : ℝ => f (Real.exp (c * t) * x))
      ((Real.exp (c * s) * c * x) • deriv f (Real.exp (c * s) * x)) s := by
    simpa [Function.comp_def] using
      (f.differentiableAt (x := Real.exp (c * s) * x)).hasDerivAt.scomp s harg
  convert hw.mul hcomp using 1
  simp only [dilationDerivative, smul_apply, smul_eq_mul, schwartzK_apply, Complex.real_smul,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat]
  have hi : -Complex.I * (Complex.I * (c : ℂ)) = (c : ℂ) := by
    rw [← mul_assoc, neg_mul, ← pow_two, Complex.I_sq, neg_neg, one_mul]
  rw [← mul_assoc (-Complex.I), hi]
  ring

private theorem dilationRepresentative_zero (c : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    dilationRepresentative c f 0 x = f x := by
  simp [dilationRepresentative_eq]

private theorem dilationDerivative_bound (c : ℝ) (f : 𝓢(ℝ, ℂ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ δ > 0, ∀ t ∈ Metric.ball (0 : ℝ) δ, ∀ x,
      ‖dilationRepresentative c (dilationDerivative c f) t x‖ ≤ M / (1 + ‖x‖) := by
  obtain ⟨M, hM, he, _⟩ := representative_local_decay c (dilationDerivative c f) (0, 0)
  have hp : Continuous (fun t : ℝ => (-t, (0 : ℝ))) := by fun_prop
  have ht : Tendsto (fun t : ℝ => (-t, (0 : ℝ))) (𝓝 0) (𝓝 (0, 0)) := by
    simpa only [neg_zero] using (hp.continuousAt (x := 0)).tendsto
  have he' := ht.eventually he
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp he'
  exact ⟨M, hM, δ, hδ, fun _ ht x => hb ht x⟩

private theorem dilationSlope_bound {M δ : ℝ} (hδ : 0 < δ)
    (c : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) {s : ℝ} (hs : s ∈ Metric.ball (0 : ℝ) δ)
    (hb : ∀ t ∈ Metric.ball (0 : ℝ) δ,
      ‖dilationRepresentative c (dilationDerivative c f) t x‖ ≤ M / (1 + ‖x‖)) :
    ‖s⁻¹ • (dilationRepresentative c f s x - f x)‖ ≤ M / (1 + ‖x‖) := by
  have hzero : (0 : ℝ) ∈ Metric.ball 0 δ := Metric.mem_ball_self hδ
  have hM := (norm_nonneg _).trans (hb 0 hzero)
  by_cases hz : s = 0
  · simpa [hz] using hM
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t _ => (dilationRepresentative_hasDerivAt c f t x).differentiableAt)
    (fun t ht => by rw [(dilationRepresentative_hasDerivAt c f t x).deriv]; exact hb t ht)
    (convex_ball (0 : ℝ) δ) hzero hs
  rw [dilationRepresentative_zero, sub_zero] at h
  rw [norm_smul, norm_inv, ← div_eq_inv_mul, div_le_iff₀ (norm_pos_iff.mpr hz)]
  exact h

/-- Dilation has the strong Fourier derivative `-iK` on Schwartz vectors. -/
theorem schwartz_dilation_strongDerivative (c : ℝ) (f : 𝓢(ℝ, ℂ)) :
    HasDerivAt (fun s => affineUnitary c (dilation c (-s)) (f.toLp 2))
      ((-Complex.I • schwartzK c f).toLp 2) 0 := by
  let U := fun s : ℝ => affineUnitary c (dilation c (-s)) (f.toLp 2)
  have hU0 : U 0 = f.toLp 2 := by
    change affineUnitary c (dilation c (-0)) (f.toLp 2) = _
    rw [neg_zero, show dilation c 0 = 1 from rfl, map_one]
    rfl
  rw [hasDerivAt_iff_tendsto_slope_zero]
  change Tendsto (fun s => s⁻¹ • (U (0 + s) - U 0)) (𝓝[≠] 0)
    (𝓝 ((dilationDerivative c f).toLp 2))
  simp only [zero_add, hU0]
  obtain ⟨M, hM, δ, hδ, hb⟩ := dilationDerivative_bound c f
  let F := fun s x => s⁻¹ • (dilationRepresentative c f s x - f x) - dilationDerivative c f x
  apply tendsto_L2_of_representatives (F := F) (M := fun x => 2 * M / (1 + ‖x‖))
  · intro s
    let A : PositionL2 := U s - f.toLp 2 volume
    let G : PositionL2 := (dilationDerivative c f).toLp 2 volume
    filter_upwards [Lp.coeFn_sub (s⁻¹ • A) G,
      Lp.coeFn_smul s⁻¹ A, Lp.coeFn_sub (U s) (f.toLp 2 volume),
      representative_schwartz_ae (dilation c (-s)) f, f.coeFn_toLp 2 volume,
      (dilationDerivative c f).coeFn_toLp 2 volume] with x h₁ h₂ h₃ h₄ h₅ h₆
    change (s⁻¹ • A - G) x = F s x
    rw [h₁, Pi.sub_apply, h₂, Pi.smul_apply, h₆]
    change s⁻¹ • (U s - f.toLp 2 volume) x - dilationDerivative c f x = _
    rw [h₃, Pi.sub_apply, h₄, h₅]
    rfl
  · exact decay_memLp _
  · have hnear : ∀ᶠ s in 𝓝[≠] (0 : ℝ), s ∈ Metric.ball 0 δ :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) hδ)
    filter_upwards [hnear] with s hs
    exact Eventually.of_forall fun x => calc
      ‖F s x‖ ≤ ‖s⁻¹ • (dilationRepresentative c f s x - f x)‖ +
          ‖dilationDerivative c f x‖ := norm_sub_le _ _
      _ ≤ M / (1 + ‖x‖) + M / (1 + ‖x‖) := by
        refine add_le_add (dilationSlope_bound hδ c f x hs (fun t ht => hb t ht x)) ?_
        simpa only [dilationRepresentative_zero] using hb 0 (Metric.mem_ball_self hδ) x
      _ = _ := by
        rw [Real.norm_of_nonneg (show 0 ≤ 2 * M / (1 + ‖x‖) by positivity), two_mul, add_div]
  · exact Eventually.of_forall fun x => by
      have ht := (dilationRepresentative_hasDerivAt c f 0 x).tendsto_slope_zero
      simp only [zero_add, dilationRepresentative_zero] at ht
      simpa only [F, sub_self] using ht.sub_const (dilationDerivative c f x)

/-- Fourier transformation intertwines position dilation with reciprocal dilation. -/
theorem fourier_dilation_intertwines (c s : ℝ) (f : PositionL2) :
    𝓕 (affineUnitary c (dilation c s) f) =
      affineUnitary c (dilation c (-s)) (𝓕 f) := by
  apply Lp.ext
  filter_upwards [fourier_affineUnitary_ae (dilation c s) f,
    affineUnitary_ae (dilation c (-s)) (𝓕 f)] with ξ h₁ h₂
  rw [h₁, h₂]
  simp [dilation, scale, phase, mul_neg, Real.exp_neg, Real.sqrt_inv, div_eq_inv_mul, mul_comm]

/-- The Fourier orbit of a position-space dilation differentiates to `-iK` in Hilbert norm. -/
theorem schwartz_dilation_fourier_strongDerivative (c : ℝ) (f : 𝓢(ℝ, ℂ)) :
    HasDerivAt (fun s => (𝓕 (affineUnitary c (dilation c s)
      (𝓕⁻ (f.toLp 2 : PositionL2))) : PositionL2))
      ((-Complex.I • schwartzK c f).toLp 2) 0 := by
  have hF : (𝓕 (𝓕⁻ (f.toLp 2 : PositionL2)) : PositionL2) = f.toLp 2 :=
    (Lp.fourierTransformₗᵢ ℝ ℂ).apply_symm_apply _
  simpa only [fourier_dilation_intertwines, hF] using schwartz_dilation_strongDerivative c f

end Omega.RealAffine
