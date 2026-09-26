/- GID: D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworth
   generality: G
   mirror-B: D5/B/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform real-time Edgeworth, fixed-width local limits, and atom decay for irrational two-jump Poisson laws. -/

import D5.S3.TotalVariation.Asymptotics.CompoundPoissonEdgeworthCutoff

open MeasureTheory ProbabilityTheory Set Filter Convolution
open scoped FourierTransform Real NNReal ENNReal Topology BigOperators
noncomputable section
namespace CompoundPoissonEdgeworthProposal
open CompoundPoissonEdgeworth
open StatLean.HypothesisTesting hiding edgeworthCDF

/-- Uniform first Edgeworth expansion, fixed-width Ioc local limit, and uniform atom decay at all sufficiently large real times. -/
theorem result (p q a b : ℝ) (hp : 0<p) (hq : 0<q)
    (hb : b≠0) (hirr : Irrational (a/b)) :
    (∀ ε : ℝ, 0<ε → ∀ᶠ lam : ℝ in atTop, ∀ x : ℝ,
      Real.sqrt lam*|rateCDF lam p q a b x-rateEdgeworthCDF lam p q a b x| < ε) ∧
    (∀ h : ℝ, 0<h → ∀ ε : ℝ, 0<ε → ∀ᶠ lam : ℝ in atTop, ∀ y : ℝ,
      |Real.sqrt lam*(rateCountLaw lam p q).real
        {n | y<a*(n.1:ℝ)+b*(n.2:ℝ) ∧ a*(n.1:ℝ)+b*(n.2:ℝ)≤y+h} -
        (h/Real.sqrt (p*a^2+q*b^2))*gaussianPDFReal 0 1
          ((y-lam*(p*a+q*b))/Real.sqrt (lam*(p*a^2+q*b^2)))|<ε) ∧
    (∀ ε : ℝ, 0<ε → ∀ᶠ lam : ℝ in atTop, ∀ x : ℝ,
      Real.sqrt lam*(rateCountLaw lam p q).real {n | rateScore lam p q a b n=x}<ε) := by
  have pair_charFun (p q : ℝ≥0) (a b t : ℝ) :
      charFun (pairLaw p q a b) t =
      Complex.exp ((p:ℂ)*(Complex.exp ((t*a:ℝ)*Complex.I)-1)+
        (q:ℂ)*(Complex.exp ((t*b:ℝ)*Complex.I)-1)) := by
    have hone (p : ℝ≥0) (u : ℝ) :
        (∫ n : ℕ, Complex.exp (((u*(n:ℝ):ℝ):ℂ)*Complex.I) ∂poissonMeasure p) =
          Complex.exp ((p:ℂ)*(Complex.exp ((u:ℂ)*Complex.I)-1)) := by
      have hh := charFun_map_cast_poissonMeasure p u
      rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop)] at hh
      simpa only [Complex.ofReal_mul] using hh
    rw [pairLaw, charFun_apply_real, integral_map (by fun_prop) (by fun_prop)]
    have heq : (fun n : ℕ × ℕ => Complex.exp (((t*(a*(n.1:ℝ)+b*(n.2:ℝ)):ℝ):ℂ)*Complex.I)) =
        (fun n : ℕ × ℕ => Complex.exp ((((t*a)*(n.1:ℝ):ℝ):ℂ)*Complex.I)*
          Complex.exp ((((t*b)*(n.2:ℝ):ℝ):ℂ)*Complex.I)) := by
      funext n
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp_rw [← Complex.ofReal_mul]
    rw [heq, integral_prod_mul
      (fun n : ℕ => Complex.exp ((((t*a)*(n:ℝ):ℝ):ℂ)*Complex.I))
      (fun n : ℕ => Complex.exp ((((t*b)*(n:ℝ):ℝ):ℂ)*Complex.I)), hone, hone,
      ← Complex.exp_add]

  have centered_charFun (lam p q a b t : ℝ)
      (hlam : 0≤lam) (hp : 0≤p) (hq : 0≤q) :
      charFun (centeredLaw lam p q a b) t = Complex.exp (centeredExponent lam p q a b t) := by
    have hpmean := Real.coe_toNNReal (lam*p) (mul_nonneg hlam hp)
    have hqmean := Real.coe_toNNReal (lam*q) (mul_nonneg hlam hq)
    unfold centeredLaw
    simp only [sub_eq_add_neg]
    rw [charFun_map_add_const,pair_charFun,← Complex.exp_add]
    congr 1
    change (↑(↑(Real.toNNReal (lam*p)):ℝ):ℂ)*_+(↑(↑(Real.toNNReal (lam*q)):ℝ):ℂ)*_+_ = _
    rw [hpmean,hqmean]
    dsimp [centeredExponent]
    simp only [starRingEnd_apply,star_trivial]
    push_cast
    ring

  have scaledError_integrable (p q a b w l r : ℝ) (hp : 0≤p) (hq : 0≤q) :
      IntegrableOn (fun u => ‖scaledError p q a b w u‖/|u|) (Icc l r) := by
    have hd : Differentiable ℝ (scaledError p q a b w) := by
      change Differentiable ℝ (fun u => scaledError p q a b w u)
      simp only [scaledError, centered_charFun (w^2) p q a b _ (sq_nonneg _) hp hq,
        centeredExponent]
      fun_prop
    have hz : scaledError p q a b w 0 = 0 := by
      simp [scaledError, centered_charFun (w^2) p q a b _ (sq_nonneg _) hp hq,
        centeredExponent]
    have hc : Continuous (dslope (scaledError p q a b w) 0) := by
      apply continuous_iff_continuousAt.mpr
      intro y
      by_cases hy : y=0
      · subst y; exact continuousAt_dslope_same.mpr (hd 0)
      · exact (continuousAt_dslope_of_ne hy).mpr hd.continuous.continuousAt
    apply hc.norm.integrableOn_Icc.congr
    filter_upwards [ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton (0:ℝ)))] with u hu0
    have hun : u≠0 := by simpa using hu0
    rw [dslope_of_ne _ hun, slope_def_module, hz, sub_zero, sub_zero,
      norm_smul, norm_inv, Real.norm_eq_abs]
    ring
  have scaledError_neg_norm (p q a b w u : ℝ) :
      ‖scaledError p q a b w (-u)‖ = ‖scaledError p q a b w u‖ := by
    have heq : scaledError p q a b w (-u) =
        starRingEnd ℂ (scaledError p q a b w u) := by
      simp only [scaledError, neg_div, charFun_neg, map_sub, map_mul, map_add, map_one,
        map_pow, Complex.conj_ofReal, Complex.conj_I, neg_sq]
      push_cast
      ring
    rw [heq, Complex.norm_conj]

  have normalized_uniform_edgeworth (p q a b : ℝ) (hp : 0<p) (hq : 0<q)
      (hb0 : b≠0) (hirr : Irrational (a/b)) (hV : p*a^2+q*b^2=1) :
      ∀ ε : ℝ, 0<ε → ∀ᶠ w : ℝ in atTop, ∀ x : ℝ,
        w*|(normalizedLaw w p q a b).real (Iic x)-
          StatLean.HypothesisTesting.edgeworthCDF ((p*a^3+q*b^3)/w) 1 x| < ε := by
    let M := p*a^3+q*b^3
    let P := fun w => normalizedLaw w p q a b
    let qD := fun w => StatLean.HypothesisTesting.edgeworthDensity (M/w) 1
    let f := fun w u => ‖scaledError p q a b w u‖/|u|
    let j := fun w ξ =>
      ‖charFun (P w) (-(2*Real.pi*ξ))-charFunDensity (qD w) (-(2*Real.pi*ξ))‖ /
        (Real.pi*|ξ|)
    have hprob (w : ℝ) : IsProbabilityMeasure (P w) := by
      haveI : IsProbabilityMeasure (pairLaw (Real.toNNReal (w^2*p))
          (Real.toNNReal (w^2*q)) a b) := by
        unfold pairLaw
        exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
      haveI : IsProbabilityMeasure (centeredLaw (w^2) p q a b) :=
        Measure.isProbabilityMeasure_map (by fun_prop)
      exact Measure.isProbabilityMeasure_map (by fun_prop)
    have hexpr (w u : ℝ) : charFun (P w) u-charFunDensity (qD w) u =
        scaledError p q a b w u := by
      have hfun : (fun z : ℝ => z/w) = (fun z => w⁻¹*z) := by funext z; ring
      dsimp only [P, normalizedLaw, qD]
      rw [hfun, charFun_map_mul_comp (by fun_prop),
        StatLean.HypothesisTesting.charFunDensity_edgeworthDensity]
      simp only [Nat.cast_one, Real.sqrt_one, inv_one, mul_one]
      dsimp [scaledError]
      rw [hV]
      have harg : w⁻¹*u=u/w := by ring
      rw [harg]
      simp only [Measure.map_id']
      congr 1
      rw [show -((u:ℂ)^2)/2 = ((-(u^2)/2:ℝ):ℂ) by push_cast; ring,
        ← Complex.ofReal_exp]
      rw [show Complex.I^3 = -Complex.I by norm_num [pow_succ]]
      dsimp [M]
      push_cast
      ring
    have hj (w ξ : ℝ) : j w ξ = 2*f w (2*Real.pi*ξ) := by
      dsimp [j]
      rw [hexpr, scaledError_neg_norm]
      dsimp [f]
      rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos]
      norm_num
      field_simp
    have hjint (w C : ℝ) (hw : 0≤w) (hC : 0<C) :
        IntegrableOn (j w) (Icc (-C*w) (C*w)) := by
      have hB : 0≤C*w := mul_nonneg hC.le hw
      have hπ : 0<2*Real.pi := by positivity
      have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le
        (mul_le_mul_of_nonneg_left (neg_le_self hB) hπ.le)).mpr
          (scaledError_integrable p q a b w ((2*Real.pi)*(-(C*w)))
            ((2*Real.pi)*(C*w)) hp.le hq.le)
      have hit := hi.comp_mul_left (c:=2*Real.pi)
      simp only [mul_div_cancel_left₀ _ hπ.ne'] at hit
      have hi' := (intervalIntegrable_iff_integrableOn_Icc_of_le (neg_le_self hB)).mp hit
      have heq : j w = fun ξ => 2*f w (2*Real.pi*ξ) := funext (hj w)
      rw [heq, neg_mul]
      exact hi'.const_mul 2
    have hintegral (w C : ℝ) (hw : 0≤w) (hC : 0<C) :
        (∫ ξ in Icc (-C*w) (C*w), j w ξ) =
          Real.pi⁻¹ * ∫ u in Icc (-(2*Real.pi*C)*w) ((2*Real.pi*C)*w), f w u := by
      have hB : 0≤C*w := mul_nonneg hC.le hw
      have hπ : 0<2*Real.pi := by positivity
      simp_rw [hj]
      rw [integral_const_mul, neg_mul, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (neg_le_self hB),
        intervalIntegral.integral_comp_mul_left (f w) hπ.ne', smul_eq_mul,
        intervalIntegral.integral_of_le (mul_le_mul_of_nonneg_left (neg_le_self hB) hπ.le),
        ← integral_Icc_eq_integral_Ioc]
      have hleft : 2*Real.pi*-(C*w) = -(2*Real.pi*C)*w := by ring
      have hright : 2*Real.pi*(C*w) = (2*Real.pi*C)*w := by ring
      rw [hleft,hright]
      field_simp
    have hlimit (C : ℝ) (hC : 0<C) :
        Tendsto (fun w : ℝ => w*∫ ξ in Icc (-C*w) (C*w), j w ξ) atTop (𝓝 0) := by
      have hh := (symmetric_cutoff_vanishes p q a b (2*Real.pi*C)
        hp hq hb0 hirr (by positivity)).const_mul Real.pi⁻¹
      simp only [mul_zero] at hh
      apply hh.congr'
      filter_upwards [eventually_ge_atTop (0:ℝ)] with w hw
      rw [hintegral w C hw hC]
      ring
    obtain ⟨H,hH,hSmooth⟩ := generic_finite_smoothing
    let A : ℝ≥0 := ⟨(Real.sqrt (2*Real.pi))⁻¹ * (1+66*|M|), by positivity⟩
    have hqA (w : ℝ) (hw : 1≤w) (x : ℝ) : |qD w x|≤A := by
      have hM : |M/w|≤|M| := by
        rw [abs_div, abs_of_nonneg (zero_le_one.trans hw)]
        exact div_le_self (abs_nonneg M) hw
      have hh := StatLean.HypothesisTesting.abs_edgeworthDensity_le (M/w) (n:=1) (by norm_num) x
      apply hh.trans
      change (Real.sqrt (2*Real.pi))⁻¹*(1+66*|M/w|) ≤
        (Real.sqrt (2*Real.pi))⁻¹*(1+66*|M|)
      gcongr
    have hqint (w : ℝ) : Integrable (qD w) :=
      StatLean.HypothesisTesting.integrable_edgeworthDensity (M/w) 1
    have hLip (w : ℝ) (hw : 1≤w) : LipschitzWith A (densityCDF (qD w)) := by
      have ho (x y : ℝ) (hxy : x≤y) :
          |densityCDF (qD w) y-densityCDF (qD w) x| ≤ (A:ℝ)*(y-x) := by
        have hs : densityCDF (qD w) y-densityCDF (qD w) x = ∫ t in Ioc x y, qD w t := by
          dsimp [densityCDF]
          rw [← Iic_union_Ioc_eq_Iic hxy,
            setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
              (hqint w).integrableOn (hqint w).integrableOn]
          ring
        rw [hs]
        have hh := norm_setIntegral_le_of_norm_le_const (μ:= (volume : Measure ℝ))
          (f:=qD w) (s:=Ioc x y) (by simp [Real.volume_Ioc])
          (fun t _ => by simpa only [Real.norm_eq_abs] using hqA w hw t)
        simpa only [Real.norm_eq_abs, Real.volume_real_Ioc_of_le hxy] using hh
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [Real.dist_eq, Real.dist_eq]
      rcases le_total x y with hxy | hyx
      · rw [abs_sub_comm (densityCDF (qD w) x), abs_of_nonpos (sub_nonpos.mpr hxy)]
        convert ho x y hxy using 1 <;> ring
      · rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
        exact ho y x hyx
    intro ε hε
    let C := 8*(A:ℝ)*H/ε+1
    have hC : 0<C := by dsimp [C]; positivity
    have hrem : 4*(A:ℝ)*H/C<ε/2 := by
      apply (div_lt_iff₀ hC).mpr
      have hCe : C*ε=8*(A:ℝ)*H+ε := by dsimp [C]; field_simp <;> ring
      nlinarith
    have he := (tendsto_order.mp (hlimit C hC)).2 (ε/4) (by positivity)
    filter_upwards [eventually_ge_atTop (1:ℝ), he] with w hw hew
    intro x
    have hw0 : 0<w := zero_lt_one.trans_le hw
    haveI := hprob w
    have hh := hSmooth (P w) (qD w) (hqint w) A (hqA w hw) (hLip w hw)
      (C*w) (by positivity) (by simpa only [neg_mul] using hjint w C hw0.le hC) x
    rw [StatLean.HypothesisTesting.densityCDF_edgeworthDensity] at hh
    have hm := mul_le_mul_of_nonneg_left hh hw0.le
    have heq : w*(2*(∫ ξ in Icc (-(C*w)) (C*w), j w ξ)+4*(A:ℝ)*H/(C*w)) =
        2*(w*∫ ξ in Icc (-C*w) (C*w), j w ξ)+4*(A:ℝ)*H/C := by
      rw [neg_mul]
      field_simp
      <;> ring
    change w*|(P w).real (Iic x)-StatLean.HypothesisTesting.edgeworthCDF (M/w) 1 x| < ε
    change w*|(P w).real (Iic x)-StatLean.HypothesisTesting.edgeworthCDF (M/w) 1 x| ≤
      w*(2*(∫ ξ in Icc (-(C*w)) (C*w), j w ξ)+4*(A:ℝ)*H/(C*w)) at hm
    rw [heq] at hm
    linarith

  have general_rate_uniform_edgeworth (p q a b : ℝ) (hp : 0<p) (hq : 0<q)
      (hb : b≠0) (hirr : Irrational (a/b)) :
      ∀ ε : ℝ, 0<ε → ∀ᶠ lam : ℝ in atTop, ∀ x : ℝ,
        Real.sqrt lam*|rateCDF lam p q a b x-rateEdgeworthCDF lam p q a b x| < ε := by
    let V := p*a^2+q*b^2
    let σ := Real.sqrt V
    have hV : 0<V := add_pos_of_nonneg_of_pos (mul_nonneg hp.le (sq_nonneg _))
      (mul_pos hq (sq_pos_of_ne_zero hb))
    have hσ : 0<σ := Real.sqrt_pos.mpr hV
    have hσ2 : σ^2=V := Real.sq_sqrt hV.le
    have hσ3 : σ^3=Real.rpow V (3/2:ℝ) := by
      dsimp [σ]
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hV.le]
      norm_num
    have hbn : b/σ≠0 := div_ne_zero hb hσ.ne'
    have hirrn : Irrational ((a/σ)/(b/σ)) := by
      have heq : (a/σ)/(b/σ)=a/b := by field_simp
      rw [heq]
      exact hirr
    have hVn : p*(a/σ)^2+q*(b/σ)^2=1 := by
      field_simp
      nlinarith only [hσ2]
    have hMn : p*(a/σ)^3+q*(b/σ)^3=(p*a^3+q*b^3)/σ^3 := by ring
    have hmap (lam : ℝ) (hlam : 0≤lam) :
        normalizedLaw (Real.sqrt lam) p q (a/σ) (b/σ) =
          (rateCountLaw lam p q).map (rateScore lam p q a b) := by
      dsimp only [normalizedLaw, centeredLaw, pairLaw, rateCountLaw]
      rw [Real.sq_sqrt hlam, Measure.map_map (by fun_prop) (by fun_prop),
        Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext n
      dsimp [Function.comp_def,rateScore]
      rw [Real.sqrt_mul hlam]
      change ((a/σ)*(n.1:ℝ)+(b/σ)*(n.2:ℝ)-lam*(p*(a/σ)+q*(b/σ)))/Real.sqrt lam =
        (a*(n.1:ℝ)+b*(n.2:ℝ)-lam*(p*a+q*b))/(Real.sqrt lam*σ)
      ring
    have hcdf (lam : ℝ) (hlam : 0≤lam) (x : ℝ) :
        (normalizedLaw (Real.sqrt lam) p q (a/σ) (b/σ)).real (Iic x) =
          rateCDF lam p q a b x := by
      rw [hmap lam hlam]
      simp only [Measure.real, Measure.map_apply (measurable_of_countable _) measurableSet_Iic,
        rateCDF]
      rfl
    have hcorr (lam x : ℝ) :
        StatLean.HypothesisTesting.edgeworthCDF
          ((p*(a/σ)^3+q*(b/σ)^3)/Real.sqrt lam) 1 x = rateEdgeworthCDF lam p q a b x := by
      rw [hMn,hσ3]
      simp only [StatLean.HypothesisTesting.edgeworthCDF,
        StatLean.HypothesisTesting.stdNormalCDF, StatLean.HypothesisTesting.normalCDF,
        StatLean.HypothesisTesting.stdNormalPDF_eq_gaussianPDFReal,
        Nat.cast_one, Real.sqrt_one, inv_one, mul_one]
      dsimp [rateEdgeworthCDF, V, Measure.real]
      ring
    intro ε hε
    have hh := Real.tendsto_sqrt_atTop.eventually
      (normalized_uniform_edgeworth p q (a/σ) (b/σ) hp hq hbn hirrn hVn ε hε)
    filter_upwards [eventually_ge_atTop (0:ℝ),hh] with lam hlam hh
    intro x
    simpa only [hcdf lam hlam x,hcorr lam x] using hh x

  have local_limit_of_edgeworth (F : ℝ → ℝ → ℝ) (κ : ℝ)
      (hF : ∀ ε : ℝ, 0<ε → ∀ᶠ w : ℝ in atTop, ∀ x : ℝ,
        w*|F w x-StatLean.HypothesisTesting.edgeworthCDF (κ/w) 1 x|<ε)
      (d : ℝ) (hd : 0<d) :
      ∀ ε : ℝ, 0<ε → ∀ᶠ w : ℝ in atTop, ∀ x : ℝ,
        |w*(F w (x+d/w)-F w x)-d*stdNormalPDF x|<ε := by
    let φ := stdNormalPDF
    let ψ := fun x : ℝ => φ x*(1-x^2)
    have hφzero : Tendsto φ (cocompact ℝ) (𝓝 0) := by
      have hh := (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact (a:=1/2)
        (by norm_num) 0).div_const (Real.sqrt (2*Real.pi))
      convert hh using 1
      · funext x
        simp only [Real.rpow_zero,one_mul]
        dsimp [φ,stdNormalPDF]
        congr 2
        ring
      · simp
    have hφ2zero : Tendsto (fun x : ℝ => φ x*x^2) (cocompact ℝ) (𝓝 0) := by
      have hh := (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact (a:=1/2)
        (by norm_num) 2).div_const (Real.sqrt (2*Real.pi))
      convert hh using 1
      · funext x
        rw [show (2:ℝ)=((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, sq_abs]
        dsimp [φ,stdNormalPDF]
        rw [show -(1/2:ℝ)*x^2 = -x^2/2 by ring]
        ring
      · simp
    have hψzero : Tendsto ψ (cocompact ℝ) (𝓝 0) := by
      convert hφzero.sub hφ2zero using 1
      · funext x; dsimp [ψ]; ring
      · simp
    have hφuc : UniformContinuous φ :=
      continuous_stdNormalPDF.uniformContinuous_of_tendsto_cocompact hφzero
    have hψcont : Continuous ψ :=
      continuous_stdNormalPDF.mul (continuous_const.sub (continuous_id.pow 2))
    have hψuc : UniformContinuous ψ := hψcont.uniformContinuous_of_tendsto_cocompact hψzero
    have hG (w x : ℝ) : StatLean.HypothesisTesting.edgeworthCDF (κ/w) 1 x =
        stdNormalCDF x+κ/(6*w)*ψ x := by
      simp only [StatLean.HypothesisTesting.edgeworthCDF, Nat.cast_one,
        Real.sqrt_one, inv_one, mul_one]
      dsimp [ψ,φ]
      ring
    intro ε hε
    let η := ε/(8*(d+|κ|+1))
    have hη : 0<η := by dsimp [η]; positivity
    have hbudget : (2*d+|κ|)*η<ε/2 := by
      have heq : η*(8*(d+|κ|+1))=ε := by dsimp [η]; field_simp
      nlinarith [abs_nonneg κ]
    obtain ⟨δ₁,hδ₁,hφmod⟩ := Metric.uniformContinuous_iff.mp hφuc η hη
    obtain ⟨δ₂,hδ₂,hψmod⟩ := Metric.uniformContinuous_iff.mp hψuc η hη
    have hstep : Tendsto (fun w : ℝ => d/w) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv,mul_zero] using tendsto_inv_atTop_zero.const_mul d
    have he1 := (tendsto_order.mp hstep).2 δ₁ hδ₁
    have he2 := (tendsto_order.mp hstep).2 δ₂ hδ₂
    filter_upwards [eventually_ge_atTop (1:ℝ),hF (ε/4) (by positivity),he1,he2]
      with w hw hFw hstep1 hstep2
    intro x
    have hw0 : 0<w := zero_lt_one.trans_le hw
    let y := x+d/w
    have hxy : x≤y := by
      have hh : 0≤d/w := by positivity
      dsimp [y]
      linarith
    have hydiff : y-x=d/w := by dsimp [y]; ring
    have hφint : IntegrableOn φ (Ioc x y) := integrable_stdNormalPDF.integrableOn
    have hcint : IntegrableOn (fun _ : ℝ => φ x) (Ioc x y) :=
      (continuousOn_const.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have hPhiDiff : stdNormalCDF y-stdNormalCDF x=∫ t in Ioc x y, φ t := by
      simp only [stdNormalCDF_eq_setIntegral]
      rw [← Iic_union_Ioc_eq_Iic hxy,
        setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
          integrable_stdNormalPDF.integrableOn integrable_stdNormalPDF.integrableOn]
      ring
    have hdiff : (∫ t in Ioc x y, φ t-φ x) =
        stdNormalCDF y-stdNormalCDF x-(d/w)*φ x := by
      rw [integral_sub hφint hcint, ← hPhiDiff, setIntegral_const,
        Real.volume_real_Ioc_of_le hxy, smul_eq_mul,hydiff]
    have hbound : |∫ t in Ioc x y, φ t-φ x|≤η*(d/w) := by
      have hh := norm_setIntegral_le_of_norm_le_const (μ:=(volume:Measure ℝ))
        (s:=Ioc x y) (f:=fun t => φ t-φ x) (C:=η) (by simp [Real.volume_Ioc]) (by
          intro t ht
          have htx : dist t x<δ₁ := by
            rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1.le)]
            linarith [ht.2]
          simpa only [Real.dist_eq, Real.norm_eq_abs] using (hφmod htx).le)
      simpa only [Real.norm_eq_abs, Real.volume_real_Ioc_of_le hxy,hydiff] using hh
    have hψbound : |ψ y-ψ x|<η := by
      apply hψmod
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxy),hydiff]
      exact hstep2
    have heq : w*(F w y-F w x)-d*φ x =
        w*(F w y-StatLean.HypothesisTesting.edgeworthCDF (κ/w) 1 y)-
        w*(F w x-StatLean.HypothesisTesting.edgeworthCDF (κ/w) 1 x)+
        w*(∫ t in Ioc x y, φ t-φ x)+κ/6*(ψ y-ψ x) := by
      rw [hdiff,hG,hG]
      field_simp
      <;> ring
    rw [show x+d/w=y from rfl,heq]
    have h1 := hFw y
    have h2 := hFw x
    have h3 : w*|∫ t in Ioc x y, φ t-φ x|≤η*d := by
      have hh := mul_le_mul_of_nonneg_left hbound hw0.le
      calc
        _ ≤ w*(η*(d/w)) := hh
        _ = η*d := by field_simp <;> ring
    have h4 : |κ/6*(ψ y-ψ x)|≤|κ| *η := by
      rw [abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℝ)<6)]
      have hh := mul_le_mul_of_nonneg_left hψbound.le (abs_nonneg κ)
      have hn := mul_nonneg (abs_nonneg κ) (abs_nonneg (ψ y-ψ x))
      nlinarith
    calc
      _ ≤ |w*(F w y-StatLean.HypothesisTesting.edgeworthCDF (κ/w) 1 y)|+
          |w*(F w x-StatLean.HypothesisTesting.edgeworthCDF (κ/w) 1 x)|+
          |w*(∫ t in Ioc x y, φ t-φ x)|+|κ/6*(ψ y-ψ x)| := by
        exact (abs_add_le _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)) le_rfl)
      _ < ε := by
        simp only [abs_mul,abs_of_pos hw0] at h4 ⊢
        nlinarith [abs_nonneg κ]

  have general_rate_interval_local_limit (p q a b : ℝ) (hp : 0<p) (hq : 0<q)
      (hb : b≠0) (hirr : Irrational (a/b)) (h : ℝ) (hh : 0<h) :
      ∀ ε : ℝ, 0<ε → ∀ᶠ lam : ℝ in atTop, ∀ y : ℝ,
        |Real.sqrt lam*(rateCountLaw lam p q).real
          {n | y<a*(n.1:ℝ)+b*(n.2:ℝ) ∧ a*(n.1:ℝ)+b*(n.2:ℝ)≤y+h} -
          (h/Real.sqrt (p*a^2+q*b^2))*gaussianPDFReal 0 1
            ((y-lam*(p*a+q*b))/Real.sqrt (lam*(p*a^2+q*b^2)))|<ε := by
    let V := p*a^2+q*b^2
    let σ := Real.sqrt V
    let κ := (p*a^3+q*b^3)/Real.rpow V (3/2:ℝ)
    let F := fun w x => rateCDF (w^2) p q a b x
    have hV : 0<V := add_pos_of_nonneg_of_pos (mul_nonneg hp.le (sq_nonneg _))
      (mul_pos hq (sq_pos_of_ne_zero hb))
    have hσ : 0<σ := Real.sqrt_pos.mpr hV
    have hcorr (w x : ℝ) (hw : 0≤w) :
        rateEdgeworthCDF (w^2) p q a b x =
        StatLean.HypothesisTesting.edgeworthCDF (κ/w) 1 x := by
      simp only [rateEdgeworthCDF, Real.sqrt_sq hw,
        StatLean.HypothesisTesting.edgeworthCDF,
        StatLean.HypothesisTesting.stdNormalCDF, StatLean.HypothesisTesting.normalCDF,
        StatLean.HypothesisTesting.stdNormalPDF_eq_gaussianPDFReal,
        Nat.cast_one,Real.sqrt_one,inv_one,mul_one]
      dsimp [κ,V,Measure.real]
      ring
    have hF : ∀ ε : ℝ, 0<ε → ∀ᶠ w : ℝ in atTop, ∀ x : ℝ,
        w*|F w x-StatLean.HypothesisTesting.edgeworthCDF (κ/w) 1 x|<ε := by
      intro ε hε
      have he := (tendsto_pow_atTop (by decide : (2:ℕ)≠0)).eventually
        (general_rate_uniform_edgeworth p q a b hp hq hb hirr ε hε)
      filter_upwards [eventually_ge_atTop (0:ℝ),he] with w hw he x
      simpa only [Real.sqrt_sq hw,hcorr w x hw] using he x
    intro ε hε
    have hi := Real.tendsto_sqrt_atTop.eventually
      (local_limit_of_edgeworth F κ hF (h/σ) (by positivity) ε hε)
    filter_upwards [eventually_ge_atTop (1:ℝ),hi] with lam hlam hi
    intro y
    have hlam0 : 0<lam := zero_lt_one.trans_le hlam
    have hw : 0<Real.sqrt lam := Real.sqrt_pos.mpr hlam0
    have hden : Real.sqrt (lam*V)=Real.sqrt lam*σ := Real.sqrt_mul hlam0.le V
    have hdenpos : 0<Real.sqrt (lam*V) := Real.sqrt_pos.mpr (mul_pos hlam0 hV)
    let x := (y-lam*(p*a+q*b))/Real.sqrt (lam*V)
    let z := x+(h/σ)/Real.sqrt lam
    have hxz : x≤z := by
      have hn : 0≤(h/σ)/Real.sqrt lam := by positivity
      dsimp [z]
      linarith
    let μ := (rateCountLaw lam p q).map (rateScore lam p q a b)
    haveI : IsProbabilityMeasure (rateCountLaw lam p q) := by dsimp [rateCountLaw]; infer_instance
    haveI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
    have hCDF (t : ℝ) : μ.real (Iic t)=rateCDF lam p q a b t := by
      simp only [μ,Measure.real,Measure.map_apply (measurable_of_countable _) measurableSet_Iic,rateCDF]
      rfl
    have hdiff : rateCDF lam p q a b z-rateCDF lam p q a b x=μ.real (Ioc x z) := by
      have heq : μ.real (Iic z)=μ.real (Iic x)+μ.real (Ioc x z) := by
        rw [← Iic_union_Ioc_eq_Iic hxz,
          measureReal_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc]
      rw [hCDF,hCDF] at heq
      linarith
    have hz : z=(y+h-lam*(p*a+q*b))/Real.sqrt (lam*V) := by
      dsimp [z,x]
      rw [hden]
      field_simp
      <;> ring
    have hinter : μ.real (Ioc x z)=(rateCountLaw lam p q).real
        {n | y<a*(n.1:ℝ)+b*(n.2:ℝ) ∧ a*(n.1:ℝ)+b*(n.2:ℝ)≤y+h} := by
      simp only [μ,Measure.real,Measure.map_apply (measurable_of_countable _) measurableSet_Ioc]
      congr 2
      ext n
      change (x<rateScore lam p q a b n ∧ rateScore lam p q a b n≤z) ↔ _
      rw [hz]
      dsimp [x,rateScore]
      change ((y-lam*(p*a+q*b))/Real.sqrt (lam*V) <
        (a*(n.1:ℝ)+b*(n.2:ℝ)-lam*(p*a+q*b))/Real.sqrt (lam*V) ∧
        (a*(n.1:ℝ)+b*(n.2:ℝ)-lam*(p*a+q*b))/Real.sqrt (lam*V)≤
        (y+h-lam*(p*a+q*b))/Real.sqrt (lam*V)) ↔ _
      rw [div_lt_div_iff_of_pos_right hdenpos,div_le_div_iff_of_pos_right hdenpos]
      constructor <;> intro hn <;> constructor <;> linarith [hn.1,hn.2]
    have hhx := hi x
    dsimp only [F] at hhx
    rw [Real.sq_sqrt hlam0.le] at hhx
    change |Real.sqrt lam*(rateCDF lam p q a b z-rateCDF lam p q a b x)-
      (h/σ)*stdNormalPDF x|<ε at hhx
    rw [hdiff,hinter,stdNormalPDF_eq_gaussianPDFReal] at hhx
    exact hhx

  have atom_bound_of_continuous_comparison (μ : Measure ℝ) [IsProbabilityMeasure μ]
      (G : ℝ → ℝ) (hG : Continuous G) (e : ℝ)
      (h : ∀ x : ℝ, |μ.real (Iic x)-G x|≤e) (x : ℝ) : μ.real {x}≤2*e := by
    apply le_of_forall_pos_le_add
    intro η hη
    obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp (hG.continuousAt (x:=x)) η hη
    let y := x-δ/2
    have hyx : y<x := by dsimp [y]; linarith
    have hdist : dist y x<δ := by
      rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hyx)]
      dsimp [y]
      linarith
    have hGy : |G y-G x|<η := by simpa only [Real.dist_eq] using hclose hdist
    have hsub : μ.real {x}≤μ.real (Ioc y x) := measureReal_mono (by
      intro z hz
      have hz' : z=x := by simpa using hz
      subst z
      exact ⟨hyx,le_rfl⟩)
    have hsplit : μ.real (Iic x)=μ.real (Iic y)+μ.real (Ioc y x) := by
      rw [← Iic_union_Ioc_eq_Iic hyx.le,
        measureReal_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc]
    have hx := (abs_le.mp (h x)).2
    have hy := (abs_le.mp (h y)).1
    have hGxy := (abs_lt.mp hGy).1
    linarith

  have general_rate_atom_vanishes (p q a b : ℝ) (hp : 0<p) (hq : 0<q)
      (hb : b≠0) (hirr : Irrational (a/b)) :
      ∀ ε : ℝ, 0<ε → ∀ᶠ lam : ℝ in atTop, ∀ x : ℝ,
        Real.sqrt lam*(rateCountLaw lam p q).real {n | rateScore lam p q a b n=x}<ε := by
    intro ε hε
    have hh := general_rate_uniform_edgeworth p q a b hp hq hb hirr (ε/4) (by positivity)
    filter_upwards [eventually_ge_atTop (1:ℝ),hh] with lam hlam hh
    intro x
    let μ := (rateCountLaw lam p q).map (rateScore lam p q a b)
    haveI : IsProbabilityMeasure (rateCountLaw lam p q) := by dsimp [rateCountLaw]; infer_instance
    haveI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
    have hw : 0<Real.sqrt lam := Real.sqrt_pos.mpr (zero_lt_one.trans_le hlam)
    have hG : Continuous (rateEdgeworthCDF lam p q a b) := by
      have hc : Continuous (fun x : ℝ => (gaussianReal 0 1).real (Iic x)) := by
        have heq : (fun x : ℝ => (gaussianReal 0 1).real (Iic x)) =
            StatLean.HypothesisTesting.stdNormalCDF := rfl
        rw [heq]
        change Continuous (fun x => StatLean.HypothesisTesting.stdNormalCDF x)
        simp_rw [StatLean.HypothesisTesting.stdNormalCDF_eq_setIntegral]
        apply continuous_iff_continuousAt.mpr
        intro x
        have hon : ContinuousOn (fun t : ℝ => ∫ u in Iic t, StatLean.HypothesisTesting.stdNormalPDF u) (Iic (x+1)) :=
          StatLean.HypothesisTesting.integrable_stdNormalPDF.integrableOn.continuousOn_Iic_primitive_Iic
        exact hon.continuousAt (Iic_mem_nhds (by linarith))
      have hpdf : Continuous (gaussianPDFReal 0 1) := by
        have ht := StatLean.HypothesisTesting.continuous_stdNormalPDF
        change Continuous (fun x => StatLean.HypothesisTesting.stdNormalPDF x) at ht
        simpa only [StatLean.HypothesisTesting.stdNormalPDF_eq_gaussianPDFReal] using ht
      change Continuous (fun x => rateEdgeworthCDF lam p q a b x)
      dsimp [rateEdgeworthCDF]
      fun_prop
    have hCDF (z : ℝ) : μ.real (Iic z)=rateCDF lam p q a b z := by
      simp only [μ,Measure.real,Measure.map_apply (measurable_of_countable _) measurableSet_Iic,rateCDF]
      rfl
    have hbound := atom_bound_of_continuous_comparison μ (rateEdgeworthCDF lam p q a b) hG
      (ε/(4*Real.sqrt lam)) (by
        intro z
        rw [hCDF]
        have hh' := hh z
        rw [mul_comm] at hh'
        have hz := (lt_div_iff₀ hw).mpr hh'
        calc
          _ ≤ (ε/4)/Real.sqrt lam := hz.le
          _ = ε/(4*Real.sqrt lam) := by ring) x
    have hx : μ.real {x}=(rateCountLaw lam p q).real {n | rateScore lam p q a b n=x} := by
      simp only [μ,Measure.real,Measure.map_apply (measurable_of_countable _) (measurableSet_singleton x)]
      rfl
    rw [hx] at hbound
    have hm := mul_le_mul_of_nonneg_left hbound hw.le
    have heq : Real.sqrt lam*(2*(ε/(4*Real.sqrt lam)))=ε/2 := by field_simp <;> norm_num
    rw [heq] at hm
    linarith

  exact ⟨general_rate_uniform_edgeworth p q a b hp hq hb hirr,
    fun h hh => general_rate_interval_local_limit p q a b hp hq hb hirr h hh,
    general_rate_atom_vanishes p q a b hp hq hb hirr⟩

end CompoundPoissonEdgeworthProposal
end
