/- GID: D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworthCutoff
   generality: G
   mirror-B: D5/B/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworthCutoff
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Irrational two-jump damping controls the symmetric moving-cutoff Fourier error. -/

import D5.S3.TotalVariation.Asymptotics.CompoundPoissonEdgeworthFoundation

open MeasureTheory ProbabilityTheory Set Filter Convolution
open scoped FourierTransform Real NNReal ENNReal Topology BigOperators
noncomputable section
namespace CompoundPoissonEdgeworthProposal
open CompoundPoissonEdgeworth
open StatLean.HypothesisTesting hiding edgeworthCDF

def scaledError (p q a b w u : ℝ) : ℂ :=
  charFun (centeredLaw (w^2) p q a b) (u/w) -
    (Real.exp (-(p*a^2+q*b^2)*u^2/2):ℂ)*
      (1+((p*a^3+q*b^3)*u^3/(6*w):ℝ)*Complex.I^3)

def normalizedLaw (w p q a b : ℝ) : Measure ℝ :=
  (centeredLaw (w^2) p q a b).map (fun z => z/w)

def rateCountLaw (lam p q : ℝ) : Measure (ℕ × ℕ) :=
  (poissonMeasure (Real.toNNReal (lam*p))).prod (poissonMeasure (Real.toNNReal (lam*q)))

def rateScore (lam p q a b : ℝ) (n : ℕ × ℕ) : ℝ :=
  (a*(n.1:ℝ)+b*(n.2:ℝ)-lam*(p*a+q*b))/Real.sqrt (lam*(p*a^2+q*b^2))

def rateCDF (lam p q a b x : ℝ) : ℝ :=
  (rateCountLaw lam p q).real {n | rateScore lam p q a b n≤x}

def rateEdgeworthCDF (lam p q a b x : ℝ) : ℝ :=
  (gaussianReal 0 1).real (Iic x)+gaussianPDFReal 0 1 x*(p*a^3+q*b^3)*(1-x^2)/
    (6*Real.rpow (p*a^2+q*b^2) (3/2:ℝ)*Real.sqrt lam)

/-- For every fixed positive cutoff, the symmetric Fourier error is little-o of inverse square-root time. -/
theorem symmetric_cutoff_vanishes (p q a b C : ℝ) (hp : 0<p) (hq : 0<q)
    (hb0 : b ≠ 0) (hirr : Irrational (a/b)) (hC : 0<C) :
    Tendsto (fun w : ℝ => w * ∫ u in Icc (-C*w) (C*w),
      ‖scaledError p q a b w u‖/|u|) atTop (𝓝 0) := by
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

  have pair_charFun_norm (p q : ℝ≥0) (a b t : ℝ) :
      ‖charFun (pairLaw p q a b) t‖ = Real.exp (-damping p q a b t) := by
    rw [pair_charFun,Complex.norm_exp]
    congr 1
    simp only [Complex.add_re,Complex.mul_re,Complex.sub_re,Complex.one_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.exp_ofReal_mul_I_re]
    dsimp [damping]
    ring

  have damping_pos (p q a b : ℝ) (hp : 0<p) (hq : 0<q)
      (hb : b ≠ 0) (hirr : Irrational (a/b)) {t : ℝ} (ht : t ≠ 0) :
      0 < damping p q a b t := by
    have h1 : 0 ≤ 1-Real.cos (t*a) := sub_nonneg.mpr (Real.cos_le_one _)
    have h2 : 0 ≤ 1-Real.cos (t*b) := sub_nonneg.mpr (Real.cos_le_one _)
    have hnonneg : 0 ≤ damping p q a b t := add_nonneg (mul_nonneg hp.le h1) (mul_nonneg hq.le h2)
    apply lt_of_le_of_ne hnonneg
    intro hz
    have hsum : p*(1-Real.cos (t*a))+q*(1-Real.cos (t*b))=0 := hz.symm
    have hc1 : Real.cos (t*a)=1 := by
      have h := (add_eq_zero_iff_of_nonneg (mul_nonneg hp.le h1) (mul_nonneg hq.le h2)).mp hsum
      have := (mul_eq_zero.mp h.1).resolve_left hp.ne'
      linarith only [this]
    have hc2 : Real.cos (t*b)=1 := by
      have h := (add_eq_zero_iff_of_nonneg (mul_nonneg hp.le h1) (mul_nonneg hq.le h2)).mp hsum
      have := (mul_eq_zero.mp h.2).resolve_left hq.ne'
      linarith only [this]
    obtain ⟨m,hm⟩ := (Real.cos_eq_one_iff _).mp hc1
    obtain ⟨n,hn⟩ := (Real.cos_eq_one_iff _).mp hc2
    have hn0 : (n:ℝ) ≠ 0 := by
      intro h
      rw [h,zero_mul] at hn
      exact (mul_ne_zero ht hb) hn.symm
    apply hirr.ne_rational m n
    apply (div_eq_div_iff hb hn0).mpr
    have hpi : 2*Real.pi ≠ 0 := by positivity
    have hc : (t*a)*((n:ℝ)*(2*Real.pi)) = (t*b)*((m:ℝ)*(2*Real.pi)) := by rw [hm,hn]; ring
    have hh : t*(2*Real.pi)*(a*(n:ℝ)-b*(m:ℝ))=0 := by nlinarith only [hc]
    have := (mul_eq_zero.mp hh).resolve_left (mul_ne_zero ht hpi)
    linarith only [this]

  have nonlattice_annulus_decay (p q a b : ℝ) (hp : 0<p) (hq : 0<q)
      (hb : b ≠ 0) (hirr : Irrational (a/b)) (eta C : ℝ) (heta : 0<eta) :
      ∃ c : ℝ, 0<c ∧ ∀ lam : ℝ, 0≤lam → ∀ t : ℝ, eta≤|t| → |t|≤C →
        ‖charFun (pairLaw (Real.toNNReal (lam*p)) (Real.toNNReal (lam*q)) a b) t‖ ≤
          Real.exp (-c*lam) := by
    let K := {t : ℝ | eta≤|t| ∧ |t|≤C}
    have hKclosed : IsClosed K :=
      (isClosed_le continuous_const continuous_abs).inter
        (isClosed_le continuous_abs continuous_const)
    have hK : IsCompact K := isCompact_Icc.of_isClosed_subset hKclosed (by
      intro t ht
      exact abs_le.mp ht.2)
    have hc : Continuous (damping p q a b) := by unfold damping; fun_prop
    obtain ⟨c,hcpos,hclower⟩ := hK.exists_forall_le' hc.continuousOn (a:=0) (by
      intro t ht
      apply damping_pos p q a b hp hq hb hirr
      intro hz
      have := ht.1
      simp only [hz,abs_zero] at this
      linarith only [this,heta])
    refine ⟨c,hcpos,?_⟩
    intro lam hlam t hteta htC
    have hpmean : (Real.toNNReal (lam*p):ℝ)=lam*p := Real.coe_toNNReal _ (mul_nonneg hlam hp.le)
    have hqmean : (Real.toNNReal (lam*q):ℝ)=lam*q := Real.coe_toNNReal _ (mul_nonneg hlam hq.le)
    rw [pair_charFun_norm]
    have hdamp : damping (Real.toNNReal (lam*p)) (Real.toNNReal (lam*q)) a b t =
        lam*damping p q a b t := by simp only [damping,hpmean,hqmean]; ring
    rw [hdamp]
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left (hclower t ⟨hteta,htC⟩) hlam
    linarith only [this]

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

  have annulus_integral_vanishes (p q a b : ℝ) (hp : 0<p) (hq : 0<q)
      (hb : b ≠ 0) (hirr : Irrational (a/b)) (eta C : ℝ) (heta : 0<eta) :
      Tendsto (fun lam : ℝ => Real.sqrt lam *
        ∫ t in Icc eta C,
          ‖charFun (pairLaw (Real.toNNReal (lam*p)) (Real.toNNReal (lam*q)) a b) t‖/t)
        atTop (𝓝 0) := by
    obtain ⟨c,hc,hdecay⟩ := nonlattice_annulus_decay p q a b hp hq hb hirr eta C heta
    let f := fun lam t =>
      ‖charFun (pairLaw (Real.toNNReal (lam*p)) (Real.toNNReal (lam*q)) a b) t‖/t
    have hint (lam : ℝ) : IntegrableOn (f lam) (Icc eta C) := by
      have hcont : Continuous (fun t =>
          ‖charFun (pairLaw (Real.toNNReal (lam*p)) (Real.toNNReal (lam*q)) a b) t‖) := by
        simp_rw [pair_charFun]
        fun_prop
      exact (hcont.continuousOn.div continuousOn_id
        (fun t ht => ne_of_gt (heta.trans_le ht.1))).integrableOn_compact isCompact_Icc
    have hnonneg (lam : ℝ) : 0 ≤ ∫ t in Icc eta C, f lam t := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact div_nonneg (norm_nonneg _) (heta.le.trans ht.1)
    have hupper (lam : ℝ) (hlam : 0≤lam) :
        (∫ t in Icc eta C, f lam t) ≤ volume.real (Icc eta C) * (Real.exp (-c*lam)/eta) := by
      have hh := setIntegral_mono_on (hint lam)
        (continuousOn_const.integrableOn_compact (μ:=volume) isCompact_Icc)
        measurableSet_Icc (fun t ht => show f lam t ≤ Real.exp (-c*lam)/eta from by
          have htpos := heta.trans_le ht.1
          have hbound := hdecay lam hlam t (by simpa only [abs_of_pos htpos] using ht.1) (by simpa only [abs_of_pos htpos] using ht.2)
          exact (div_le_div_of_nonneg_right hbound htpos.le).trans
            (div_le_div_of_nonneg_left (Real.exp_pos _).le heta ht.1))
      simpa only [setIntegral_const,smul_eq_mul] using hh
    have hexp : Tendsto (fun lam : ℝ => Real.sqrt lam*Real.exp (-c*lam)) atTop (𝓝 0) := by
      simpa only [Real.sqrt_eq_rpow] using
        tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1/2:ℝ) c hc
    have hlim : Tendsto (fun lam : ℝ => Real.sqrt lam *
        (volume.real (Icc eta C) * (Real.exp (-c*lam)/eta))) atTop (𝓝 0) := by
      convert hexp.const_mul (volume.real (Icc eta C)/eta) using 1
      · funext lam; ring
      · simp
    apply squeeze_zero'
      (Filter.Eventually.of_forall (fun lam => mul_nonneg (Real.sqrt_nonneg _) (hnonneg lam)))
      (Filter.Eventually.mono (eventually_ge_atTop (0:ℝ)) (fun lam hlam =>
        mul_le_mul_of_nonneg_left (hupper lam hlam) (Real.sqrt_nonneg _))) hlim

  have gaussian_correction_tail (V M δ C : ℝ) (hV : 0<V) (hδ : 0<δ) :
      Tendsto (fun w : ℝ => w * ∫ u in Icc (δ*w) (C*w),
        Real.exp (-V*u^2/2)*(1+|M| *u^3/(6*w))/u) atTop (𝓝 0) := by
    let g := fun u : ℝ => ‖Real.exp (-V*u^2/2)*(1+|M| *u^3/6)‖
    let f := fun w u : ℝ => Real.exp (-V*u^2/2)*(1+|M| *u^3/(6*w))/u
    have hg : Integrable g := by
      have h0 := integrable_exp_neg_mul_sq (show 0<V/2 by positivity)
      have h3 := integrable_rpow_mul_exp_neg_mul_sq (show 0<V/2 by positivity)
        (s:=((3:ℕ):ℝ)) (by norm_num)
      have hh := (h0.add (h3.mul_const (|M|/6))).norm
      convert hh using 1
      funext u
      simp only [Real.rpow_natCast, Pi.add_apply] at *
      dsimp only [g]
      congr 1
      ring_nf
    have hg0 (u : ℝ) : 0≤g u := norm_nonneg _
    have hpoint (w u : ℝ) (hw : 1≤w) (hu : δ*w≤u) :
        0≤w*f w u ∧ w*f w u≤g u/δ := by
      have hw0 : 0<w := lt_of_lt_of_le zero_lt_one hw
      have hu0 : 0<u := (mul_pos hδ hw0).trans_le hu
      have hgform : g u=Real.exp (-V*u^2/2)*(1+|M| *u^3/6) := by
        dsimp [g]
        rw [abs_of_nonneg (by positivity)]
      have hcoeff : |M| *u^3/(6*w)≤|M| *u^3/6 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
      have hratio : w/u≤1/δ := (div_le_div_iff₀ hu0 hδ).mpr (by simpa [mul_comm] using hu)
      dsimp [f]
      constructor
      · positivity
      · rw [hgform]
        calc
          w*(Real.exp (-V*u^2/2)*(1+|M| *u^3/(6*w))/u) =
            (w/u)*(Real.exp (-V*u^2/2)*(1+|M| *u^3/(6*w))) := by ring
          _ ≤ (1/δ)*(Real.exp (-V*u^2/2)*(1+|M| *u^3/6)) :=
            mul_le_mul hratio (mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le)
              (by positivity) (by positivity)
          _ = _ := by ring
    have hbound (w : ℝ) (hw : 1≤w) :
        0≤w*(∫ u in Icc (δ*w) (C*w), f w u) ∧
        w*(∫ u in Icc (δ*w) (C*w), f w u) ≤
          (∫ u in Ici (δ*w), g u)/δ := by
      have hmeas : AEStronglyMeasurable (fun u => w*f w u) := by
        dsimp [f]
        exact (by fun_prop : Measurable _).aestronglyMeasurable
      have hi : IntegrableOn (fun u => w*f w u) (Icc (δ*w) (C*w)) := by
        apply Integrable.mono' (hg.div_const δ).integrableOn hmeas.restrict
        filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
        rw [Real.norm_of_nonneg (hpoint w u hw hu.1).1]
        exact (hpoint w u hw hu.1).2
      rw [← integral_const_mul]
      constructor
      · apply integral_nonneg_of_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
        exact (hpoint w u hw hu.1).1
      · calc
          _ ≤ ∫ u in Icc (δ*w) (C*w), g u/δ :=
            setIntegral_mono_on hi (hg.div_const δ).integrableOn measurableSet_Icc
              (fun u hu => (hpoint w u hw hu.1).2)
          _ ≤ ∫ u in Ici (δ*w), g u/δ :=
            setIntegral_mono_set (hg.div_const δ).integrableOn
              (Filter.Eventually.of_forall (fun u => div_nonneg (hg0 u) hδ.le))
              (Filter.Eventually.of_forall (fun u hu => hu.1))
          _ = _ := integral_div δ g
    have hlim : Tendsto (fun w : ℝ => (∫ u in Ici (δ*w), g u)/δ) atTop (𝓝 0) := by
      simpa using (tendsto_integral_Ici_zero (f:=g)
        (tendsto_id.const_mul_atTop hδ)).div_const δ
    apply squeeze_zero'
      ((eventually_ge_atTop (1:ℝ)).mono (fun w hw => (hbound w hw).1))
      ((eventually_ge_atTop (1:ℝ)).mono (fun w hw => (hbound w hw).2)) hlim

  have positive_cutoff_vanishes (p q a b δ C : ℝ) (hp : 0<p) (hq : 0<q)
      (hb0 : b ≠ 0) (hirr : Irrational (a/b)) (hV : 0<p*a^2+q*b^2)
      (hδ : 0<δ) (hδC : δ≤C) (ha : δ*|a|≤1) (hb : δ*|b|≤1)
      (habsorb : |p*a^3+q*b^3|/6*δ+(p*a^4+q*b^4)*δ^2 ≤ (p*a^2+q*b^2)/4) :
      Tendsto (fun w : ℝ => w * ∫ u in Icc 0 (C*w), ‖scaledError p q a b w u‖/u)
        atTop (𝓝 0) := by
    let V := p*a^2+q*b^2
    let M := p*a^3+q*b^3
    let f := fun w u => ‖scaledError p q a b w u‖/u
    let g := fun w u => ‖charFun (pairLaw (Real.toNNReal (w^2*p))
      (Real.toNNReal (w^2*q)) a b) (u/w)‖/u
    let k := fun w u => Real.exp (-V*u^2/2)*(1+|M| *u^3/(6*w))/u
    have hfint (w l r : ℝ) (hl : 0≤l) : IntegrableOn (f w) (Icc l r) := by
      have hd : Differentiable ℝ (scaledError p q a b w) := by
        change Differentiable ℝ (fun u => scaledError p q a b w u)
        simp only [scaledError, centered_charFun (w^2) p q a b _ (sq_nonneg _) hp.le hq.le,
          centeredExponent]
        fun_prop
      have hz : scaledError p q a b w 0 = 0 := by
        simp [scaledError, centered_charFun (w^2) p q a b _ (sq_nonneg _) hp.le hq.le,
          centeredExponent]
      have hc : Continuous (dslope (scaledError p q a b w) 0) := by
        apply continuous_iff_continuousAt.mpr
        intro y
        by_cases hy : y=0
        · subst y; exact continuousAt_dslope_same.mpr (hd 0)
        · exact (continuousAt_dslope_of_ne hy).mpr hd.continuous.continuousAt
      apply hc.norm.integrableOn_Icc.congr
      filter_upwards [ae_restrict_mem measurableSet_Icc,
        ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton (0:ℝ)))] with u hu hu0
      have hun : u≠0 := by simpa using hu0
      rw [dslope_of_ne _ hun, slope_def_module, hz, sub_zero, sub_zero,
        norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (hl.trans hu.1)]
      dsimp [f]
      ring
    have hcenter (w t : ℝ) :
        ‖charFun (centeredLaw (w^2) p q a b) t‖ =
        ‖charFun (pairLaw (Real.toNNReal (w^2*p)) (Real.toNNReal (w^2*q)) a b) t‖ := by
      simp only [centeredLaw, sub_eq_add_neg]
      rw [charFun_map_add_const, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    have hpoint (w : ℝ) (hw : 1≤w) (u : ℝ) (hu : δ*w≤u) :
        f w u ≤ g w u+k w u := by
      have hw0 : 0<w := lt_of_lt_of_le zero_lt_one hw
      have hu0 : 0<u := (mul_pos hδ hw0).trans_le hu
      have hn : ‖(1:ℂ)+((M*u^3/(6*w):ℝ):ℂ)*Complex.I^3‖ ≤ 1+|M| *u^3/(6*w) := by
        calc
          _ ≤ ‖(1:ℂ)‖+‖((M*u^3/(6*w):ℝ):ℂ)*Complex.I^3‖ := norm_add_le _ _
          _ = _ := by simp [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
            abs_div, abs_mul, abs_of_pos hw0, abs_of_pos hu0]
      dsimp [f, scaledError, g, k]
      have hn2 := norm_sub_le (charFun (centeredLaw (w^2) p q a b) (u/w))
        ((Real.exp (-V*u^2/2):ℂ)*(1+((M*u^3/(6*w):ℝ):ℂ)*Complex.I^3))
      rw [hcenter, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)] at hn2
      have hn3 := mul_le_mul_of_nonneg_left hn (Real.exp_pos (-V*u^2/2)).le
      apply (div_le_div_of_nonneg_right (hn2.trans (add_le_add le_rfl hn3)) hu0.le).trans_eq
      ring
    have hhigh (w : ℝ) (hw : 1≤w) :
        (∫ u in Icc (δ*w) (C*w), f w u) ≤
          (∫ t in Icc δ C, ‖charFun (pairLaw (Real.toNNReal (w^2*p))
            (Real.toNNReal (w^2*q)) a b) t‖/t) + ∫ u in Icc (δ*w) (C*w), k w u := by
      have hw0 : 0<w := lt_of_lt_of_le zero_lt_one hw
      have hgint : IntegrableOn (g w) (Icc (δ*w) (C*w)) := by
        apply ContinuousOn.integrableOn_compact isCompact_Icc
        apply ContinuousOn.div _ continuousOn_id (fun u hu => ne_of_gt ((mul_pos hδ hw0).trans_le hu.1))
        simp_rw [pair_charFun]
        fun_prop
      have hkint : IntegrableOn (k w) (Icc (δ*w) (C*w)) := by
        apply ContinuousOn.integrableOn_compact isCompact_Icc
        apply ContinuousOn.div _ continuousOn_id (fun u hu => ne_of_gt ((mul_pos hδ hw0).trans_le hu.1))
        fun_prop
      have hscale : (∫ u in Icc (δ*w) (C*w), g w u) =
          ∫ t in Icc δ C, ‖charFun (pairLaw (Real.toNNReal (w^2*p))
            (Real.toNNReal (w^2*q)) a b) t‖/t := by
        let j := fun t => ‖charFun (pairLaw (Real.toNNReal (w^2*p))
            (Real.toNNReal (w^2*q)) a b) t‖/t
        have heq : g w = fun u => w⁻¹ * j (u/w) := by
          funext u
          dsimp [g,j]
          field_simp
        rw [heq, integral_const_mul, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (mul_le_mul_of_nonneg_right hδC hw0.le),
          intervalIntegral.integral_comp_div j hw0.ne']
        simp only [mul_div_cancel_right₀ _ hw0.ne', smul_eq_mul,
          ← mul_assoc, inv_mul_cancel₀ hw0.ne', one_mul]
        rw [intervalIntegral.integral_of_le hδC, ← integral_Icc_eq_integral_Ioc]
      calc
        _ ≤ ∫ u in Icc (δ*w) (C*w), (g w u+k w u) :=
          setIntegral_mono_on (hfint w _ _ (mul_nonneg hδ.le hw0.le)) (hgint.add hkint)
            measurableSet_Icc (fun u hu => hpoint w hw u hu.1)
        _ = _ := by rw [integral_add hgint hkint, hscale]
    have hsplit (w : ℝ) (hw : 1≤w) :
        (∫ u in Icc 0 (C*w), f w u) =
        (∫ u in Icc 0 (δ*w), f w u)+(∫ u in Icc (δ*w) (C*w), f w u) := by
      have hw0 : 0≤w := (zero_le_one.trans hw)
      have h0δ : 0≤δ*w := mul_nonneg hδ.le hw0
      have hδCw := mul_le_mul_of_nonneg_right hδC hw0
      have h0C : 0≤C*w := h0δ.trans hδCw
      simp_rw [integral_Icc_eq_integral_Ioc]
      rw [← intervalIntegral.integral_of_le h0C, ← intervalIntegral.integral_of_le h0δ,
        ← intervalIntegral.integral_of_le hδCw,
        intervalIntegral.integral_add_adjacent_intervals
          ((intervalIntegrable_iff_integrableOn_Icc_of_le h0δ).mpr (hfint w _ _ le_rfl))
          ((intervalIntegrable_iff_integrableOn_Icc_of_le hδCw).mpr (hfint w _ _ h0δ))]
    have hlow := low_frequency_integral_vanishes p q a b δ hp.le hq.le hV hδ.le ha hb habsorb
    have hraw := (annulus_integral_vanishes p q a b hp hq hb0 hirr δ C hδ).comp
      (tendsto_pow_atTop (by decide : (2:ℕ)≠0))
    have hraw' : Tendsto (fun w : ℝ => w * ∫ t in Icc δ C,
        ‖charFun (pairLaw (Real.toNNReal (w^2*p)) (Real.toNNReal (w^2*q)) a b) t‖/t)
        atTop (𝓝 0) := by
      apply hraw.congr'
      filter_upwards [eventually_ge_atTop (0:ℝ)] with w hw
      simp only [Function.comp_def, Real.sqrt_sq hw]
    have hgauss := gaussian_correction_tail V M δ C hV hδ
    have hlimit := hlow.add (hraw'.add hgauss)
    simp only [add_zero] at hlimit
    apply squeeze_zero' _ _ hlimit
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with w hw
      apply mul_nonneg (zero_le_one.trans hw)
      exact setIntegral_nonneg measurableSet_Icc (fun u hu => div_nonneg (norm_nonneg _) hu.1)
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with w hw
      change w*(∫ u in Icc 0 (C*w), f w u) ≤ _
      rw [hsplit w hw]
      have hh := mul_le_mul_of_nonneg_left (hhigh w hw) (zero_le_one.trans hw)
      dsimp only [f, scaledError, k, V, M] at *
      linarith
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

  let V := p*a^2+q*b^2
  let W := p*a^4+q*b^4
  let c := |p*a^3+q*b^3|/6
  have hV : 0<V := add_pos_of_nonneg_of_pos (mul_nonneg hp.le (sq_nonneg _))
    (mul_pos hq (sq_pos_of_ne_zero hb0))
  have hW : 0≤W := by dsimp [W]; positivity
  have hc : 0≤c := by dsimp [c]; positivity
  let δ := min 1 (min C (min (1/(|a|+1)) (min (1/(|b|+1)) (V/(4*(c+W+1))))))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδ1 : δ≤1 := min_le_left _ _
  have hδC : δ≤C := (min_le_right _ _).trans (min_le_left _ _)
  have hδa : δ≤1/(|a|+1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδb : δ≤1/(|b|+1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδV : δ≤V/(4*(c+W+1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have ha : δ*|a|≤1 := by
    have hh := (le_div_iff₀ (by positivity : 0 < |a|+1)).mp hδa
    nlinarith
  have hb : δ*|b|≤1 := by
    have hh := (le_div_iff₀ (by positivity : 0 < |b|+1)).mp hδb
    nlinarith
  have habsorb : c*δ+W*δ^2≤V/4 := by
    have hh := (le_div_iff₀ (by positivity : 0<4*(c+W+1))).mp hδV
    have hs : δ^2≤δ := by nlinarith
    have hws := mul_le_mul_of_nonneg_left hs hW
    nlinarith
  have hpos := positive_cutoff_vanishes p q a b δ C hp hq hb0 hirr hV
    hδ hδC ha hb habsorb
  let f := fun w u => ‖scaledError p q a b w u‖/|u|
  have heven (w u : ℝ) : f w (-u)=f w u := by
    dsimp [f]
    rw [scaledError_neg_norm, abs_neg]
  have heq (w : ℝ) (hw : 0≤w) :
      (∫ u in Icc (-C*w) (C*w), f w u) =
        2*∫ u in Icc 0 (C*w), ‖scaledError p q a b w u‖/u := by
    have hB : 0≤C*w := mul_nonneg hC.le hw
    have hi1 := (intervalIntegrable_iff_integrableOn_Icc_of_le (neg_nonpos.mpr hB)).mpr
      (scaledError_integrable p q a b w (-(C*w)) 0 hp.le hq.le)
    have hi2 := (intervalIntegrable_iff_integrableOn_Icc_of_le hB).mpr
      (scaledError_integrable p q a b w 0 (C*w) hp.le hq.le)
    have hn : (∫ u in -(C*w)..0, f w u) = ∫ u in 0..C*w, f w u := by
      have hh := intervalIntegral.integral_comp_neg (f w) (a:=0) (b:=C*w)
      simp only [heven, neg_zero] at hh
      exact hh.symm
    have hmain : (∫ u in Icc (-C*w) (C*w), f w u) = 2*∫ u in Icc 0 (C*w), f w u := by
      rw [neg_mul, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (neg_le_self hB),
        ← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, hn,
        intervalIntegral.integral_of_le hB, ← integral_Icc_eq_integral_Ioc]
      ring
    rw [hmain]
    congr 1
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    dsimp [f]
    rw [abs_of_nonneg hu.1]
  have hlim := hpos.const_mul 2
  simp only [mul_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with w hw
  change 2*(w*∫ u in Icc 0 (C*w), ‖scaledError p q a b w u‖/u) =
    w*∫ u in Icc (-C*w) (C*w), f w u
  rw [heq w hw]
  ring


end CompoundPoissonEdgeworthProposal
end
