/- GID: D5/S3/Quantum/Analysis/FirstDomainWeakCCR
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/FirstDomainWeakCCR
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual position and weak momentum satisfy the canonical form identity on their individual first L2 domains. -/

import D5.S3.Quantum.Analysis.TranslationDomainWeakStrong
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section

namespace D5.S3.Quantum.Analysis.FirstDomainWeakCCR

set_option backward.isDefEq.respectTransparency false in
/-- The actual position and momentum outputs satisfy the weak canonical relation
on their individual first L2 domains. -/
theorem first_domain_weak_ccr (hbar : ℝ) (hhbar : 0 < hbar)
    (f g df dg : ℝ → ℂ)
    (hf : MemLp f 2 (volume : Measure ℝ)) (hg : MemLp g 2 (volume : Measure ℝ))
    (hdf : MemLp df 2 (volume : Measure ℝ)) (hdg : MemLp dg 2 (volume : Measure ℝ))
    (hxf : MemLp (fun x : ℝ => (x : ℂ) * f x) 2 (volume : Measure ℝ))
    (hxg : MemLp (fun x : ℝ => (x : ℂ) * g x) 2 (volume : Measure ℝ))
    (hwf : ∀ φ : ℝ → ℝ, ContDiff ℝ (WithTop.some (⊤ : ℕ∞)) φ →
      HasCompactSupport φ → (∫ x : ℝ, ((deriv φ x : ℝ) : ℂ) * f x) =
      -∫ x : ℝ, (φ x : ℂ) * df x)
    (hwg : ∀ φ : ℝ → ℝ, ContDiff ℝ (WithTop.some (⊤ : ℕ∞)) φ →
      HasCompactSupport φ → (∫ x : ℝ, ((deriv φ x : ℝ) : ℂ) * g x) =
      -∫ x : ℝ, (φ x : ℂ) * dg x) :
    inner ℂ (hxf.toLp (fun x : ℝ => (x : ℂ) * f x))
        ((-Complex.I * (hbar : ℂ)) • hdg.toLp dg) -
      inner ℂ ((-Complex.I * (hbar : ℂ)) • hdf.toLp df)
        (hxg.toLp (fun x : ℝ => (x : ℂ) * g x)) =
      Complex.I * (hbar : ℂ) * inner ℂ (hf.toLp f) (hg.toLp g) := by
  have hmod (f : ℝ → ℂ) (hf : MemLp f 2 (volume : Measure ℝ))
      (hxf : MemLp (fun x : ℝ => (x : ℂ) * f x) 2 (volume : Measure ℝ)) :
      ∃ hm : ∀ t : ℝ, MemLp (fun x : ℝ => Complex.exp ((t * x : ℝ) * Complex.I) * f x)
        2 (volume : Measure ℝ),
        HasDerivAt (fun t : ℝ => (hm t).toLp
          (fun x : ℝ => Complex.exp ((t * x : ℝ) * Complex.I) * f x))
          (Complex.I • hxf.toLp (fun x : ℝ => (x : ℂ) * f x)) 0 := by
    let phase : ℝ → ℝ → ℂ := fun t x => Complex.exp ((t * x : ℝ) * Complex.I)
    have hphase : ∀ t x, ‖phase t x‖ = 1 := by
      intro t x
      simp [phase, Complex.norm_exp, Complex.mul_re]
    have hm : ∀ t : ℝ, MemLp (fun x : ℝ => phase t x * f x)
        2 (volume : Measure ℝ) := by
      intro t
      have hc : Continuous (phase t) := by dsimp [phase]; fun_prop
      apply MemLp.of_le_mul (c := 1) hf (hc.aestronglyMeasurable.mul hf.aestronglyMeasurable)
      filter_upwards [] with x
      simp [norm_mul, hphase]
    refine ⟨hm, ?_⟩
    have hd : ∀ x t, HasDerivAt (fun r : ℝ => phase r x)
        (phase t x * ((x : ℂ) * Complex.I)) t := by
      intro x t
      simpa [phase] using (((hasDerivAt_id t).mul_const x).ofReal_comp.mul_const
        Complex.I).cexp
    have hphase_bound : ∀ t x, ‖phase t x - 1‖ ≤ ‖x‖ * ‖t‖ := by
      intro t x
      have hl : LipschitzWith ‖x‖₊ (fun r : ℝ => phase r x) :=
        lipschitzWith_of_nnnorm_deriv_le (fun r => (hd x r).differentiableAt) (by
          intro r
          rw [(hd x r).deriv]
          apply le_of_eq
          apply NNReal.eq
          simp [norm_mul, hphase])
      simpa [dist_eq_norm, phase] using hl.dist_le_mul t 0
    let q : ℝ → ℝ → ℂ := fun t x => t⁻¹ • ((phase t x - 1) * f x)
    let k : ℝ → ℂ := fun x => Complex.I * ((x : ℂ) * f x)
    have hk : MemLp k 2 (volume : Measure ℝ) := by
      simpa [k] using hxf.const_mul Complex.I
    have hq : ∀ t, MemLp (q t) 2 (volume : Measure ℝ) := by
      intro t
      convert ((hm t).sub hf).const_smul t⁻¹ using 1
      funext x
      simp only [q, Pi.smul_apply, Pi.sub_apply, sub_mul, one_mul]
    have hqb : ∀ t x, ‖q t x‖ ≤ ‖(x : ℂ) * f x‖ := by
      intro t x
      by_cases ht : t = 0
      · simp [q, ht]
        positivity
      · have htn : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht
        calc
          ‖q t x‖ = ‖t‖⁻¹ * (‖phase t x - 1‖ * ‖f x‖) := by
            simp [q, norm_smul, norm_mul]
          _ ≤ ‖t‖⁻¹ * ((‖x‖ * ‖t‖) * ‖f x‖) := by
            gcongr
            exact hphase_bound t x
          _ = ‖(x : ℂ) * f x‖ := by
            rw [norm_mul, Complex.norm_real]
            field_simp
    have herror : ∀ t x, ‖q t x - k x‖ ≤ ‖(2 : ℂ) * ((x : ℂ) * f x)‖ := by
      intro t x
      calc
        ‖q t x - k x‖ ≤ ‖q t x‖ + ‖k x‖ := norm_sub_le _ _
        _ ≤ ‖(x : ℂ) * f x‖ + ‖(x : ℂ) * f x‖ := by
          simpa [k, norm_mul] using add_le_add (hqb t x) (le_refl ‖k x‖)
        _ = ‖(2 : ℂ) * ((x : ℂ) * f x)‖ := by simp [norm_mul]; ring
    have hqlim : ∀ x, Tendsto (fun t => q t x) (𝓝[≠] (0 : ℝ)) (𝓝 (k x)) := by
      intro x
      have hdx := (hd x 0).mul_const (f x)
      have ht := hdx.tendsto_slope_zero
      convert ht using 1
      · funext t
        simp only [q, zero_add, phase, zero_mul, Complex.ofReal_zero, Complex.exp_zero,
          one_mul, sub_mul]
      · simp [k, phase]
        ring
    let b : ℝ → ℝ≥0∞ := fun x => ‖(2 : ℂ) * ((x : ℂ) * f x)‖ₑ ^ (2 : ℝ)
    have hfin : ∫⁻ x : ℝ, b x ∂volume ≠ ∞ := by
      have hb := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) (hxf.const_mul (2 : ℂ)).eLpNorm_lt_top
      simpa [b] using hb.ne
    have hi : Tendsto (fun t => ∫⁻ x : ℝ, ‖q t x - k x‖ₑ ^ (2 : ℝ) ∂volume)
        (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      have hdct := tendsto_lintegral_filter_of_dominated_convergence' (μ := (volume : Measure ℝ))
        (F := fun t x => ‖q t x - k x‖ₑ ^ (2 : ℝ)) (f := fun _ => 0) b
        (Eventually.of_forall fun t => ((hq t).sub hk).aestronglyMeasurable.enorm.pow_const _)
        (Eventually.of_forall fun t => Eventually.of_forall fun x => by
          apply ENNReal.rpow_le_rpow _ (by norm_num)
          exact ENNReal.coe_le_coe.mpr (by exact_mod_cast herror t x))
        hfin (Eventually.of_forall fun x => by
          have hz : Tendsto (fun t => q t x - k x) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
            simpa using (hqlim x).sub (tendsto_const_nhds (x := k x))
          simpa using hz.enorm.ennrpow_const (2 : ℝ))
      simpa using hdct
    have hen : Tendsto (fun t => eLpNorm (q t - k) 2 (volume : Measure ℝ))
        (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
      simpa using hi.ennrpow_const (1 / (2 : ℝ))
    have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' q hq k hk).mpr hen
    apply hasDerivAt_iff_tendsto_slope_zero.mpr
    convert ht using 1
    · funext t
      apply Lp.ext
      filter_upwards [(hq t).coeFn_toLp,
        Lp.coeFn_smul t⁻¹ (((hm (0 + t)).toLp _) - ((hm 0).toLp _)),
        Lp.coeFn_sub ((hm (0 + t)).toLp _) ((hm 0).toLp _),
        (hm (0 + t)).coeFn_toLp, (hm 0).coeFn_toLp] with x hx hsm hsub hpt hp0
      simp_all [q, phase, sub_mul]
    · apply congrArg nhds
      apply Lp.ext
      filter_upwards [hk.coeFn_toLp, Lp.coeFn_smul Complex.I (hxf.toLp _), hxf.coeFn_toLp]
        with x hx hi hxv
      simp_all [k]
  let H : Type := Lp ℂ 2 (volume : Measure ℝ)
  let phase : ℝ → ℝ → ℂ := fun s x => Complex.exp ((s * x : ℝ) * Complex.I)
  have hphase : ∀ s x, ‖phase s x‖ = 1 := by
    intro s x
    simp [phase, Complex.norm_exp, Complex.mul_re]
  have hm : ∀ (s : ℝ) (u : H), MemLp (fun x : ℝ => phase s x * u x)
      2 (volume : Measure ℝ) := by
    intro s u
    have hc : Continuous (phase s) := by dsimp [phase]; fun_prop
    apply MemLp.of_le_mul (c := 1) (Lp.memLp u)
      (hc.aestronglyMeasurable.mul (Lp.memLp u).aestronglyMeasurable)
    filter_upwards [] with x
    simp [norm_mul, hphase]
  let U : ℝ → H → H := fun s u => (hm s u).toLp (fun x => phase s x * u x)
  let V : ℝ → H → H := fun t u => DomAddAct.mk t +ᵥ u
  let F : H := hf.toLp f
  let G : H := hg.toLp g
  let QF : H := hxf.toLp (fun x : ℝ => (x : ℂ) * f x)
  let QG : H := hxg.toLp (fun x : ℝ => (x : ℂ) * g x)
  let DF : H := hdf.toLp df
  let DG : H := hdg.toLp dg
  have hUae : ∀ s u, U s u =ᵐ[volume] fun x => phase s x * u x := by
    intro s u
    exact (hm s u).coeFn_toLp
  have hVae : ∀ t u, V t u =ᵐ[volume] fun x => u (t + x) := by
    intro t u
    exact DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk t) u
  have hU0 : ∀ u, U 0 u = u := by
    intro u
    apply Lp.ext
    filter_upwards [hUae 0 u] with x hx
    simpa [phase] using hx
  have hV0 : ∀ u, V 0 u = u := by intro u; simp [V]
  have hUadj : ∀ s u v, inner ℂ (U s u) v = inner ℂ u (U (-s) v) := by
    intro s u v
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hUae s u, hUae (-s) v] with x hu hv
    rw [hu, hv]
    simp [smul_eq_mul, phase, ← Complex.exp_conj, mul_assoc, mul_comm, mul_left_comm]
  have hVadj : ∀ t u v, inner ℂ (V t u) v = inner ℂ u (V (-t) v) := by
    intro t u v
    rw [L2.inner_def, L2.inner_def]
    rw [← integral_add_left_eq_self (fun y : ℝ => inner ℂ (u y) ((V (-t) v) y)) t]
    apply integral_congr_ae
    filter_upwards [hVae t u,
      (measurePreserving_add_left (volume : Measure ℝ) t).quasiMeasurePreserving.ae_eq_comp
        (hVae (-t) v)] with x hu hv
    have hv' : (V (-t) v) (t + x) = v (-t + (t + x)) := by
      simpa [Function.comp_def] using hv
    rw [hu, hv']
    simp
  have hWeyl : ∀ s t u, V t (U s u) =
      Complex.exp ((s * t : ℝ) * Complex.I) • U s (V t u) := by
    intro s t u
    apply Lp.ext
    filter_upwards [hVae t (U s u), hUae s (V t u), hVae t u,
      Lp.coeFn_smul (Complex.exp ((s * t : ℝ) * Complex.I)) (U s (V t u)),
      (measurePreserving_add_left (volume : Measure ℝ) t).quasiMeasurePreserving.ae_eq_comp
        (hUae s u)] with x hv hu hvu hsm huc
    have huc' : (U s u) (t + x) = phase s (t + x) * u (t + x) := by
      simpa [Function.comp_def] using huc
    rw [hv, huc', hsm]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hu, hvu]
    simp only [phase, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]
    ring
  have hsubL (u v w : H) : inner ℂ (u - v) w = inner ℂ u w - inner ℂ v w := by
    convert (inner_sub_left (𝕜 := ℂ) u v w) using 1 <;> rfl
  have hsubR (u v w : H) : inner ℂ u (v - w) = inner ℂ u v - inner ℂ u w := by
    convert (inner_sub_right (𝕜 := ℂ) u v w) using 1 <;> rfl
  have hnegR (u v : H) : inner ℂ u (-v) = -inner ℂ u v := by
    convert (inner_neg_right (𝕜 := ℂ) u v) using 1 <;> rfl
  have hbounded : ∀ s t,
      inner ℂ (U s F - F) (V t G - G) -
        inner ℂ (V (-t) F - F) (U (-s) G - G) =
      (1 - Complex.exp ((-(s * t) : ℝ) * Complex.I)) * inner ℂ (U s F) (V t G) := by
    intro s t
    simp only [hsubL, hsubR]
    rw [hUadj s F G, hVadj (-t) F G, hVadj (-t) F (U (-s) G)]
    simp only [neg_neg]
    rw [hWeyl (-s) t G, inner_smul_right, ← hUadj s F (V t G)]
    simp only [neg_mul]
    ring
  have hUF : HasDerivAt (fun s => U s F) (Complex.I • QF) 0 := by
    obtain ⟨hm', hd⟩ := hmod f hf hxf
    have he : (fun s => U s F) = (fun s => (hm' s).toLp
        (fun x : ℝ => Complex.exp ((s * x : ℝ) * Complex.I) * f x)) := by
      funext s
      apply Lp.ext
      filter_upwards [hUae s F, hf.coeFn_toLp, (hm' s).coeFn_toLp] with x hu hfx hmx
      simp_all [F, phase]
    simpa only [he, QF] using hd
  have hUG : HasDerivAt (fun s => U s G) (Complex.I • QG) 0 := by
    obtain ⟨hm', hd⟩ := hmod g hg hxg
    have he : (fun s => U s G) = (fun s => (hm' s).toLp
        (fun x : ℝ => Complex.exp ((s * x : ℝ) * Complex.I) * g x)) := by
      funext s
      apply Lp.ext
      filter_upwards [hUae s G, hg.coeFn_toLp, (hm' s).coeFn_toLp] with x hu hgx hmx
      simp_all [G, phase]
    simpa only [he, QG] using hd
  have hVF : HasDerivAt (fun t => V t F) DF 0 :=
    (D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.translation_domain_iff f df hf hdf).mp hwf
  have hVG : HasDerivAt (fun t => V t G) DG 0 :=
    (D5.S3.Quantum.Analysis.TranslationDomainWeakStrong.translation_domain_iff g dg hg hdg).mp hwg
  have hreflect (a : ℝ → H) (a' : H) (ha : HasDerivAt a a' 0) :
      HasDerivAt (fun t : ℝ => a (-t)) (-a') 0 := by
    have hn : Tendsto (fun t : ℝ => -t) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · simpa using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, neg_eq_zero] using ht
    have hc := (ha.tendsto_slope_zero.comp hn).neg
    apply hasDerivAt_iff_tendsto_slope_zero.mpr
    convert hc using 1
    funext t
    simp only [zero_add, neg_zero, inv_neg, neg_smul, Function.comp_apply]
    convert (neg_neg (t⁻¹ • (a (-t) - a 0))).symm using 1 <;> rfl
  have hfirst : ∀ t,
      inner ℂ (Complex.I • QF) (V t G - G) -
        inner ℂ (V (-t) F - F) (-Complex.I • QG) =
      (Complex.I * (t : ℂ)) * inner ℂ F (V t G) := by
    intro t
    have hneg : HasDerivAt (fun s : ℝ => U (-s) G) (-Complex.I • QG) 0 := by
      simpa only [neg_smul] using hreflect (fun s => U s G) (Complex.I • QG) hUG
    have hleft := (HasDerivAt.inner ℂ (hUF.sub_const F)
      (hasDerivAt_const (x := (0 : ℝ)) (V t G - G))).sub
      (HasDerivAt.inner ℂ (hasDerivAt_const (x := (0 : ℝ)) (V (-t) F - F))
        (hneg.sub_const G))
    have hphaseD : HasDerivAt
        (fun s : ℝ => 1 - Complex.exp ((-(s * t) : ℝ) * Complex.I))
        (Complex.I * (t : ℂ)) 0 := by
      have he := ((((hasDerivAt_id (0 : ℝ)).mul_const t).neg).ofReal_comp.mul_const
        Complex.I).cexp
      convert he.const_sub 1 using 1 <;> norm_num <;> first | rfl | ring
    have hright := hphaseD.mul
      (HasDerivAt.inner ℂ hUF (hasDerivAt_const (x := (0 : ℝ)) (V t G)))
    have heq := hleft.unique (hright.congr_of_eventuallyEq
      (Eventually.of_forall fun s => hbounded s t))
    simpa [hU0, inner_zero_left, inner_zero_right, hnegR, neg_smul, sub_neg_eq_add] using heq
  have hnegV : HasDerivAt (fun t : ℝ => V (-t) F) (-DF) 0 :=
    hreflect (fun t => V t F) DF hVF
  have hleft := (HasDerivAt.inner ℂ (hasDerivAt_const (x := (0 : ℝ)) (Complex.I • QF))
    (hVG.sub_const G)).sub
    (HasDerivAt.inner ℂ (hnegV.sub_const F)
      (hasDerivAt_const (x := (0 : ℝ)) (-Complex.I • QG)))
  have hright := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul Complex.I).mul
    (HasDerivAt.inner ℂ (hasDerivAt_const (x := (0 : ℝ)) F) hVG)
  have heq := hleft.unique (hright.congr_of_eventuallyEq
    (Eventually.of_forall fun t => hfirst t))
  simp only [hV0, sub_self, inner_zero_left, inner_zero_right, zero_add, add_zero,
    mul_zero, zero_mul, Complex.ofReal_zero, Complex.ofReal_one, id_eq, neg_zero,
    one_mul, mul_one] at heq
  simp only [inner_smul_left, inner_smul_right, inner_neg_left, map_neg,
    Complex.conj_I, neg_neg] at heq
  simp only [inner_smul_left, inner_smul_right, map_mul, map_neg, Complex.conj_I,
    Complex.conj_ofReal, neg_neg]
  change (-Complex.I * (hbar : ℂ)) * inner ℂ QF DG -
    (Complex.I * (hbar : ℂ)) * inner ℂ DF QG =
      Complex.I * (hbar : ℂ) * inner ℂ F G
  linear_combination (hbar : ℂ) * heq

end D5.S3.Quantum.Analysis.FirstDomainWeakCCR
