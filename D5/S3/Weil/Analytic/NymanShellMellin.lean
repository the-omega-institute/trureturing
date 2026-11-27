/- GID: D5/S3/Weil/Analytic/NymanShellMellin
   generality: I
   mirror-B: D5/B/S3/Weil/Analytic/NymanShellMellin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mellin continuation for compactly supported Möbius shell sums. -/

import Mathlib.Analysis.MellinTransform
import D5.S3.Weil.ZetaPntBounds.ZetaBoundsUpper
import Mathlib.Tactic
import Mathlib.NumberTheory.LSeries.Dirichlet
import OmegaBuild.Commands

/-! Mellin continuation for compactly supported Möbius shell sums. -/

compile_only_with_mathlib

set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory ArithmeticFunction Complex Finset
open scoped Topology ArithmeticFunction.Moebius LSeries.notation

namespace NymanShellMellin

/-- Literal locally finite Möbius sum at all positive continuous scales. -/
def scaled (W : ℝ→ℂ) (t : ℝ) : ℂ := ∑' n : ℕ,(μ n:ℂ)*W ((n:ℝ)*t)

private theorem continuousOn_scaled {W : ℝ→ℂ} (hc : Continuous W)
    (hW : ∀ x∉Set.Ioo (1:ℝ) 2,W x=0) :
    ContinuousOn (scaled W) (Set.Ioi 0) := by
  intro t ht
  let R : ℕ := ⌈4/t⌉₊
  have hpos : 0<t := ht
  have he : scaled W =ᶠ[𝓝[Set.Ioi 0] t]
      fun x => ∑ n∈range (R+1), (μ n:ℂ)*W ((n:ℝ)*x) := by
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (show t/2<t by linarith))] with x hx
    unfold scaled
    apply tsum_eq_sum
    intro n hn
    have hnR : R<n := by simpa [Finset.mem_range,not_lt] using hn
    have hR : 4/t≤(R:ℝ) := Nat.le_ceil _
    have hRn : (R:ℝ)<n := by exact_mod_cast hnR
    have hnt : (4:ℝ)<(n:ℝ)*t := by
      exact (div_lt_iff₀ hpos).mp (hR.trans_lt hRn)
    have hnx : 2≤(n:ℝ)*x := by
      have hn0 : (0:ℝ)≤n := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hx.le hn0]
    rw [hW _ (by intro h; exact (not_lt_of_ge hnx) h.2),mul_zero]
  apply (Continuous.continuousWithinAt (f:=fun x => ∑ n∈range (R+1), (μ n:ℂ)*W ((n:ℝ)*x)) ?_).congr_of_eventuallyEq_of_mem he ht
  exact continuous_finsetSum _ fun n _ => continuous_const.mul (hc.comp (continuous_const.mul continuous_id))

private theorem zero_top {W : ℝ→ℂ} (hW : ∀ x∉Set.Ioo (1:ℝ) 2,W x=0) {t : ℝ} (ht : 2≤t) :
    scaled W t=0 := by
  unfold scaled
  trans ∑' n : ℕ,(0:ℂ)
  · apply tsum_congr
    intro n
    rcases eq_or_ne n 0 with rfl|hn
    · simp
    · have hn1 : (1:ℝ)≤n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
      have hnx : 2≤(n:ℝ)*t := by nlinarith
      rw [hW _ (by intro h; exact (not_lt_of_ge hnx) h.2),mul_zero]
  · simp

private theorem W_convergent {W : ℝ→ℂ} (hc : Continuous W)
    (hW : ∀ x∉Set.Ioo (1:ℝ) 2,W x=0) (s : ℂ) : MellinConvergent W s := by
  have hzTop : W=ᶠ[atTop] (fun _ => (0:ℂ)) := eventually_atTop.2 ⟨2,fun x hx => hW _ (by intro h; linarith [h.2])⟩
  have hzBot : W=ᶠ[𝓝[>] (0:ℝ)] (fun _ => (0:ℂ)) := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1))] with x hx
    exact hW _ (by intro h; exact (not_lt_of_ge hx.le) h.1)
  refine mellinConvergent_of_isBigO_rpow (a:=s.re+1) (b:=s.re-1)
    (hc.locallyIntegrable.locallyIntegrableOn _) ?_ (by linarith) ?_ (by linarith)
  · exact (Asymptotics.isBigO_zero _ _).congr' hzTop.symm (Filter.EventuallyEq.rfl)
  · exact (Asymptotics.isBigO_zero _ _).congr' hzBot.symm (Filter.EventuallyEq.rfl)

private theorem integrable_term {W : ℝ→ℂ} (hc : Continuous W)
    (hW : ∀ x∉Set.Ioo (1:ℝ) 2,W x=0) (s : ℂ) (n : ℕ) :
    Integrable (fun t : ℝ => (t:ℂ)^(s-1)*((μ n:ℂ)*W ((n:ℝ)*t))) (volume.restrict (Set.Ioi 0)) := by
  rcases eq_or_ne n 0 with rfl|hn
  · simp
  · have hnpos : (0:ℝ)<n := by positivity
    have h := (MellinConvergent.comp_mul_left hnpos).mpr (W_convergent hc hW s)
    unfold MellinConvergent at h
    simpa only [smul_eq_mul,mul_left_comm] using h.const_mul (μ n:ℂ)

private theorem integral_term {W : ℝ→ℂ} (s : ℂ) (n : ℕ) :
    (∫ t in Set.Ioi (0:ℝ),(t:ℂ)^(s-1)*((μ n:ℂ)*W ((n:ℝ)*t))) =
      LSeries.term (fun n => (μ n:ℂ)) s n*mellin W s := by
  rcases eq_or_ne n 0 with rfl|hn
  · simp [LSeries.term_zero]
  · have hnpos : (0:ℝ)<n := by positivity
    simp_rw [mul_left_comm ((_:ℂ)^(s-1)) (μ n:ℂ),integral_const_mul]
    change (μ n:ℂ)*mellin (fun t => W ((n:ℝ)*t)) s = _
    rw [mellin_comp_mul_left W s hnpos,LSeries.term_of_ne_zero hn,smul_eq_mul,Complex.cpow_neg]
    push_cast
    ring

private theorem norm_integral_term {W : ℝ→ℂ} (s : ℂ) (n : ℕ) :
    (∫ t in Set.Ioi (0:ℝ), ‖(t:ℂ)^(s-1)*((μ n:ℂ)*W ((n:ℝ)*t))‖) =
      ‖LSeries.term (fun n => (μ n:ℂ)) s n‖ *
        (∫ t in Set.Ioi (0:ℝ), ‖(t:ℂ)^(s-1)*W t‖) := by
  rcases eq_or_ne n 0 with rfl|hn
  · simp [LSeries.term_zero]
  · let G : ℝ→ℝ := fun t => ‖(t:ℂ)^(s-1)*W t‖
    have hnpos : (0:ℝ)<n := by positivity
    have hpoint (t : ℝ) (ht : 0<t) :
        ‖(t:ℂ)^(s-1)*((μ n:ℂ)*W ((n:ℝ)*t))‖ =
          ‖(μ n:ℂ)‖ * (n:ℝ)^(1-s.re) * G ((n:ℝ)*t) := by
      unfold G
      rw [norm_mul,norm_mul,norm_mul,Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg hnpos.le ht.le,norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
      have he : (s-1).re=s.re-1 := by simp
      rw [he]
      have hp : (n:ℝ)^(1-s.re)*(n:ℝ)^(s.re-1)=1 := by
        rw [←Real.rpow_add hnpos,show 1-s.re+(s.re-1)=0 by ring,Real.rpow_zero]
      calc
        _ = ‖(μ n:ℂ)‖ * (((n:ℝ)^(1-s.re)*(n:ℝ)^(s.re-1)) *
          (‖(t:ℂ)^(s-1)‖*‖W ((n:ℝ)*t)‖)) := by rw [hp,one_mul]; ring
        _ = _ := by ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpoint,integral_const_mul,
      integral_comp_mul_left_Ioi G 0 hnpos,mul_zero]
    change ‖(μ n:ℂ)‖*(n:ℝ)^(1-s.re) * ((n:ℝ)⁻¹ * ∫ t in Set.Ioi 0,G t) = _
    rw [LSeries.term_of_ne_zero hn,norm_div]
    rw [show (n:ℂ)=((n:ℝ):ℂ) by push_cast; rfl,Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
    have hpow : (n:ℝ)^(1-s.re)*(n:ℝ)⁻¹=((n:ℝ)^s.re)⁻¹ := by
      rw [←Real.rpow_neg_one,←Real.rpow_add hnpos,←Real.rpow_neg hnpos.le]
      congr 1
      ring
    rw [show ∫ t in Set.Ioi (0:ℝ),‖(t:ℂ)^(s-1)*W t‖ = ∫ t in Set.Ioi 0,G t by rfl, mul_assoc,←mul_assoc ((n:ℝ)^(1-s.re)),hpow]
    ring

/-- Absolute-convergence half-plane identity of the scale Mellin transform and the actual
reciprocal-zeta Dirichlet series. -/
theorem scaled_mellin_dirichlet {W : ℝ→ℂ} (hc : Continuous W)
    (hW : ∀ x∉Set.Ioo (1:ℝ) 2,W x=0) {s : ℂ} (hs : 1<s.re) :
    riemannZeta s*mellin (scaled W) s=mellin W s := by
  have hsumm : LSeriesSummable (fun n => (μ n:ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  have hsum : Summable (fun n : ℕ => ∫ t in Set.Ioi (0:ℝ), ‖(t:ℂ)^(s-1)*((μ n:ℂ)*W ((n:ℝ)*t))‖) := by
    simp_rw [norm_integral_term]
    exact hsumm.norm.mul_right _
  have hm : mellin (scaled W) s=LSeries (fun n => (μ n:ℂ)) s*mellin W s := by
    unfold mellin at ⊢
    calc
      _ = ∫ t in Set.Ioi (0:ℝ),∑' n, (t:ℂ)^(s-1)*((μ n:ℂ)*W ((n:ℝ)*t)) := by
        simp_rw [scaled,smul_eq_mul,tsum_mul_left]
      _ = ∑' n : ℕ,∫ t in Set.Ioi (0:ℝ),(t:ℂ)^(s-1)*((μ n:ℂ)*W ((n:ℝ)*t)) := by
        exact (integral_tsum_of_summable_integral_norm (integrable_term hc hW s) hsum).symm
      _ = _ := by
        simp_rw [integral_term]
        rw [tsum_mul_right]
        rfl
  rw [hm,←mul_assoc]
  have hz := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at hz
  rw [hz,one_mul]

private theorem W_differentiableAt {W : ℝ→ℂ} (hc : Continuous W)
    (hW : ∀ x∉Set.Ioo (1:ℝ) 2,W x=0) (s : ℂ) :
    DifferentiableAt ℂ (mellin W) s := by
  have hzTop : W=ᶠ[atTop] (fun _ => (0:ℂ)) := eventually_atTop.2 ⟨2,fun x hx => hW _ (by intro h; linarith [h.2])⟩
  have hzBot : W=ᶠ[𝓝[>] (0:ℝ)] (fun _ => (0:ℂ)) := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1))] with x hx
    exact hW _ (by intro h; exact (not_lt_of_ge hx.le) h.1)
  refine mellin_differentiableAt_of_isBigO_rpow (a:=s.re+1) (b:=s.re-1)
    (hc.locallyIntegrable.locallyIntegrableOn _) ?_ (by linarith) ?_ (by linarith)
  · exact (Asymptotics.isBigO_zero _ _).congr' hzTop.symm (Filter.EventuallyEq.rfl)
  · exact (Asymptotics.isBigO_zero _ _).congr' hzBot.symm (Filter.EventuallyEq.rfl)

private theorem scaled_differentiableAt {W : ℝ→ℂ} (hc : Continuous W)
    (hW : ∀ x∉Set.Ioo (1:ℝ) 2,W x=0)
    (hsmall : ∀ ε : ℝ, 0<ε → scaled W =O[𝓝[>] (0:ℝ)] (fun t => t^(-(1/2+ε:ℝ))))
    {s : ℂ} (hs : 1/2<s.re) : DifferentiableAt ℂ (mellin (scaled W)) s := by
  obtain ⟨b,hb1,hb2⟩ := exists_between hs
  have hbpos : 0<b-1/2 := by linarith
  have hzTop : scaled W=ᶠ[atTop] (fun _ => (0:ℂ)) :=
    eventually_atTop.2 ⟨2,fun _ ht => zero_top hW ht⟩
  refine mellin_differentiableAt_of_isBigO_rpow (a:=s.re+1) (b:=b)
    ((continuousOn_scaled hc hW).locallyIntegrableOn measurableSet_Ioi) ?_ (by linarith) ?_ hb2
  · exact (Asymptotics.isBigO_zero _ _).congr' hzTop.symm (Filter.EventuallyEq.rfl)
  · simpa only [show 1/2+(b-1/2)=b by ring] using hsmall (b-1/2) hbpos

private theorem domain_preconnected : IsPreconnected {s : ℂ | 1/2<s.re ∧ s≠1} := by
  let T : ℂ→ℂ := fun z => (z+1)/2
  have hT : Continuous T := by fun_prop
  have hreT : ∀ z : ℂ,(T z).re=(z.re+1)/2 := by
    intro z
    norm_num [T,Complex.div_re]
  have himage : T '' {z : ℂ | z≠1 ∧ 0<z.re}={s : ℂ | 1/2<s.re ∧ s≠1} := by
    ext s
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨?_,?_⟩
      · rw [hreT]; linarith [hz.2]
      · intro h
        apply hz.1
        dsimp [T] at h
        linear_combination h*2
    · intro hs
      refine ⟨2*s-1,⟨?_,?_⟩,?_⟩
      · intro h
        apply hs.2
        linear_combination h/2
      · simp only [Complex.sub_re,Complex.mul_re,Complex.re_ofNat,
          Complex.im_ofNat,zero_mul,sub_zero,Complex.one_re]
        linarith [hs.1]
      · dsimp [T]; ring
  rw [←himage]
  exact isPathConnected_aux.isConnected.isPreconnected.image T hT.continuousOn

/-- A holomorphically continued genuine scaled Möbius test must have zero Mellin
kernel at each genuine right-strip zero. -/
theorem zero_forces_kernel_zero {W : ℝ→ℂ} (hc : Continuous W)
    (hW : ∀ x∉Set.Ioo (1:ℝ) 2,W x=0)
    (hsmall : ∀ ε : ℝ, 0<ε → scaled W =O[𝓝[>] (0:ℝ)] (fun t => t^(-(1/2+ε:ℝ))))
    {rho : ℂ} (hrho : 1/2<rho.re) (hrho1 : rho.re<1) (hz : riemannZeta rho=0) :
    mellin W rho=0 := by
  let U := {s : ℂ | 1/2<s.re ∧ s≠1}
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
  have hprod : AnalyticOnNhd ℂ (fun s => riemannZeta s*mellin (scaled W) s) U :=
    (show DifferentiableOn ℂ (fun s => riemannZeta s*mellin (scaled W) s) U from
       fun s hs => ((differentiableAt_riemannZeta hs.2).mul (scaled_differentiableAt hc hW hsmall hs.1)).differentiableWithinAt).analyticOnNhd hU
  have hker : AnalyticOnNhd ℂ (mellin W) U :=
    (show DifferentiableOn ℂ (mellin W) U from
       fun s hs => (W_differentiableAt hc hW s).differentiableWithinAt).analyticOnNhd hU
  have htwo : (2:ℂ)∈U := by constructor <;> norm_num
  have heq : (fun s => riemannZeta s*mellin (scaled W) s) =ᶠ[𝓝 (2:ℂ)] mellin W := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1:ℝ)<(2:ℂ).re by norm_num)] with s hs
    exact scaled_mellin_dirichlet hc hW hs
  have hh := hprod.eqOn_of_preconnected_of_eventuallyEq hker domain_preconnected htwo heq
    (show rho∈U from ⟨hrho,fun he => by subst rho; norm_num at hrho1⟩)
  change riemannZeta rho*mellin (scaled W) rho=mellin W rho at hh
  rw [hz,zero_mul] at hh
  exact hh.symm

end NymanShellMellin
