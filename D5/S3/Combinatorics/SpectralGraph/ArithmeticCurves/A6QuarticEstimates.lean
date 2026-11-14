/- GID: D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6QuarticEstimates
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6QuarticEstimates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full positive-domain quartic tail, monotonicity and rational height estimates -/

import D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6EllipticModels
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.NumberTheory.Height.NumberField

/-! Source: supplied S.quarticmethod, original blob
19f74b8f3176c3318a521138504d04efab3760ac, PR9
6d491f77b35dec808fc777b69939c56cdae5dc02; application of Tzanakis,
Acta Arithmetica75(2)(1996),165-190, DOI10.4064/aa-75-2-165-190.
Original Nikandish problem and Ma/Nikandish/Zhang attribution remain.
These analytic/height estimates do not constitute a complete coefficient
bound, rank, saturation, regulator/David constants, LLL certificate or
integral-point exhaustion. Equation26's printed-factor discrepancy is
unresolved and neither printed factor is adopted. Both W signs and the
original integral inverse and positivity filters remain in force. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6QuarticEstimates
open A6EllipticModels

theorem quartic_gt_leading (b : ℝ) (hb : 0<b) : 43645*b^4<f b := by
  have h : 0<1152400*b^3+6640150*b^2+4524000*b+950625 := by positivity
  dsimp [f]
  linarith

theorem quartic_positive (b : ℝ) (hb : 0<b) : 0<f b := by
  exact lt_of_le_of_lt (by positivity) (quartic_gt_leading b hb)

def Fstar (b : ℝ) : ℝ :=
  (1950*Real.sqrt (f b)+4524000*b+1901250)/b^2

def fDerivative (b : ℝ) : ℝ :=
  174580*b^3+3457200*b^2+13280300*b+4524000

theorem hasDerivAt_f (b : ℝ) : HasDerivAt f (fDerivative b) b := by
  convert (((((hasDerivAt_id b).pow 4).const_mul 43645).add
    (((hasDerivAt_id b).pow 3).const_mul 1152400)).add
    (((hasDerivAt_id b).pow 2).const_mul 6640150)).add
    ((hasDerivAt_id b).const_mul 4524000) |>.add_const 950625 using 1 <;>
    (try ext x) <;> dsimp [f,fDerivative] <;> ring

theorem hasDerivAt_Fstar (b : ℝ) (hb : 0<b) :
    HasDerivAt Fstar
      (((1950*(fDerivative b/(2*Real.sqrt (f b)))+4524000)*b^2-
        (1950*Real.sqrt (f b)+4524000*b+1901250)*(2*b))/(b^2)^2) b := by
  have hs:=(hasDerivAt_f b).sqrt (quartic_positive b hb).ne'
  convert (((hs.const_mul 1950).add ((hasDerivAt_id b).const_mul 4524000)).add_const
    1901250).div ((hasDerivAt_id b).pow 2) (pow_ne_zero 2 hb.ne') using 1 <;>
    (try ext x) <;> dsimp [Fstar] <;> ring

theorem derivative_identity (b : ℝ) (hb : 0<b) :
    b^3*Real.sqrt (f b)*deriv Fstar b=
      -975*(1152400*b^3+2*6640150*b^2+3*4524000*b+3802500)-
      (4524000*b+3802500)*Real.sqrt (f b) := by
  rw [(hasDerivAt_Fstar b hb).deriv]
  have hs:=Real.sq_sqrt (quartic_positive b hb).le
  have hsn : Real.sqrt (f b)≠0 := (Real.sqrt_pos.2 (quartic_positive b hb)).ne'
  field_simp
  dsimp [fDerivative,f] at hs ⊢
  nlinarith [hs]

theorem derivative_negative (b : ℝ) (hb : 0<b) : deriv Fstar b<0 := by
  have hp : 0<b^3*Real.sqrt (f b) :=
    mul_pos (pow_pos hb 3) (Real.sqrt_pos.2 (quartic_positive b hb))
  have h1 : 0<975*(1152400*b^3+2*6640150*b^2+3*4524000*b+3802500) := by positivity
  have h2 : 0≤(4524000*b+3802500)*Real.sqrt (f b) := by positivity
  have he:=derivative_identity b hb
  have hprod : b^3*Real.sqrt (f b)*deriv Fstar b<0 := by linarith
  by_contra hn
  have hd : 0≤deriv Fstar b:=le_of_not_gt hn
  have hm:=mul_nonneg hp.le hd
  linarith

theorem Fstar_strictAnti : StrictAntiOn Fstar (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro b hb
    exact (hasDerivAt_Fstar b hb).continuousAt.continuousWithinAt
  · intro b hb
    rw [interior_Ioi] at hb
    exact derivative_negative b hb

/-- The source's entire integer-height majorant, on both W signs. -/
theorem quartic_upper (b : ℝ) (hb : 1≤b) : f b≤13310820*b^4 := by
  have h0 : 1≤b^4 := one_le_pow₀ hb
  have h1 : b≤b^4 := by simpa using pow_le_pow_right₀ hb (show 1≤4 by decide)
  have h2 : b^2≤b^4 := pow_le_pow_right₀ hb (by decide)
  have h3 : b^3≤b^4 := pow_le_pow_right₀ hb (by decide)
  dsimp [f]
  nlinarith

theorem both_signs_W_bound (b W : ℝ) (hb : 1≤b) (hw : W^2=f b) :
    |W|<3649*b^2 := by
  have hf:=quartic_upper b hb
  have hb4 : 0<b^4 := pow_pos (by linarith) 4
  apply abs_lt_of_sq_lt_sq _ (by positivity)
  rw [hw]
  nlinarith

def chartNumerator {R : Type*} [CommRing R] (b W : R) : R :=
  1950*(W+975)+4524000*b

theorem chart_numerator_bound (b W : ℝ) (hb : 1≤b) (hw : W^2=f b) :
    |chartNumerator b W|≤13540800*b^2 := by
  have hW:=both_signs_W_bound b W hb hw
  have hb2 : b≤b^2 := by nlinarith
  have hb20 : 1≤b^2 := by nlinarith
  calc
    |chartNumerator b W|≤1950*|W|+1901250+4524000*b := by
      dsimp [chartNumerator]
      rw [show 1950*(W+975)+4524000*b=1950*W+1901250+4524000*b by ring]
      have h:=abs_add_le (1950*W+1901250) (4524000*b)
      have h':=abs_add_le (1950*W) 1901250
      norm_num [abs_mul,abs_of_nonneg (by linarith : 0≤b)] at h h'
      linarith
    _ ≤13540800*b^2 := by nlinarith

/-- Reduction to lowest terms can only reduce the original numerator and
positive denominator. This is the actual rational Weil height. -/
theorem height_int_div (n d : ℤ) (hd : 0<d) (M : ℝ)
    (hn : |(n:ℝ)|≤M) (hdM : (d:ℝ)≤M) :
    Height.logHeight₁ ((n:ℚ)/(d:ℚ))≤Real.log M := by
  let q : ℚ := (n:ℚ)/(d:ℚ)
  have he : q=Rat.divInt n d := by dsimp [q];rw [Rat.divInt_eq_div]
  obtain ⟨c,hnc,hdc⟩:=Rat.num_den_mk hd.ne' he
  have hden : (0:ℤ)<q.den := by exact_mod_cast q.den_pos
  have hc : 0<c := by nlinarith
  have habs:=congrArg Int.natAbs hnc
  rw [Int.natAbs_mul] at habs
  have hcabs : 1≤c.natAbs := by
    have : c≠0 := by omega
    exact Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr this)
  have hqn : q.num.natAbs≤n.natAbs := by
    rw [habs]
    exact Nat.le_mul_of_pos_left _ hcabs
  have hqd : (q.den:ℤ)≤d := by nlinarith
  have hqnR : (q.num.natAbs:ℝ)≤|(n:ℝ)| := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using (show (q.num.natAbs:ℝ)≤(n.natAbs:ℝ) by exact_mod_cast hqn)
  have hqdR : (q.den:ℝ)≤M := le_trans (by exact_mod_cast hqd) hdM
  have hmax : ((max q.num.natAbs q.den:ℕ):ℝ)≤M := by
    rw [Nat.cast_max]
    exact max_le (hqnR.trans hn) hqdR
  have hpos : (0:ℝ)<((max q.num.natAbs q.den:ℕ):ℝ) := by
    exact_mod_cast lt_of_lt_of_le q.den_pos (le_max_right q.num.natAbs q.den)
  change Height.logHeight₁ q≤Real.log M
  rw [Rat.logHeight₁_eq_log_max]
  exact Real.log_le_log hpos hmax

/-- The full original logarithmic horizontal-height estimate, for both signs
of every integral quartic point and with no parameter cutoff. -/
theorem rational_chart_height (b W : ℤ) (hb : 1≤b) (hw : W^2=f b) :
    Height.logHeight₁ (rationalU (b:ℚ) (W:ℚ))≤
      Real.log 13540800+2*Real.log (b:ℝ) := by
  have hbR : (1:ℝ)≤b := by exact_mod_cast hb
  have hwR : (W:ℝ)^2=f (b:ℝ) := by
    dsimp [f] at hw ⊢
    exact_mod_cast hw
  have hn:=chart_numerator_bound (b:ℝ) W hbR hwR
  have he:=height_int_div (chartNumerator b W) (b^2)
    (sq_pos_of_pos (by omega)) (13540800*(b:ℝ)^2)
    (by simpa [chartNumerator] using hn) (by push_cast;nlinarith [sq_nonneg (b:ℝ)])
  have hcast : rationalU (b:ℚ) (W:ℚ)=
      ((chartNumerator b W:ℤ):ℚ)/((b^2:ℤ):ℚ) := by
    dsimp [rationalU,chartNumerator]
    push_cast
    ring
  rw [hcast]
  convert he using 1
  rw [Real.log_mul (by norm_num) (pow_ne_zero 2 (by linarith : (b:ℝ)≠0)),Real.log_pow]
  norm_num


/-- The entire positive tail integrand is bounded strictly by the
integrable leading-term comparison, with no numerical cutoff. -/
theorem inverse_sqrt_lt (u : ℝ) (hu : 0<u) :
    1/Real.sqrt (f u)<1/(Real.sqrt 43645*u^2) := by
  have hlead : 0≤43645*u^4 := by positivity
  have hs:=Real.sqrt_lt_sqrt hlead (quartic_gt_leading u hu)
  have he : Real.sqrt (43645*u^4)=Real.sqrt 43645*u^2 := by
    rw [Real.sqrt_mul (by norm_num),show u^4=(u^2)^2 by ring,
      Real.sqrt_sq (sq_nonneg u)]
  rw [he] at hs
  exact one_div_lt_one_div_of_lt (by positivity) hs

theorem tail_integrable (b : ℝ) (hb : 0<b) :
    IntegrableOn (fun u : ℝ => 1/Real.sqrt (f u)) (Ioi b) := by
  have hg : IntegrableOn (fun u : ℝ => 1/(Real.sqrt 43645*u^2)) (Ioi b) := by
    have he : (fun u : ℝ=>1/(Real.sqrt 43645*u^2))=
        (fun u : ℝ=>(1/Real.sqrt 43645)*u^(-2:ℝ)) := by
      funext u
      simp only [Real.rpow_neg_ofNat,zpow_neg,zpow_ofNat]
      ring
    rw [he]
    exact (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) hb).const_mul
      (1/Real.sqrt 43645)
  apply hg.mono_nonneg
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro u hu
    exact (continuousAt_const.div
      ((hasDerivAt_f u).continuousAt.sqrt)
      (Real.sqrt_pos.2 (quartic_positive u (hb.trans hu))).ne').continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact le_of_lt (one_div_pos.2 (Real.sqrt_pos.2 (quartic_positive u (hb.trans hu))))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (inverse_sqrt_lt u (hb.trans hu)).le

/-- Strict improper-integral estimate on every positive real tail. -/
theorem tail_integral_bound (b : ℝ) (hb : 0<b) :
    (∫ u : ℝ in Ioi b, 1/Real.sqrt (f u))<1/(Real.sqrt 43645*b) := by
  let g : ℝ → ℝ := fun u => 1/(Real.sqrt 43645*u^2)
  let h : ℝ → ℝ := fun u => 1/Real.sqrt (f u)
  have hg : IntegrableOn g (Ioi b) := by
    have he : g=
        (fun u : ℝ=>(1/Real.sqrt 43645)*u^(-2:ℝ)) := by
      funext u
      simp only [g,Real.rpow_neg_ofNat,zpow_neg,zpow_ofNat]
      ring
    rw [he]
    exact (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) hb).const_mul
      (1/Real.sqrt 43645)
  have hh : IntegrableOn h (Ioi b) := tail_integrable b hb
  have hdiff : ∀ u ∈ Ioi b, 0<g u-h u := by
    intro u hu
    exact sub_pos.2 (inverse_sqrt_lt u (hb.trans hu))
  have hs : Function.support (fun u => g u-h u)∩Ioi b=Ioi b := by
    apply Set.inter_eq_right.mpr
    intro u hu
    exact (hdiff u hu).ne'
  have hi : 0<(∫ u in Ioi b, g u-h u) := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae _ (hg.sub hh)).2
    · change 0<volume (Function.support (fun u=>g u-h u)∩Ioi b)
      rw [hs,Real.volume_Ioi]
      exact ENNReal.zero_lt_top
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact (hdiff u hu).le
  rw [integral_sub hg hh] at hi
  have he : (∫ u in Ioi b, g u)=1/(Real.sqrt 43645*b) := by
    calc
      (∫ u in Ioi b, g u)=
          (1/Real.sqrt 43645)*(∫ u : ℝ in Ioi b, u^(-2:ℝ)) := by
        rw [←integral_const_mul]
        congr 1
        ext u
        simp only [g,Real.rpow_neg_ofNat,zpow_neg,zpow_ofNat]
        ring
      _ = 1/(Real.sqrt 43645*b) := by
        rw [integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) hb]
        norm_num [Real.rpow_neg_one]
        ring
  rw [he] at hi
  exact sub_pos.mp hi


/-- Positivity of the original improper integral on every positive tail. -/
theorem tail_integral_positive (b : ℝ) (hb : 0<b) :
    0<(∫ u : ℝ in Ioi b, 1/Real.sqrt (f u)) := by
  have hp : ∀ u∈Ioi b,0<1/Real.sqrt (f u):=by
    intro u hu
    exact one_div_pos.2 (Real.sqrt_pos.2 (quartic_positive u (hb.trans hu)))
  have hs : Function.support (fun u : ℝ=>1/Real.sqrt (f u))∩Ioi b=Ioi b := by
    apply Set.inter_eq_right.mpr
    intro u hu
    exact (hp u hu).ne'
  apply (setIntegral_pos_iff_support_of_nonneg_ae _ (tail_integrable b hb)).2
  · rw [hs,Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (hp u hu).le

theorem Fstar_gt_asymptote (b : ℝ) (hb : 0<b) :
    1950*Real.sqrt 43645<Fstar b := by
  have hs:=Real.sqrt_lt_sqrt (show 0≤43645*b^4 by positivity) (quartic_gt_leading b hb)
  have he : Real.sqrt (43645*b^4)=Real.sqrt 43645*b^2:=by
    rw [Real.sqrt_mul (by norm_num),show b^4=(b^2)^2 by ring,
      Real.sqrt_sq (sq_nonneg b)]
  rw [he] at hs
  dsimp [Fstar]
  apply (lt_div_iff₀ (sq_pos_of_pos hb)).2
  nlinarith [hs]

private def normalized (b : ℝ) : ℝ :=
  43645+1152400*b⁻¹+6640150*(b⁻¹)^2+4524000*(b⁻¹)^3+950625*(b⁻¹)^4

private theorem normalized_eq (b : ℝ) (hb : b≠0) : normalized b=f b/b^4 := by
  dsimp [normalized,f]
  field_simp [hb]
  <;>ring

/-- Exact positive-branch asymptotic value of the full rational chart. -/
theorem Fstar_limit : Tendsto Fstar atTop (𝓝 (1950*Real.sqrt 43645)) := by
  have hi : Tendsto (fun b : ℝ=>b⁻¹) atTop (𝓝 0):=tendsto_inv_atTop_zero
  have hn : Tendsto normalized atTop (𝓝 43645):=by
    change Tendsto (fun x : ℝ=>43645+1152400*x⁻¹+6640150*(x⁻¹)^2+
      4524000*(x⁻¹)^3+950625*(x⁻¹)^4) atTop (𝓝 43645)
    have hc : Tendsto (fun _ : ℝ=>(43645:ℝ)) atTop (𝓝 43645):=tendsto_const_nhds
    simpa only [normalized,zero_pow (by decide : 2≠0),zero_pow (by decide : 3≠0),
      zero_pow (by decide : 4≠0),mul_zero,add_zero] using
      (((hc.add (hi.const_mul 1152400)).add ((hi.pow 2).const_mul 6640150)).add
        ((hi.pow 3).const_mul 4524000)).add ((hi.pow 4).const_mul 950625)
  have hs : Tendsto (fun b=>Real.sqrt (normalized b)) atTop (𝓝 (Real.sqrt 43645)):=
    (Real.continuous_sqrt.tendsto 43645).comp hn
  have he : Fstar=ᶠ[atTop] (fun b=>1950*Real.sqrt (normalized b)+
      4524000*b⁻¹+1901250*(b⁻¹)^2) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with b hb
    rw [normalized_eq b hb.ne',Real.sqrt_div (quartic_positive b hb).le,
      show b^4=(b^2)^2 by ring,Real.sqrt_sq (sq_nonneg b)]
    dsimp [Fstar]
    field_simp [hb.ne']
    <;>ring
  have hl : Tendsto (fun b=>1950*Real.sqrt (normalized b)+
      4524000*b⁻¹+1901250*(b⁻¹)^2) atTop (𝓝 (1950*Real.sqrt 43645)) := by
    simpa only [mul_zero,zero_pow (by decide : 2≠0),add_zero] using
      ((hs.const_mul 1950).add (hi.const_mul 4524000)).add
        ((hi.pow 2).const_mul 1901250)
  exact hl.congr' he.symm

/-- Both forbidden values in the original method are excluded on the
whole positive branch; this proves that no positive cutoff is needed. -/
theorem Fstar_excluded_values (b : ℝ) (hb : 0<b) :
    Fstar b≠ -1950*Real.sqrt 43645 ∧ Fstar b≠ -1257750 := by
  have h:=Fstar_gt_asymptote b hb
  have hp : 0<1950*Real.sqrt 43645:=by positivity
  constructor <;> intro he <;> rw [he] at h <;> linarith


end D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6QuarticEstimates
