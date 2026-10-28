/- GID: D5/S3/Quantum/Fibers/OriginalDensityStability
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/OriginalDensityStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integral loss-density stability of original absolutely continuous controls. -/

import D5.S3.Quantum.Fibers.OriginalCompleteOutputStability
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
universe v
open scoped ComplexOrder InnerProductSpace BigOperators
open Set Filter Topology MeasureTheory intervalIntegral TraceClassFiniteBlocks
namespace D5.S3.Quantum.Fibers.OriginalDensityStability
open OriginalControlMarkedJump OriginalControlComposition OriginalMarkedConcatenation
open OriginalReferenceOutputMeasure OriginalReferenceRepeatedMass OriginalCompleteOutputStability

private def rate (c x v : ℝ) : ℝ := max v 0/x+max (-v) 0/(c-x)

private theorem velocity_error (c eta x v w : ℝ) (he : 0 < eta)
    (hx : eta ≤ x) (hcx : eta ≤ c-x) :
    |rate c x v-rate c x w| ≤ |v-w|/eta := by
  have hx0 := he.trans_le hx
  have hc0 := he.trans_le hcx
  by_cases hv : 0 ≤ v <;> by_cases hw : 0 ≤ w
  · simp only [rate,max_eq_left hv,max_eq_left hw,max_eq_right (neg_nonpos.mpr hv),
      max_eq_right (neg_nonpos.mpr hw),zero_div,add_zero,← sub_div,abs_div,abs_of_pos hx0]
    exact div_le_div_of_nonneg_left (abs_nonneg _) he hx
  · have hw' : w ≤ 0 := (le_of_not_ge hw)
    have hr : rate c x v-rate c x w = v/x-(-w)/(c-x) := by
      simp [rate,max_eq_left hv,max_eq_right hw',max_eq_right (neg_nonpos.mpr hv),
        max_eq_left (neg_nonneg.mpr hw')]
    rw [hr,abs_of_nonneg (sub_nonneg.mpr (hw'.trans hv))]
    calc
      _ ≤ v/x+(-w)/(c-x) := (by simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (v/x) (-((-w)/(c-x)))) |>.trans_eq (by
        rw [abs_of_nonneg (div_nonneg hv hx0.le),abs_of_nonneg (div_nonneg (neg_nonneg.mpr hw') hc0.le)])
      _ ≤ v/eta+(-w)/eta := add_le_add
        (div_le_div_of_nonneg_left hv he hx)
        (div_le_div_of_nonneg_left (neg_nonneg.mpr hw') he hcx)
      _ = _ := by ring
  · have hv' : v ≤ 0 := le_of_not_ge hv
    have hr : rate c x v-rate c x w = (-v)/(c-x)-w/x := by
      simp [rate,max_eq_left hw,max_eq_right hv',max_eq_right (neg_nonpos.mpr hw),
        max_eq_left (neg_nonneg.mpr hv')]
    rw [hr,abs_of_nonpos (sub_nonpos.mpr (hv'.trans hw))]
    calc
      _ ≤ (-v)/(c-x)+w/x := (by simpa only [sub_eq_add_neg,abs_neg] using abs_add_le ((-v)/(c-x)) (-(w/x))) |>.trans_eq (by
        rw [abs_of_nonneg (div_nonneg (neg_nonneg.mpr hv') hc0.le),abs_of_nonneg (div_nonneg hw hx0.le)])
      _ ≤ (-v)/eta+w/eta := add_le_add
        (div_le_div_of_nonneg_left (neg_nonneg.mpr hv') he hcx)
        (div_le_div_of_nonneg_left hw he hx)
      _ = _ := by ring
  · have hv' : v ≤ 0 := le_of_not_ge hv
    have hw' : w ≤ 0 := le_of_not_ge hw
    simp only [rate,max_eq_right hv',max_eq_right hw',max_eq_left (neg_nonneg.mpr hv'),
      max_eq_left (neg_nonneg.mpr hw'),zero_div,zero_add,← sub_div,abs_div,abs_of_pos hc0]
    rw [show -v- -w = -(v-w) by ring,abs_neg]
    exact div_le_div_of_nonneg_left (abs_nonneg _) he hcx

private theorem reciprocal_error (eta x y : ℝ) (he : 0 < eta)
    (hx : eta ≤ x) (hy : eta ≤ y) :
    |x⁻¹-y⁻¹| ≤ |x-y|/eta^2 := by
  have hx0 := he.trans_le hx
  have hy0 := he.trans_le hy
  have hxy : eta^2 ≤ x*y := by nlinarith [mul_le_mul hx hy he.le hx0.le]
  have hid : |x⁻¹-y⁻¹| = |x-y|/(x*y) := by
    simpa only [Real.dist_eq,Real.norm_eq_abs,abs_of_pos hx0,abs_of_pos hy0] using
      dist_inv_inv₀ hx0.ne' hy0.ne'
  rw [hid]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos he) hxy

private theorem height_error (c eta x y w : ℝ) (he : 0 < eta)
    (hx : eta ≤ x) (hcx : eta ≤ c-x) (hy : eta ≤ y) (hcy : eta ≤ c-y) :
    |rate c x w-rate c y w| ≤ |w|*|x-y|/eta^2 := by
  have h0 := reciprocal_error eta x y he hx hy
  have h1 := reciprocal_error eta (c-x) (c-y) he hcx hcy
  rw [show (c-x)-(c-y) = -(x-y) by ring,abs_neg] at h1
  by_cases hw : 0 ≤ w
  · simp only [rate,max_eq_left hw,max_eq_right (neg_nonpos.mpr hw),zero_div,add_zero,
      div_eq_mul_inv,← mul_sub,abs_mul,abs_of_nonneg hw]
    simpa only [mul_div_assoc,abs_of_nonneg hw] using mul_le_mul_of_nonneg_left h0 hw
  · have hw' : w ≤ 0 := le_of_not_ge hw
    simp only [rate,max_eq_right hw',max_eq_left (neg_nonneg.mpr hw'),zero_div,zero_add,
      div_eq_mul_inv,← mul_sub,abs_mul,abs_neg,abs_of_nonpos hw']
    simpa only [mul_div_assoc,abs_of_nonpos hw'] using
      mul_le_mul_of_nonneg_left h1 (neg_nonneg.mpr hw')

/-- The source hazard has velocity coefficient one, with no speed bound. -/
theorem hazard_pointwise_error (c eta : ℝ) (k l : ℝ → ℝ) (t : ℝ)
    (he : 0 < eta) (hk : k t ∈ Icc eta (c-eta)) (hl : l t ∈ Icc eta (c-eta)) :
    |hazard c k t-hazard c l t| ≤
      |deriv k t-deriv l t|/eta+|deriv l t|*|k t-l t|/eta^2 := by
  have hv := velocity_error c eta (k t) (deriv k t) (deriv l t) he hk.1 (by linarith [hk.2])
  have hh := height_error c eta (k t) (l t) (deriv l t) he hk.1
    (by linarith [hk.2]) hl.1 (by linarith [hl.2])
  exact (abs_sub_le (rate c (k t) (deriv k t)) (rate c (k t) (deriv l t))
    (rate c (l t) (deriv l t))).trans (add_le_add hv hh)

/-- The actual L1 derivative discrepancy, on the common physical clock. -/
def derivativeError (T : ℝ) (k l : ℝ → ℝ) : ℝ :=
  ∫ t in Ioc (0 : ℝ) T, |deriv k t-deriv l t|

/-- For an absolutely continuous height this is its total variation. -/
def variation (T : ℝ) (k : ℝ → ℝ) : ℝ :=
  ∫ t in Ioc (0 : ℝ) T, |deriv k t|

def budget (eta delta e M : ℝ) : ℝ := e/eta+M*delta/eta^2

private theorem derivative_integrable (c T : ℝ) (k chi : ℝ → ℝ)
    (hk : OriginalControl (c,c,1-2*c) T k chi) :
    IntegrableOn (deriv k) (Ioc 0 T) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hk.1).mp
    (original_ac _ _ _ _ hk).1.intervalIntegrable_deriv

/-- IS.26's hazard estimate with the original coefficient one on velocity error. -/
theorem hazard_integral_error (c T eta delta : ℝ) (k chi l psi : ℝ → ℝ)
    (he : 0 < eta)
    (hk : OriginalControl (c,c,1-2*c) T k chi)
    (hl : OriginalControl (c,c,1-2*c) T l psi)
    (hmk : ∀ t ∈ Icc 0 T, k t ∈ Icc eta (c-eta))
    (hml : ∀ t ∈ Icc 0 T, l t ∈ Icc eta (c-eta))
    (hd : ∀ t ∈ Icc 0 T, |k t-l t| ≤ delta) :
    (∫ t in Ioc (0 : ℝ) T, |hazard c k t-hazard c l t|) ≤
      budget eta delta (derivativeError T k l) (variation T l) := by
  have hki := derivative_integrable c T k chi hk
  have hli := derivative_integrable c T l psi hl
  have hkh := (intervalIntegrable_iff_integrableOn_Ioc_of_le hk.1).mp
    (hazard_integrable c T 0 k (height_control c T k chi hk))
  have hlh := (intervalIntegrable_iff_integrableOn_Ioc_of_le hk.1).mp
    (hazard_integrable c T 0 l (height_control c T l psi hl))
  have hR := ((hki.sub hli).abs.div_const eta).add ((hli.abs.mul_const delta).div_const (eta^2))
  have hb : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) T),
      |hazard c k t-hazard c l t| ≤
        |deriv k t-deriv l t|/eta+|deriv l t|*delta/eta^2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (hazard_pointwise_error c eta k l t he (hmk t ⟨ht.1.le,ht.2⟩)
      (hml t ⟨ht.1.le,ht.2⟩)).trans
      (add_le_add_left (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hd t ⟨ht.1.le,ht.2⟩) (abs_nonneg _)) (sq_nonneg _)) _)
  have h := integral_mono_ae (hkh.sub hlh).abs hR hb
  rw [integral_add ((hki.sub hli).abs.div_const eta) ((hli.abs.mul_const delta).div_const (eta^2)),
    integral_div,integral_div,integral_mul_const] at h
  exact h

private theorem exp_negative_error (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.exp (-x)-Real.exp (-y)| ≤ |x-y| := by
  have h := norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := Real.exp) (f' := Real.exp) (s := Iic (0 : ℝ)) (C := 1)
    (fun z _ => (Real.hasDerivAt_exp z).hasDerivWithinAt)
    (fun z hz => by simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using
      Real.exp_le_one_iff.mpr hz)
    (convex_Iic 0) (neg_nonpos.mpr hy) (neg_nonpos.mpr hx)
  simpa only [Real.norm_eq_abs,one_mul,neg_sub_neg,abs_sub_comm] using h

private theorem hazard_nonneg_on (c T : ℝ) (k chi : ℝ → ℝ)
    (hk : OriginalControl (c,c,1-2*c) T k chi) (t : ℝ) (ht : t ∈ Icc 0 T) :
    0 ≤ hazard c k t := by
  have hb := OriginalRepeatedMarkedLaw.native_bounds c T 0 k (height_control c T k chi hk) t ht
  exact add_nonneg (div_nonneg (le_max_right _ _) hb.1.le)
    (div_nonneg (le_max_right _ _) (sub_pos.mpr hb.2).le)

/-- Every survival prefix is controlled by the full accumulated hazard error. -/
theorem survival_integral_error (c T : ℝ) (k chi l psi : ℝ → ℝ)
    (hk : OriginalControl (c,c,1-2*c) T k chi)
    (hl : OriginalControl (c,c,1-2*c) T l psi) (t : ℝ) (ht : t ∈ Icc 0 T) :
    |survival c k t-survival c l t| ≤
      ∫ u in Ioc (0 : ℝ) T, |hazard c k u-hazard c l u| := by
  have hki := hazard_integrable c T 0 k (height_control c T k chi hk)
  have hli := hazard_integrable c T 0 l (height_control c T l psi hl)
  have hsub : uIcc (0 : ℝ) t ⊆ uIcc 0 T := by
    rw [uIcc_of_le ht.1,uIcc_of_le hk.1]
    exact Icc_subset_Icc le_rfl ht.2
  have hki' := hki.mono_set hsub
  have hli' := hli.mono_set hsub
  have hn (q cq) (hq : OriginalControl (c,c,1-2*c) T q cq) :
      0 ≤ ∫ u in (0 : ℝ)..t,hazard c q u :=
    intervalIntegral.integral_nonneg ht.1 (fun u hu => hazard_nonneg_on c T q cq hq u ⟨hu.1,hu.2.trans ht.2⟩)
  calc
    _ ≤ |(∫ u in (0 : ℝ)..t,hazard c k u)-(∫ u in (0 : ℝ)..t,hazard c l u)| :=
      exp_negative_error _ _ (hn k chi hk) (hn l psi hl)
    _ = |∫ u in Ioc (0 : ℝ) t,hazard c k u-hazard c l u| := by
      rw [← intervalIntegral.integral_sub hki' hli',intervalIntegral.integral_of_le ht.1]
    _ ≤ ∫ u in Ioc (0 : ℝ) t,|hazard c k u-hazard c l u| :=
      by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun u => hazard c k u-hazard c l u)
    _ ≤ _ := setIntegral_mono_set
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hk.1).mp (hki.sub hli)).abs
      (ae_of_all _ (fun _ => abs_nonneg _))
      (Ioc_subset_Ioc le_rfl ht.2).eventuallySubset

/-- IS.26 supplies uniform survival control on the entire original class. -/
theorem survival_error (c T eta delta : ℝ) (k chi l psi : ℝ → ℝ)
    (he : 0 < eta)
    (hk : OriginalControl (c,c,1-2*c) T k chi)
    (hl : OriginalControl (c,c,1-2*c) T l psi)
    (hmk : ∀ t ∈ Icc 0 T, k t ∈ Icc eta (c-eta))
    (hml : ∀ t ∈ Icc 0 T, l t ∈ Icc eta (c-eta))
    (hd : ∀ t ∈ Icc 0 T, |k t-l t| ≤ delta)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    |survival c k t-survival c l t| ≤
      budget eta delta (derivativeError T k l) (variation T l) :=
  (survival_integral_error c T k chi l psi hk hl t ht).trans
    (hazard_integral_error c T eta delta k chi l psi he hk hl hmk hml hd)

private theorem survival_derivative (c T : ℝ) (k chi : ℝ → ℝ)
    (hk : OriginalControl (c,c,1-2*c) T k chi) :
    ∀ᵐ t : ℝ, t ∈ uIcc 0 T →
      deriv (survival c k) t = -hazard c k t*survival c k t := by
  have hi := hazard_integrable c T 0 k (height_control c T k chi hk)
  filter_upwards [hi.ae_hasDerivAt_integral] with t ht hmem
  have h := (ht hmem 0 (by simp)).neg.exp
  simpa only [mul_neg,neg_mul,mul_comm] using h.deriv

private theorem density_derivative (c a T : ℝ) (k chi : ℝ → ℝ)
    (hc : c < 1/2) (ha : a ∈ Ioo 0 c)
    (hk : OriginalControl (c,c,1-2*c) T k chi) (i : Fin 5) :
    ∀ᵐ t : ℝ, t ∈ uIcc 0 T →
      lossDensity c a k i t = -(deriv (survival c k) t*p c (k t) i+
        survival c k t*(FiniteRectangleTransport.direction i*deriv k t)) := by
  have h0 := height_control c T k chi hk
  have hki := (original_ac _ _ _ _ hk).1
  have hSi := survival_ac c T k h0
  filter_upwards [native_coefficient_deriv c a T k hc ha h0 i,
    hki.ae_differentiableAt,hSi.ae_differentiableAt] with t hf hkt hSt ht
  have hp : HasDerivAt (fun u => p c (k u) i)
      (FiniteRectangleTransport.direction i*deriv k t) t := by
    simpa [p] using FiniteRectangleTransport.probability_derivative
      (c,c,1-2*c) k (deriv k t) t (hkt ht).hasDerivAt i
  have hprod := (hSt ht).hasDerivAt.mul hp
  rw [lossDensity,hf ht,hprod.deriv]
  field_simp [(p_pos c a hc ha i).ne']

private theorem survival_unit (c T : ℝ) (k chi : ℝ → ℝ)
    (hk : OriginalControl (c,c,1-2*c) T k chi) (t : ℝ) (ht : t ∈ Icc 0 T) :
    0 ≤ survival c k t ∧ survival c k t ≤ 1 := by
  exact ⟨(Real.exp_pos _).le,survival_le_one c T k chi hk t ht⟩

private theorem hazard_integral_le_variation (c T eta : ℝ) (l psi : ℝ → ℝ)
    (he : 0 < eta) (hl : OriginalControl (c,c,1-2*c) T l psi)
    (hml : ∀ t ∈ Icc 0 T, l t ∈ Icc eta (c-eta)) :
    (∫ t in Ioc (0 : ℝ) T,hazard c l t) ≤ variation T l/eta := by
  have hhi := (intervalIntegrable_iff_integrableOn_Ioc_of_le hl.1).mp
    (hazard_integrable c T 0 l (height_control c T l psi hl))
  have hdi := (derivative_integrable c T l psi hl).abs.div_const eta
  have hb : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) T), hazard c l t ≤ |deriv l t|/eta := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have h := hml t ⟨ht.1.le,ht.2⟩
    have hcx : eta ≤ c-l t := by linarith [h.2]
    change max (deriv l t) 0/l t+max (-deriv l t) 0/(c-l t) ≤ _
    calc
      _ ≤ max (deriv l t) 0/eta+max (-deriv l t) 0/eta :=
        add_le_add (div_le_div_of_nonneg_left (le_max_right _ _) he h.1)
          (div_le_div_of_nonneg_left (le_max_right _ _) he hcx)
      _ = _ := by
        rw [← add_div]
        congr 1
        by_cases hv : 0 ≤ deriv l t
        · simp [max_eq_left hv,max_eq_right (neg_nonpos.mpr hv),abs_of_nonneg hv]
        · have hv' := le_of_not_ge hv
          simp [max_eq_right hv',max_eq_left (neg_nonneg.mpr hv'),abs_of_nonpos hv']
  have h := integral_mono_ae hhi hdi hb
  simpa only [integral_div,variation] using h

private theorem survival_derivative_error (c T eta delta : ℝ) (k chi l psi : ℝ → ℝ)
    (he : 0 < eta)
    (hk : OriginalControl (c,c,1-2*c) T k chi)
    (hl : OriginalControl (c,c,1-2*c) T l psi)
    (hmk : ∀ t ∈ Icc 0 T, k t ∈ Icc eta (c-eta))
    (hml : ∀ t ∈ Icc 0 T, l t ∈ Icc eta (c-eta))
    (hd : ∀ t ∈ Icc 0 T, |k t-l t| ≤ delta) :
    (∫ t in Ioc (0 : ℝ) T,|deriv (survival c k) t-deriv (survival c l) t|) ≤
      (1+variation T l/eta)*budget eta delta (derivativeError T k l) (variation T l) := by
  let B := budget eta delta (derivativeError T k l) (variation T l)
  have hB : 0 ≤ B := (abs_nonneg _).trans
    (survival_error c T eta delta k chi l psi he hk hl hmk hml hd 0 ⟨le_rfl,hk.1⟩)
  have hki := (intervalIntegrable_iff_integrableOn_Ioc_of_le hk.1).mp
    (survival_ac c T k (height_control c T k chi hk)).intervalIntegrable_deriv
  have hli := (intervalIntegrable_iff_integrableOn_Ioc_of_le hk.1).mp
    (survival_ac c T l (height_control c T l psi hl)).intervalIntegrable_deriv
  have hkh := (intervalIntegrable_iff_integrableOn_Ioc_of_le hk.1).mp
    (hazard_integrable c T 0 k (height_control c T k chi hk))
  have hlh := (intervalIntegrable_iff_integrableOn_Ioc_of_le hk.1).mp
    (hazard_integrable c T 0 l (height_control c T l psi hl))
  have hb : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) T),
      |deriv (survival c k) t-deriv (survival c l) t| ≤
        |hazard c k t-hazard c l t|+B*hazard c l t := by
    have hak := survival_derivative c T k chi hk
    have hal := survival_derivative c T l psi hl
    filter_upwards [ae_restrict_of_ae hak,ae_restrict_of_ae hal,
      ae_restrict_mem measurableSet_Ioc] with t hkt hlt ht
    have ht' : t ∈ Icc 0 T := ⟨ht.1.le,ht.2⟩
    have htu : t ∈ uIcc 0 T := by simpa only [uIcc_of_le hk.1] using ht'
    rw [hkt htu,hlt htu]
    have hS := survival_unit c T k chi hk t ht'
    have hl0 := hazard_nonneg_on c T l psi hl t ht'
    have hs := survival_error c T eta delta k chi l psi he hk hl hmk hml hd t ht'
    calc
      _ = |-(hazard c k t-hazard c l t)*survival c k t-
          hazard c l t*(survival c k t-survival c l t)| := by congr 1; ring
      _ ≤ |hazard c k t-hazard c l t|*survival c k t+
          hazard c l t*|survival c k t-survival c l t| := by
        simpa only [abs_mul,abs_neg,abs_of_nonneg hS.1,abs_of_nonneg hl0] using
          (by simpa only [sub_eq_add_neg,abs_neg] using
            abs_add_le (-(hazard c k t-hazard c l t)*survival c k t)
              (-(hazard c l t*(survival c k t-survival c l t))))
      _ ≤ |hazard c k t-hazard c l t|*1+hazard c l t*B := by gcongr
      _ = _ := by ring
  have h := integral_mono_ae (hki.sub hli).abs ((hkh.sub hlh).abs.add (hlh.const_mul B)) hb
  rw [integral_add (hkh.sub hlh).abs (hlh.const_mul B),integral_const_mul] at h
  have h0 := hazard_integral_error c T eta delta k chi l psi he hk hl hmk hml hd
  have h1 := hazard_integral_le_variation c T eta l psi he hl hml
  exact h.trans ((add_le_add h0 (mul_le_mul_of_nonneg_left h1 hB)).trans_eq (by dsimp [B]; ring))

private theorem survival_total_variation (c T : ℝ) (l psi : ℝ → ℝ)
    (hl : OriginalControl (c,c,1-2*c) T l psi) :
    (∫ t in Ioc (0 : ℝ) T,|deriv (survival c l) t|) ≤ 1 := by
  have ha := survival_ac c T l (height_control c T l psi hl)
  have he : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) T),
      |deriv (survival c l) t| = -deriv (survival c l) t := by
    filter_upwards [ae_restrict_of_ae (survival_derivative c T l psi hl),
      ae_restrict_mem measurableSet_Ioc] with t ht hmem
    have htu : t ∈ uIcc 0 T := by simpa only [uIcc_of_le hl.1] using ⟨hmem.1.le,hmem.2⟩
    rw [ht htu,abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (hazard_nonneg_on c T l psi hl t ⟨hmem.1.le,hmem.2⟩)) (Real.exp_pos _).le)]
  rw [integral_congr_ae he,integral_neg,← intervalIntegral.integral_of_le hl.1,ha.integral_deriv_eq_sub]
  have h0 : survival c l 0 = 1 := by simp [OriginalControlSurvivalInstability.survival]
  rw [h0]
  have hn : 0 ≤ survival c l T := (Real.exp_pos _).le
  linarith

private theorem product_loss_error (S U s u x y v w r B delta : ℝ)
    (hp : |x| ≤ 1) (hpd : |x-y| ≤ delta) (hS : |S-U| ≤ B)
    (hU : |U| ≤ 1) (hr : |r| ≤ 1) :
    |-(s*x+S*(r*v)) - -(u*y+U*(r*w))| ≤
      |s-u|+delta*|u|+B*|v|+|v-w| := by
  calc
    _ = |(s-u)*x+u*(x-y)+(S-U)*r*v+U*r*(v-w)| := by
      rw [show -(s*x+S*(r*v)) - -(u*y+U*(r*w)) =
        -((s-u)*x+u*(x-y)+(S-U)*r*v+U*r*(v-w)) by ring,abs_neg]
    _ ≤ |(s-u)*x+u*(x-y)+(S-U)*r*v|+|U*r*(v-w)| := abs_add_le _ _
    _ ≤ (|(s-u)*x+u*(x-y)|+|(S-U)*r*v|)+|U*r*(v-w)| := by
      gcongr; exact abs_add_le _ _
    _ ≤ ((|(s-u)*x|+|u*(x-y)|)+|(S-U)*r*v|)+|U*r*(v-w)| := by
      gcongr; exact abs_add_le _ _
    _ = ((|s-u|*|x|+|u|*|x-y|)+|S-U|*|r|*|v|)+|U|*|r|*|v-w| := by simp only [abs_mul]
    _ ≤ ((|s-u|*1+|u|*delta)+B*1*|v|)+1*1*|v-w| := by gcongr
    _ = _ := by ring

/-- IS.28 is an L1 bound on all five original loss densities, on the actual clock. -/
theorem loss_density_error (c a T eta delta : ℝ) (k chi l psi : ℝ → ℝ)
    (hc : c < 1/2) (ha : a ∈ Ioo 0 c) (he : 0 < eta)
    (hk : OriginalControl (c,c,1-2*c) T k chi)
    (hl : OriginalControl (c,c,1-2*c) T l psi)
    (hmk : ∀ t ∈ Icc 0 T, k t ∈ Icc eta (c-eta))
    (hml : ∀ t ∈ Icc 0 T, l t ∈ Icc eta (c-eta))
    (hd : ∀ t ∈ Icc 0 T, |k t-l t| ≤ delta) (i : Fin 5) :
    (∫ t in Ioc (0 : ℝ) T, |lossDensity c a k i t-lossDensity c a l i t|) ≤
      (1+variation T l/eta+variation T k)*
        budget eta delta (derivativeError T k l) (variation T l)+delta+derivativeError T k l := by
  let B := budget eta delta (derivativeError T k l) (variation T l)
  have hd0 : 0 ≤ delta := (abs_nonneg _).trans (hd 0 ⟨le_rfl,hk.1⟩)
  have hB : 0 ≤ B := (abs_nonneg _).trans
    (survival_error c T eta delta k chi l psi he hk hl hmk hml hd 0 ⟨le_rfl,hk.1⟩)
  have hks := survival_ac c T k (height_control c T k chi hk)
  have hls := survival_ac c T l (height_control c T l psi hl)
  have hksi := (intervalIntegrable_iff_integrableOn_Ioc_of_le hk.1).mp hks.intervalIntegrable_deriv
  have hlsi := (intervalIntegrable_iff_integrableOn_Ioc_of_le hk.1).mp hls.intervalIntegrable_deriv
  have hki := derivative_integrable c T k chi hk
  have hli := derivative_integrable c T l psi hl
  have hf (q cq) (hq : OriginalControl (c,c,1-2*c) T q cq) :
      IntegrableOn (lossDensity c a q i) (Ioc 0 T) :=
    ((native_mode_balance c a T q hc ha (height_control c T q cq hq)
      i 0 T ⟨le_rfl,hk.1⟩ ⟨hk.1,le_rfl⟩ hk.1).1).mul_const _
  have hR := (((hksi.sub hlsi).abs.add (hlsi.abs.const_mul delta)).add
    (hki.abs.const_mul B)).add (hki.sub hli).abs
  have hb : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) T),
      |lossDensity c a k i t-lossDensity c a l i t| ≤
        |deriv (survival c k) t-deriv (survival c l) t|+
        delta*|deriv (survival c l) t|+B*|deriv k t|+|deriv k t-deriv l t| := by
    filter_upwards [ae_restrict_of_ae (density_derivative c a T k chi hc ha hk i),
      ae_restrict_of_ae (density_derivative c a T l psi hc ha hl i),
      ae_restrict_mem measurableSet_Ioc] with t hkt hlt ht
    have ht' : t ∈ Icc 0 T := ⟨ht.1.le,ht.2⟩
    have htu : t ∈ uIcc 0 T := by simpa only [uIcc_of_le hk.1] using ht'
    rw [hkt htu,hlt htu]
    have hp := p_pos c (k t) hc
      (OriginalRepeatedMarkedLaw.native_bounds c T 0 k (height_control c T k chi hk) t ht') i
    have hp1 := probability_le_one c (k t) hc
      (OriginalRepeatedMarkedLaw.native_bounds c T 0 k (height_control c T k chi hk) t ht') i
    have hsig : |FiniteRectangleTransport.direction i| ≤ 1 := by
      fin_cases i <;> norm_num [FiniteRectangleTransport.direction]
    exact product_loss_error _ _ _ _ _ _ _ _ _ B delta
      (by rwa [abs_of_pos hp]) ((probability_difference c _ _ i).trans (hd t ht'))
      (survival_error c T eta delta k chi l psi he hk hl hmk hml hd t ht')
      (by rw [abs_of_pos (Real.exp_pos _)]; exact (survival_unit c T l psi hl t ht').2) hsig
  have h := integral_mono_ae ((hf k chi hk).sub (hf l psi hl)).abs hR hb
  rw [integral_add (((hksi.sub hlsi).abs.add (hlsi.abs.const_mul delta)).add (hki.abs.const_mul B))
      (hki.sub hli).abs,
    integral_add ((hksi.sub hlsi).abs.add (hlsi.abs.const_mul delta)) (hki.abs.const_mul B),
    integral_add (hksi.sub hlsi).abs (hlsi.abs.const_mul delta),
    integral_const_mul,integral_const_mul] at h
  have hq := survival_derivative_error c T eta delta k chi l psi he hk hl hmk hml hd
  have hv := survival_total_variation c T l psi hl
  calc
    _ ≤ ((∫ t in Ioc (0 : ℝ) T,|deriv (survival c k) t-deriv (survival c l) t|)+
      delta*(∫ t in Ioc (0 : ℝ) T,|deriv (survival c l) t|))+
      B*variation T k+derivativeError T k l := h
    _ ≤ ((1+variation T l/eta)*B+delta*1)+B*variation T k+derivativeError T k l := by
      gcongr
    _ = _ := by dsimp [B]; ring

/-- Derivative error bounds the extra height variation without a speed hypothesis. -/
theorem variation_le (c T : ℝ) (k chi l psi : ℝ → ℝ)
    (hk : OriginalControl (c,c,1-2*c) T k chi)
    (hl : OriginalControl (c,c,1-2*c) T l psi) :
    variation T k ≤ variation T l+derivativeError T k l := by
  have hki := derivative_integrable c T k chi hk
  have hli := derivative_integrable c T l psi hl
  have h := integral_mono hki.abs (hli.abs.add (hki.sub hli).abs)
    (fun t => by simpa only [add_comm] using abs_sub_le (deriv k t) (deriv l t) (0 : ℝ))
  simpa only [integral_add hli.abs (hki.sub hli).abs,variation,derivativeError] using h

/-- The least common initial probability includes mode 2 and mode 13. -/
def initialFloor (c a : ℝ) : ℝ := min a (min (c-a) (1-2*c))

private theorem initialFloor_pos (c a : ℝ) (hc : c < 1/2) (ha : a ∈ Ioo 0 c) :
    0 < initialFloor c a := by
  exact lt_min ha.1 (lt_min (sub_pos.mpr ha.2) (by linarith))

private theorem initialFloor_le (c a : ℝ) (i : Fin 5) : initialFloor c a ≤ p c a i := by
  rw [p_explicit]
  have h0 := min_le_left a (min (c-a) (1-2*c))
  have h1 := (min_le_right a (min (c-a) (1-2*c))).trans (min_le_left (c-a) (1-2*c))
  have h2 := (min_le_right a (min (c-a) (1-2*c))).trans (min_le_right (c-a) (1-2*c))
  fin_cases i <;> simp_all [initialFloor]

def phaseError (c T : ℝ) (k chi l psi : ℝ → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun i : Fin 5 => ‖character c k chi T i-character c l psi T i‖)

/-- The explicit combined IS.27--IS.29 bound concerns the actual complete output. -/
theorem complete_error_bound (c a T eta delta : ℝ) (k chi l psi : ℝ → ℝ)
    (hc : c < 1/2) (ha : a ∈ Ioo 0 c) (he : 0 < eta)
    (hk : OriginalControl (c,c,1-2*c) T k chi)
    (hl : OriginalControl (c,c,1-2*c) T l psi) (hk0 : k 0=a) (hl0 : l 0=a)
    (hmk : ∀ t ∈ Icc 0 T, k t ∈ Icc eta (c-eta))
    (hml : ∀ t ∈ Icc 0 T, l t ∈ Icc eta (c-eta))
    (hd : ∀ t ∈ Icc 0 T, |k t-l t| ≤ delta) :
    completeOperationalDistance.{v} c a T k chi l psi ≤
      Real.sqrt ((budget eta delta (derivativeError T k l) (variation T l)+delta)/initialFloor c a)+
      phaseError c T k chi l psi+
      ((1+variation T l/eta+variation T k)*
        budget eta delta (derivativeError T k l) (variation T l)+delta+derivativeError T k l)/
        (2*initialFloor c a) := by
  let B := budget eta delta (derivativeError T k l) (variation T l)
  let C := (1+variation T l/eta+variation T k)*B+delta+derivativeError T k l
  have hd0 : 0 ≤ delta := (abs_nonneg _).trans (hd 0 ⟨le_rfl,hk.1⟩)
  have hB : 0 ≤ B := (abs_nonneg _).trans
    (survival_error c T eta delta k chi l psi he hk hl hmk hml hd 0 ⟨le_rfl,hk.1⟩)
  have hC : 0 ≤ C := (integral_nonneg (fun _ => abs_nonneg _)).trans
    (loss_density_error c a T eta delta k chi l psi hc ha he hk hl hmk hml hd 0)
  have hdmin := initialFloor_pos c a hc ha
  have hb : ∀ i : Fin 5, densityError c a T k l i ≤ C/initialFloor c a := by
    intro i
    exact (div_le_div_of_nonneg_right
      (loss_density_error c a T eta delta k chi l psi hc ha he hk hl hmk hml hd i)
      (p_pos c a hc ha i).le).trans
      (div_le_div_of_nonneg_left hC hdmin (initialFloor_le c a i))
  have hbmax : Finset.univ.sup' Finset.univ_nonempty (densityError c a T k l) ≤ C/initialFloor c a :=
    Finset.sup'_le _ _ (fun i _ => hb i)
  have hterm := terminal_error_bound c a T B delta k chi l psi hc ha hk hl hk0 hl0
    (survival_error c T eta delta k chi l psi he hk hl hmk hml hd T ⟨hk.1,le_rfl⟩)
    (hd T ⟨hk.1,le_rfl⟩)
  have hroot : Finset.univ.sup' Finset.univ_nonempty
      (fun i : Fin 5 => Real.sqrt ((B+delta)/p c a i)) ≤ Real.sqrt ((B+delta)/initialFloor c a) := by
    apply Finset.sup'_le
    intro i _
    exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (add_nonneg hB hd0) hdmin (initialFloor_le c a i))
  have hop := complete_operational_bound.{v} c a T k chi l psi hc ha hk hl hk0 hl0
  calc
    _ ≤ krausError c a T k chi l psi+
      (Finset.univ.sup' Finset.univ_nonempty (densityError c a T k l))/2 := hop
    _ ≤ (Real.sqrt ((B+delta)/initialFloor c a)+phaseError c T k chi l psi)+
      (C/initialFloor c a)/2 := by gcongr; exact hterm.trans (add_le_add_right hroot _)
    _ = _ := by dsimp [B,C]; ring

/-- Common initial height upgrades L1 derivative error to uniform height error. -/
theorem height_error_le_derivativeError (c T : ℝ) (k chi l psi : ℝ → ℝ)
    (hk : OriginalControl (c,c,1-2*c) T k chi)
    (hl : OriginalControl (c,c,1-2*c) T l psi) (h0 : k 0=l 0)
    (t : ℝ) (ht : t ∈ Icc 0 T) : |k t-l t| ≤ derivativeError T k l := by
  have hsub : uIcc (0 : ℝ) t ⊆ uIcc 0 T := by
    rw [uIcc_of_le ht.1,uIcc_of_le hk.1]
    exact Icc_subset_Icc le_rfl ht.2
  have hki := ((original_ac _ _ _ _ hk).1.mono hsub)
  have hli := ((original_ac _ _ _ _ hl).1.mono hsub)
  have hEq : k t-l t = ∫ u in Ioc (0 : ℝ) t,deriv k u-deriv l u := by
    rw [← intervalIntegral.integral_of_le ht.1,
      intervalIntegral.integral_sub hki.intervalIntegrable_deriv hli.intervalIntegrable_deriv,
      hki.integral_deriv_eq_sub,hli.integral_deriv_eq_sub,h0]
    ring
  rw [hEq]
  exact (by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
    (fun u => deriv k u-deriv l u)).trans
    (setIntegral_mono_set ((derivative_integrable c T k chi hk).sub
      (derivative_integrable c T l psi hl)).abs
      (ae_of_all _ (fun _ => abs_nonneg _)) (Ioc_subset_Ioc le_rfl ht.2).eventuallySubset)

/-- Strong derivative convergence and a separate terminal character certificate
give convergence of the actual complete output, with no common speed bound. -/
theorem complete_output_convergence (c a T eta M : ℝ)
    (k chi l psi : ℕ → ℝ → ℝ)
    (hc : c < 1/2) (ha : a ∈ Ioo 0 c) (he : 0 < eta)
    (hk : ∀ n, OriginalControl (c,c,1-2*c) T (k n) (chi n))
    (hl : ∀ n, OriginalControl (c,c,1-2*c) T (l n) (psi n))
    (hk0 : ∀ n, k n 0=a) (hl0 : ∀ n, l n 0=a)
    (hmk : ∀ n t, t ∈ Icc 0 T → k n t ∈ Icc eta (c-eta))
    (hml : ∀ n t, t ∈ Icc 0 T → l n t ∈ Icc eta (c-eta))
    (hM : ∀ n, variation T (l n) ≤ M)
    (helim : Tendsto (fun n => derivativeError T (k n) (l n)) atTop (𝓝 0))
    (hzlim : Tendsto (fun n => phaseError c T (k n) (chi n) (l n) (psi n)) atTop (𝓝 0)) :
    Tendsto (fun n => completeOperationalDistance.{v} c a T (k n) (chi n) (l n) (psi n))
      atTop (𝓝 0) := by
  let e := fun n => derivativeError T (k n) (l n)
  let b := fun n => budget eta (e n) (e n) M
  let upper := fun n => Real.sqrt ((b n+e n)/initialFloor c a)+
    phaseError c T (k n) (chi n) (l n) (psi n)+
    ((1+M/eta+(M+e n))*b n+e n+e n)/(2*initialFloor c a)
  have hM0 : 0 ≤ M := (integral_nonneg (fun _ => abs_nonneg _)).trans (hM 0)
  have he0 (n) : 0 ≤ e n := integral_nonneg (fun _ => abs_nonneg _)
  have hb0 (n) : 0 ≤ b n := by
    dsimp [b,budget]
    positivity
  have hbound (n) : completeOperationalDistance.{v} c a T (k n) (chi n) (l n) (psi n) ≤ upper n := by
    have hd := height_error_le_derivativeError c T (k n) (chi n) (l n) (psi n)
      (hk n) (hl n) ((hk0 n).trans (hl0 n).symm)
    have h := complete_error_bound.{v} c a T eta (e n) (k n) (chi n) (l n) (psi n)
      hc ha he (hk n) (hl n) (hk0 n) (hl0 n) (hmk n) (hml n) hd
    have hB : budget eta (e n) (e n) (variation T (l n)) ≤ b n := by
      dsimp only [budget,b]
      gcongr
      exact hM n
    have hD : variation T (k n) ≤ M+e n :=
      (variation_le c T (k n) (chi n) (l n) (psi n) (hk n) (hl n)).trans
        (add_le_add_right (hM n) _)
    have hbudget : 0 ≤ budget eta (e n) (e n) (variation T (l n)) := by
      have hv : 0 ≤ variation T (l n) := integral_nonneg (fun _ => abs_nonneg _)
      dsimp [budget]
      positivity
    refine h.trans ?_
    dsimp only [upper]
    gcongr
    · exact initialFloor_pos c a hc ha
    · exact hB
    · exact hM n
    · exact hD
    · exact hB
  let F : ℝ × ℝ → ℝ := fun x =>
    Real.sqrt ((budget eta x.1 x.1 M+x.1)/initialFloor c a)+x.2+
      ((1+M/eta+(M+x.1))*budget eta x.1 x.1 M+x.1+x.1)/(2*initialFloor c a)
  have hF : Continuous F := by dsimp [F,budget]; fun_prop
  have hu : Tendsto upper atTop (𝓝 0) := by
    have h := (hF.tendsto (0,0)).comp (helim.prodMk_nhds hzlim)
    simpa [F,upper,b,budget,e] using h
  exact squeeze_zero
    (fun n => complete_operational_nonneg.{v} c a T (k n) (chi n) (l n) (psi n)
      hc ha (hk n) (hl n) (hk0 n) (hl0 n)) hbound hu

end D5.S3.Quantum.Fibers.OriginalDensityStability
