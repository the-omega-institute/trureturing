/- GID: D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTailL1Mass
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:actual-halfline-l1-mass)
   anchors: []
   utility: none
   digest: Exact endpoint mass and the optimal uniform half-line L1 tail constant. -/

import D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-! Half-line L1 tail integrability and its literal endpoint mass. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail

open MeasureTheory Set Filter
open scoped Topology Convolution

private theorem l1_integral_translate_halfline (f : ℝ → ℂ) (t : ℝ) :
    (∫ s : ℝ in Ioi 0, f (t + s)) = ∫ s : ℝ in Ioi t, f s := by
  calc
    (∫ s : ℝ in Ioi 0, f (t + s)) =
        ∫ s : ℝ, (Ioi (0 : ℝ)).indicator (fun x : ℝ => f (t + x)) s :=
      (integral_indicator measurableSet_Ioi).symm
    _ = ∫ s : ℝ, (Ioi t).indicator f (t + s) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun s => by
        by_cases hs : 0 < s
        · have hts : t < t + s := by linarith
          simp only [Set.indicator_apply, Set.mem_Ioi, if_pos hs, if_pos hts]
        · have hts : ¬ t < t + s := by linarith
          simp only [Set.indicator_apply, Set.mem_Ioi, if_neg hs, if_neg hts]
    _ = ∫ s : ℝ, (Ioi t).indicator f s := integral_add_left_eq_self _ t
    _ = ∫ s : ℝ in Ioi t, f s := integral_indicator measurableSet_Ioi

private theorem l1_tail_weighted_eq (k : ℝ) (u : ℝ → ℂ) (t : ℝ) :
    rightExponentialTail k u t =
      (Real.exp (k * t) : ℂ) *
        ∫ x : ℝ in Ioi t, (Real.exp (-k * x) : ℂ) * u x := by
  calc
    rightExponentialTail k u t =
        ∫ s : ℝ in Ioi 0,
          (Real.exp (k * t) : ℂ) *
            ((Real.exp (-k * (t + s)) : ℂ) * u (t + s)) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun s => by
        have he : (Real.exp (-k * s) : ℂ) =
            (Real.exp (k * t) : ℂ) * (Real.exp (-k * (t + s)) : ℂ) := by
          rw [← Complex.ofReal_mul, ← Real.exp_add]
          congr 2
          ring
        change (Real.exp (-k * s) : ℂ) * u (t + s) = _
        rw [he]
        ring
    _ = (Real.exp (k * t) : ℂ) *
        ∫ s : ℝ in Ioi 0, (Real.exp (-k * (t + s)) : ℂ) * u (t + s) :=
      integral_const_mul _ _
    _ = _ := congrArg (fun z : ℂ => (Real.exp (k * t) : ℂ) * z)
      (l1_integral_translate_halfline
        (fun x : ℝ => (Real.exp (-k * x) : ℂ) * u x) t)

/-- The actual tail is integrable on the positive half-line for every L1
input there. Its integral keeps the literal endpoint trace, rather than
assuming that trace vanishes. -/
theorem right_exponential_tail_l1_integrable_and_mass
    {k : ℝ} (hk : 0 < k) (u : ℝ → ℂ)
    (hu : IntegrableOn u (Ioi (0 : ℝ))) :
    IntegrableOn (rightExponentialTail k u) (Ioi (0 : ℝ)) ∧
    (∫ t : ℝ in Ioi 0, rightExponentialTail k u t) =
      ((k⁻¹ : ℝ) : ℂ) *
        ((∫ t : ℝ in Ioi 0, u t) - rightExponentialTail k u 0) := by
  let G : ℝ → ℂ := (Ioi (0 : ℝ)).indicator u
  let K : ℝ → ℂ := (Iic (0 : ℝ)).indicator
    (fun t : ℝ => (Real.exp (k * t) : ℂ))
  have hG : Integrable G volume :=
    (integrable_indicator_iff measurableSet_Ioi).2 hu
  have hK : Integrable K volume :=
    (integrable_indicator_iff measurableSet_Iic).2
      (integrableOn_exp_mul_Iic hk 0).ofReal
  have hKmass : (∫ t : ℝ, K t) = ((k⁻¹ : ℝ) : ℂ) := by
    dsimp only [K]
    rw [integral_indicator measurableSet_Iic, integral_complex_ofReal,
      integral_exp_mul_Iic hk 0]
    simp
  have hGmass : (∫ t : ℝ, G t) = ∫ t : ℝ in Ioi 0, u t :=
    integral_indicator measurableSet_Ioi
  have hconv (t : ℝ) :
      (K ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] G) t =
        rightExponentialTail k G t := by
    change (∫ s : ℝ, K s * G (t - s)) = _
    calc
      (∫ s : ℝ, K s * G (t - s)) =
          ∫ s : ℝ in Iic 0, (Real.exp (k * s) : ℂ) * G (t - s) := by
        rw [← integral_indicator measurableSet_Iic]
        apply integral_congr_ae
        exact Eventually.of_forall fun s => by
          by_cases hs : s ∈ Iic (0 : ℝ) <;> simp [K, hs]
      _ = ∫ s : ℝ in Ioi 0, (Real.exp (k * (-s)) : ℂ) * G (t - (-s)) := by
        simpa only [neg_zero] using
          (integral_comp_neg_Ioi 0
            (fun s : ℝ => (Real.exp (k * s) : ℂ) * G (t - s))).symm
      _ = rightExponentialTail k G t := by
        simp only [rightExponentialTail, mul_neg, neg_mul, sub_neg_eq_add]
  have hRG : Integrable (rightExponentialTail k G) volume := by
    rw [← funext hconv]
    exact hK.integrable_convolution (ContinuousLinearMap.mul ℝ ℂ) hG
  have hwhole :
      (∫ t : ℝ, rightExponentialTail k G t) =
        ((k⁻¹ : ℝ) : ℂ) * ∫ t : ℝ in Ioi 0, u t := by
    rw [← funext hconv,
      integral_convolution (ContinuousLinearMap.mul ℝ ℂ) hK hG,
      hKmass, hGmass]
    rfl
  have hpositive (t : ℝ) (ht : 0 ≤ t) :
      rightExponentialTail k G t = rightExponentialTail k u t := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hts : t + s ∈ Ioi (0 : ℝ) := by
      change 0 < t + s
      exact add_pos_of_nonneg_of_pos ht (show 0 < s from hs)
    simp only [G, Set.indicator_of_mem hts]
  have hnegative (t : ℝ) (ht : t ≤ 0) :
      rightExponentialTail k G t =
        (Real.exp (k * t) : ℂ) * rightExponentialTail k G 0 := by
    rw [l1_tail_weighted_eq]
    have he :
        (∫ x : ℝ in Ioi t, (Real.exp (-k * x) : ℂ) * G x) =
          ∫ x : ℝ in Ioi 0, (Real.exp (-k * x) : ℂ) * G x := by
      rw [← integral_indicator measurableSet_Ioi,
        ← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        by_cases hx : 0 < x
        · have htx : t < x := lt_of_le_of_lt ht hx
          simp [Set.mem_Ioi, hx, htx]
        · simp [G, Set.mem_Ioi, hx]
    rw [he]
    congr 1
    simp only [rightExponentialTail, zero_add]
  have hleft :
      (∫ t : ℝ in Iic 0, rightExponentialTail k G t) =
        ((k⁻¹ : ℝ) : ℂ) * rightExponentialTail k G 0 := by
    calc
      _ = ∫ t : ℝ in Iic 0,
          (Real.exp (k * t) : ℂ) * rightExponentialTail k G 0 := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
        exact hnegative t ht
      _ = _ := by
        rw [integral_mul_const, integral_complex_ofReal, integral_exp_mul_Iic hk 0]
        simp
  have hposae : rightExponentialTail k G =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      rightExponentialTail k u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hpositive t ht.le
  refine ⟨hRG.integrableOn.congr hposae, ?_⟩
  have hparts := intervalIntegral.integral_Iic_add_Ioi
    hRG.integrableOn hRG.integrableOn (b := (0 : ℝ))
  rw [hleft, hwhole, integral_congr_ae hposae,
    hpositive 0 le_rfl] at hparts
  linear_combination hparts

private theorem l1_tail_ofReal (k : ℝ) (v : ℝ → ℝ) (t : ℝ) :
    rightExponentialTail k (fun x => (v x : ℂ)) t =
      ((∫ s : ℝ in Ioi 0, Real.exp (-k * s) * v (t + s) : ℝ) : ℂ) := by
  change (∫ s : ℝ in Ioi 0, (Real.exp (-k * s) : ℂ) * (v (t + s) : ℂ)) = _
  simp_rw [← Complex.ofReal_mul]
  exact integral_complex_ofReal

private theorem l1_tail_norm_bound {k : ℝ} (hk : 0 < k) (u : ℝ → ℂ)
    (hu : IntegrableOn u (Ioi (0 : ℝ))) :
    (∫ t : ℝ in Ioi 0, ‖rightExponentialTail k u t‖) ≤
      k⁻¹ * ∫ t : ℝ in Ioi 0, ‖u t‖ := by
  let v : ℝ → ℂ := fun t => (‖u t‖ : ℂ)
  have hv : IntegrableOn v (Ioi (0 : ℝ)) := hu.norm.ofReal
  obtain ⟨hRu, _⟩ := right_exponential_tail_l1_integrable_and_mass hk u hu
  obtain ⟨hRv, hm⟩ := right_exponential_tail_l1_integrable_and_mass hk v hv
  have hvreal (t : ℝ) :
      (rightExponentialTail k v t).re =
        ∫ s : ℝ in Ioi 0, Real.exp (-k * s) * ‖u (t + s)‖ := by
    rw [show v = (fun t => (‖u t‖ : ℂ)) from rfl, l1_tail_ofReal]
    rfl
  have hpoint (t : ℝ) :
      ‖rightExponentialTail k u t‖ ≤ (rightExponentialTail k v t).re := by
    rw [hvreal]
    simpa only [rightExponentialTail, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      norm_integral_le_integral_norm
        (fun s : ℝ => (Real.exp (-k * s) : ℂ) * u (t + s))
        (μ := volume.restrict (Ioi (0 : ℝ)))
  have hzero : 0 ≤ (rightExponentialTail k v 0).re := by
    rw [hvreal]
    exact integral_nonneg fun s => mul_nonneg (Real.exp_nonneg _) (norm_nonneg _)
  have hvmass :
      (∫ t : ℝ in Ioi 0, v t) = ((∫ t : ℝ in Ioi 0, ‖u t‖ : ℝ) : ℂ) :=
    integral_complex_ofReal
  have hmreal :
      (∫ t : ℝ in Ioi 0, (rightExponentialTail k v t).re) =
        k⁻¹ * ((∫ t : ℝ in Ioi 0, ‖u t‖) -
          (rightExponentialTail k v 0).re) := by
    have hre :
        (∫ t : ℝ in Ioi 0, (rightExponentialTail k v t).re) =
          (∫ t : ℝ in Ioi 0, rightExponentialTail k v t).re := by
      simpa only [RCLike.re_eq_complex_re] using (integral_re hRv)
    rw [hre, hm, hvmass]
    simp
  calc
    _ ≤ ∫ t : ℝ in Ioi 0, (rightExponentialTail k v t).re :=
      integral_mono hRu.norm hRv.re hpoint
    _ = _ := hmreal
    _ ≤ k⁻¹ * ∫ t : ℝ in Ioi 0, ‖u t‖ := by
      exact mul_le_mul_of_nonneg_left (sub_le_self _ hzero) (inv_pos.mpr hk).le

private def l1_exp_profile (a : ℝ) (t : ℝ) : ℂ :=
  (Real.exp (-a * t) : ℂ)

private theorem l1_exp_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (l1_exp_profile a) (Ioi (0 : ℝ)) :=
  (integrableOn_exp_mul_Ioi (a := -a) (neg_neg_of_pos ha) 0).ofReal

private theorem l1_exp_norm_mass {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ in Ioi 0, ‖l1_exp_profile a t‖) = a⁻¹ := by
  simp only [l1_exp_profile, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  rw [integral_exp_mul_Ioi (a := -a) (neg_neg_of_pos ha) 0]
  simp

private theorem l1_exp_tail {k a : ℝ} (hk : 0 < k) (ha : 0 < a) (t : ℝ) :
    rightExponentialTail k (l1_exp_profile a) t =
      (((k + a)⁻¹ : ℝ) : ℂ) * l1_exp_profile a t := by
  calc
    _ = ∫ s : ℝ in Ioi 0,
        (Real.exp (-(k + a) * s) : ℂ) * l1_exp_profile a t := by
      apply integral_congr_ae
      exact Eventually.of_forall fun s => by
        change (Real.exp (-k * s) : ℂ) *
          (Real.exp (-a * (t + s)) : ℂ) =
          (Real.exp (-(k + a) * s) : ℂ) * (Real.exp (-a * t) : ℂ)
        rw [← Complex.ofReal_mul, ← Complex.ofReal_mul,
          ← Real.exp_add, ← Real.exp_add]
        congr 2
        ring
    _ = (∫ s : ℝ in Ioi 0, (Real.exp (-(k + a) * s) : ℂ)) *
        l1_exp_profile a t := integral_mul_const _ _
    _ = _ := by
      have hint :
          (∫ s : ℝ in Ioi 0, Real.exp (-(k + a) * s)) = (k + a)⁻¹ := by
        rw [integral_exp_mul_Ioi (a := -(k + a)) (by linarith) 0]
        simp only [mul_zero, Real.exp_zero, neg_div_neg_eq, one_div]
      rw [integral_complex_ofReal, hint]

private theorem l1_exp_tail_norm_mass {k a : ℝ} (hk : 0 < k) (ha : 0 < a) :
    (∫ t : ℝ in Ioi 0, ‖rightExponentialTail k (l1_exp_profile a) t‖) =
      (k + a)⁻¹ * a⁻¹ := by
  have hnorm (t : ℝ) :
      ‖rightExponentialTail k (l1_exp_profile a) t‖ =
        (k + a)⁻¹ * ‖l1_exp_profile a t‖ := by
    rw [l1_exp_tail hk ha, norm_mul]
    congr 1
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (add_pos hk ha))]
  simp_rw [hnorm]
  rw [integral_const_mul, l1_exp_norm_mass ha]

/-- The exact optimal constant for the actual right exponential tail on
all complex positive-half-line L1 inputs is the reciprocal decay rate.
The converse uses a whole positive-scale exponential family. -/
theorem right_exponential_tail_l1_bound_iff {k : ℝ} (hk : 0 < k) (C : ℝ) :
    (∀ (u : ℝ → ℂ), IntegrableOn u (Ioi (0 : ℝ)) →
      (∫ t : ℝ in Ioi 0, ‖rightExponentialTail k u t‖) ≤
        C * ∫ t : ℝ in Ioi 0, ‖u t‖) ↔ k⁻¹ ≤ C := by
  constructor
  · intro h
    have hratio (a : ℝ) (ha : 0 < a) : (k + a)⁻¹ ≤ C := by
      have hb := h (l1_exp_profile a) (l1_exp_integrable ha)
      rw [l1_exp_tail_norm_mass hk ha, l1_exp_norm_mass ha] at hb
      exact (mul_le_mul_iff_of_pos_right (inv_pos.mpr ha)).mp hb
    have hC : 0 < C := lt_of_lt_of_le
      (inv_pos.mpr (add_pos hk (show (0 : ℝ) < 1 by norm_num)))
      (hratio 1 (by norm_num))
    by_contra hnot
    have hsmall : C < k⁻¹ := lt_of_not_ge hnot
    have hgap : k < C⁻¹ := (lt_inv_comm₀ hC hk).mp hsmall
    let a : ℝ := (C⁻¹ - k) / 2
    have ha : 0 < a := by dsimp [a]; linarith
    have hka : k + a < C⁻¹ := by dsimp [a]; linarith
    have hinv : C < (k + a)⁻¹ :=
      (lt_inv_comm₀ hC (add_pos hk ha)).mpr hka
    exact (not_lt_of_ge (hratio a ha)) hinv
  · intro hC u hu
    exact (l1_tail_norm_bound hk u hu).trans
      (mul_le_mul_of_nonneg_right hC
        (integral_nonneg fun t => norm_nonneg (u t)))


end D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail

