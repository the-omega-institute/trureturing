/- GID: D5/S1/Words/Patterns/Separable/OccupiedMellinKelvin
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/OccupiedMellinKelvin
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Function.JacobianOneDim]
   utility: none
   digest: Exact signed Mellin cancellation and quantitative supercritical gap. -/

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The substitution y ↦ 1/y pairs the signed occupation kernel across the
unit scale. A compact subinterval of the paired integral supplies a
quantitative gain without differentiating the singular integral in β. -/

open MeasureTheory

namespace D5.S1.Words.Patterns.Separable.OccupiedMellinKelvin

private noncomputable def paired (t β : ℝ) : ℝ :=
  t ^ (-β) - 1 + t ^ (-(1 / 2 : ℝ)) * (t ^ β - 1)

private theorem paired_factor {t β : ℝ} (ht : 0 < t) :
    paired t β = (1 - t ^ β) * (t ^ (-β) - t ^ (-(1 / 2 : ℝ))) := by
  have h : t ^ β * t ^ (-β) = 1 := by
    rw [← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero]
  unfold paired
  nlinarith only [h]

private theorem paired_critical {t : ℝ} (ht : 0 < t) : paired t (1 / 2) = 0 := by
  rw [paired_factor ht, sub_self, mul_zero]

private theorem paired_nonneg {t β : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hβ : 1 / 2 ≤ β) : 0 ≤ paired t β := by
  have hb : 0 ≤ β := by linarith
  have hlog := Real.log_nonpos ht.le ht1
  have hfirst : t ^ β ≤ 1 := by
    rw [Real.rpow_def_of_pos ht, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonpos_of_nonpos_of_nonneg hlog hb)
  have hsecond : t ^ (-(1 / 2 : ℝ)) ≤ t ^ (-β) := by
    rw [Real.rpow_def_of_pos ht, Real.rpow_def_of_pos ht]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (by linarith) hlog
  rw [paired_factor ht]
  exact mul_nonneg (sub_nonneg.mpr hfirst) (sub_nonneg.mpr hsecond)

private noncomputable def gapConstant : ℝ :=
  (1 - Real.exp (-(Real.log 2 / 2))) * Real.log 2

private theorem gapConstant_pos : 0 < gapConstant := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he : Real.exp (-(Real.log 2 / 2)) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  exact mul_pos (sub_pos.mpr he) hlog

/-- Quantitative pointwise gain after Kelvin pairing, in particular on [1 / 4,1 / 2].
The bound is linear in the distance to the critical exponent and uniform in t. -/
private theorem paired_linear_gap {t β : ℝ} (ht : 0 < t) (ht2 : t ≤ 1 / 2)
    (hβ : 1 / 2 ≤ β) : gapConstant * (β - 1 / 2) ≤ paired t β := by
  let L := -Real.log t
  have hL : Real.log 2 ≤ L := by
    have h := Real.log_le_log ht ht2
    have heq : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
    dsimp [L]
    linarith only [h, heq]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 : 0 ≤ L := hlog.le.trans hL
  have hβ0 : 0 ≤ β - 1 / 2 := sub_nonneg.mpr hβ
  have hprod : Real.log 2 / 2 ≤ L * β := by
    have h1 := mul_le_mul_of_nonneg_right hL (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    have h2 := mul_le_mul_of_nonneg_left hβ hL0
    linarith only [h1, h2]
  have hfirst : 1 - Real.exp (-(Real.log 2 / 2)) ≤ 1 - t ^ β := by
    rw [Real.rpow_def_of_pos ht]
    have he := Real.exp_le_exp.mpr (show Real.log t * β ≤ -(Real.log 2 / 2) by
      dsimp [L] at hprod
      linarith only [hprod])
    linarith only [he]
  have hfirst0 : 0 ≤ 1 - Real.exp (-(Real.log 2 / 2)) := by
    apply sub_nonneg.mpr
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith only [hlog])
  let u := L / 2
  let v := L * (β - 1 / 2)
  have hv : 0 ≤ v := mul_nonneg hL0 hβ0
  have hu : 0 ≤ u := div_nonneg hL0 (by norm_num)
  have huExp : 1 ≤ Real.exp u := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr hu
  have hdiff : Real.log 2 * (β - 1 / 2) ≤ t ^ (-β) - t ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_def_of_pos ht, Real.rpow_def_of_pos ht]
    have h1 : Real.log t * (-β) = u + v := by dsimp [u, v, L]; ring
    have h2 : Real.log t * (-(1 / 2 : ℝ)) = u := by dsimp [u, L]; ring
    rw [h1, h2, Real.exp_add]
    calc
      _ ≤ v := mul_le_mul_of_nonneg_right hL hβ0
      _ ≤ Real.exp u * v := by simpa only [one_mul] using mul_le_mul_of_nonneg_right huExp hv
      _ ≤ Real.exp u * Real.exp v - Real.exp u := by
        have he := Real.add_one_le_exp v
        have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos u).le
        linarith only [hm]
  rw [paired_factor ht]
  unfold gapConstant
  rw [mul_assoc]
  exact mul_le_mul hfirst hdiff (mul_nonneg hlog.le hβ0) (hfirst0.trans hfirst)

/-- Real signed whole-line kernel for the Mellin balance of the occupation profile. -/
noncomputable def signedKernel (β y : ℝ) : ℝ :=
  (|y| ^ (-β) - 1) * |1 - y| ^ (-(3 / 2 : ℝ))

/-- Here the factor |y|⁻² is the inversion Jacobian; no integral substitution
    or convergence claim is included in this exact identity. -/
private theorem inversion_pair_identity {y : ℝ} (hy : y ≠ 0) (β : ℝ) :
    signedKernel β y + |y| ^ (-2 : ℝ) * signedKernel β y⁻¹ =
      |1 - y| ^ (-(3 / 2 : ℝ)) * paired |y| β := by
  have hpos : 0 < |y| := abs_pos.mpr hy
  have hydiv : 1 - y⁻¹ = (y - 1) / y := by
    apply (eq_div_iff hy).mpr
    rw [sub_mul, one_mul, inv_mul_cancel₀ hy]
  have hdist : |1 - y⁻¹| = |1 - y| / |y| := by
    rw [hydiv, abs_div, abs_sub_comm y 1]
  have hInv : |y⁻¹| ^ (-β) = |y| ^ β := by
    rw [abs_inv, Real.inv_rpow hpos.le, ← Real.rpow_neg hpos.le, neg_neg]
  have hPower : |y| ^ (-2 : ℝ) * (|y| ^ (-(3 / 2 : ℝ)))⁻¹ =
      |y| ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_neg hpos.le, ← Real.rpow_add hpos]
    congr 1
    norm_num
  unfold signedKernel paired
  rw [hInv, hdist, Real.div_rpow (abs_nonneg _) hpos.le,
    div_eq_mul_inv (|1-y| ^ (-(3 / 2 : ℝ))) (|y| ^ (-(3 / 2 : ℝ)))]
  calc
    _ = (|y| ^ (-β) - 1) * |1 - y| ^ (-(3 / 2 : ℝ)) +
        (|y| ^ (-2 : ℝ) * (|y| ^ (-(3 / 2 : ℝ)))⁻¹) *
          ((|y| ^ β - 1) * |1 - y| ^ (-(3 / 2 : ℝ))) := by ring
    _ = _ := by rw [hPower]; ring

private noncomputable def pairedKernel (β y : ℝ) : ℝ :=
  |1 - y| ^ (-(3 / 2 : ℝ)) * paired |y| β

private theorem pairedKernel_continuousOn {a b β : ℝ} (ha : 0 < a) (hb : b < 1) :
    ContinuousOn (pairedKernel β) (Set.Icc a b) := by
  intro y hy
  have hypos : 0 < y := ha.trans_le hy.1
  have hylt : y < 1 := hy.2.trans_lt hb
  have hy1 : 1 - y ≠ 0 := sub_ne_zero.mpr hylt.ne.symm
  have hc0 : ContinuousAt (fun z : ℝ => |1-z|) y := by
    have hc : ContinuousAt (fun _ : ℝ => (1 : ℝ)) y := continuousAt_const
    exact (hc.sub continuousAt_id).abs
  have hc1 : ContinuousAt (fun z : ℝ => |1-z| ^ (-(3 / 2 : ℝ))) y :=
        (ContinuousAt.comp (f := fun z : ℝ => |1-z|)
      (Real.continuousAt_rpow_const |1-y| (-(3 / 2 : ℝ)) (Or.inl (abs_ne_zero.mpr hy1))) hc0)
  have hc2 (q : ℝ) : ContinuousAt (fun z : ℝ => |z| ^ q) y :=
    (Real.continuousAt_rpow_const _ _ (Or.inl (abs_ne_zero.mpr hypos.ne'))).comp
      (continuousAt_id.abs)
  exact (hc1.mul (((hc2 (-β)).sub continuousAt_const).add
    ((hc2 (-(1 / 2 : ℝ))).mul ((hc2 β).sub continuousAt_const)))).continuousWithinAt

/-- Positive compact contribution to the Kelvin-paired J integral on the
    interval [1 / 4,1 / 2]. This interval excludes both singular locations 0 and 1;
    no choice of value at those endpoints affects this theorem. -/
private theorem compact_Kelvin_integral_lower {β : ℝ} (hβ : 1 / 2 ≤ β) :
    gapConstant * (β - 1 / 2) / 4 ≤
      (∫ y in (1 / 4 : ℝ)..(1 / 2 : ℝ), pairedKernel β y) := by
  have hab : (1 / 4 : ℝ) ≤ 1 / 2 := by norm_num
  have hG := (pairedKernel_continuousOn (β := β) (by norm_num : (0 : ℝ) < 1 / 4)
    (by norm_num : (1 / 2 : ℝ) < 1)).intervalIntegrable_of_Icc (μ := volume) hab
  have hm := intervalIntegral.integral_mono_on (μ := volume) (f := fun _ => gapConstant * (β-1 / 2))
    (g := pairedKernel β) hab (intervalIntegrable_const) hG (fun y hy => by
      have hypos : 0 < y := lt_of_lt_of_le (by norm_num) hy.1
      have hy2 : y ≤ 1 / 2 := hy.2
      have hylt : y < 1 := hy2.trans_lt (by norm_num)
      have hpow : 1 ≤ (1-y) ^ (-(3 / 2 : ℝ)) := by
        rw [Real.rpow_def_of_pos (sub_pos.mpr hylt)]
        calc
          1 = Real.exp 0 := Real.exp_zero.symm
          _ ≤ _ := Real.exp_le_exp.mpr (mul_nonneg_of_nonpos_of_nonpos
            (Real.log_nonpos (by linarith) (by linarith)) (by norm_num))
      have hpair : 0 ≤ paired y β := paired_nonneg hypos hylt.le hβ
      have hgap := paired_linear_gap hypos hy2 hβ
      unfold pairedKernel
      rw [abs_of_pos hypos, abs_of_pos (sub_pos.mpr hylt)]
      exact hgap.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow hpair))
  rw [intervalIntegral.integral_const, smul_eq_mul] at hm
  convert hm using 1
  ring

private def inner : Set ℝ := {y | 0 < |y| ∧ |y| < 1}
private def outer : Set ℝ := {y | 1 < |y|}

private theorem inner_measurable : MeasurableSet inner :=
  (measurableSet_lt measurable_const continuous_abs.measurable).inter
    (measurableSet_lt continuous_abs.measurable measurable_const)

private theorem outer_measurable : MeasurableSet outer :=
  measurableSet_lt measurable_const continuous_abs.measurable

private theorem inv_image_inner : (fun y : ℝ => y⁻¹) '' inner = outer := by
  ext x
  change (∃ y ∈ inner, y⁻¹ = x) ↔ 1 < |x|
  constructor
  · rintro ⟨y, hy, rfl⟩
    change 0 < |y| ∧ |y| < 1 at hy
    rw [abs_inv, one_lt_inv_iff₀]
    exact hy
  · intro hx
    have hx0 : 0 < |x| := by linarith
    refine ⟨x⁻¹, ?_, inv_inv _⟩
    change 0 < |x⁻¹| ∧ |x⁻¹| < 1
    rw [abs_inv, inv_lt_one_iff₀]
    exact ⟨inv_pos.mpr hx0, Or.inr hx⟩

private theorem jacobian_eq (x : ℝ) : |-(x^2)⁻¹| = |x| ^ (-2 : ℝ) := by
  rw [abs_neg, abs_inv, abs_of_nonneg (sq_nonneg x)]
  rw [show (-2 : ℝ) = -(2 : ℝ) by rfl, Real.rpow_neg (abs_nonneg x)]
  rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast, sq_abs]

/-- Exact outside-to-inside inversion on both half lines. The set excludes
    the pole at zero, and the derivative Jacobian is proved, not assumed. -/
private theorem outside_integral_eq_inverse_inside (g : ℝ → ℝ) :
    (∫ x in outer, g x) = ∫ y in inner, |y| ^ (-2 : ℝ) * g y⁻¹ := by
  have h := integral_image_eq_integral_abs_deriv_smul
    (f := fun x : ℝ => x⁻¹) (f' := fun x : ℝ => -(x ^ 2)⁻¹)
    inner_measurable (fun x hx => (hasDerivAt_inv (abs_pos.mp hx.1)).hasDerivWithinAt)
    inv_injective.injOn g
  rw [inv_image_inner] at h
  simpa only [smul_eq_mul, jacobian_eq] using h

private theorem integral_inside_outside (g : ℝ → ℝ) (hg : Integrable g) :
    (∫ x, g x) = (∫ x in inner, g x) + ∫ x in outer, g x := by
  have hdisj : Disjoint inner outer := by
    refine Set.disjoint_left.mpr fun x hx hx' => ?_
    exact (not_lt_of_ge (hx.2.le)) hx'
  have hae : (Set.univ : Set ℝ) =ᵐ[volume] inner ∪ outer := by
    filter_upwards [volume.ae_ne (0 : ℝ), volume.ae_ne (1 : ℝ), volume.ae_ne (-1 : ℝ)]
      with x h0 h1 hn1
    have hp : 0 < |x| := abs_pos.mpr h0
    have hne : |x| ≠ 1 := by
      by_cases hx : 0 ≤ x
      · simpa only [abs_of_nonneg hx] using h1
      · rw [abs_of_neg (lt_of_not_ge hx)]
        intro h
        apply hn1
        linarith
    refine propext (iff_of_true trivial ?_)
    exact (lt_or_gt_of_ne hne).elim (fun h => Or.inl ⟨hp, h⟩) Or.inr
  rw [← setIntegral_univ, setIntegral_congr_set hae,
    setIntegral_union hdisj outer_measurable hg.integrableOn hg.integrableOn]

private theorem integrable_inverse_inner (β : ℝ) (hβ : Integrable (signedKernel β)) :
    IntegrableOn (fun y : ℝ => |y| ^ (-2 : ℝ) * signedKernel β y⁻¹) inner := by
  have hh := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (f := fun x : ℝ => x⁻¹) (f' := fun x : ℝ => -(x ^ 2)⁻¹)
    inner_measurable (fun x hx => (hasDerivAt_inv (abs_pos.mp hx.1)).hasDerivWithinAt)
    inv_injective.injOn (signedKernel β)
  simpa only [smul_eq_mul, jacobian_eq] using hh.mp hβ.integrableOn
/-- Whole signed Mellin integral, paired by exact inversion. The sole analytic
    premise is integrability of the signed kernel. The three omitted points
    0, 1, -1 are volume-null and their assigned values play no role. -/
private theorem whole_J_eq_paired (β : ℝ) (hβ : Integrable (signedKernel β)) :
    (∫ y, signedKernel β y) = ∫ y in inner, pairedKernel β y := by
  rw [integral_inside_outside (signedKernel β) hβ, outside_integral_eq_inverse_inside]
  have hd := integrable_inverse_inner β hβ
  rw [← integral_add hβ.integrableOn hd]
  exact setIntegral_congr_fun inner_measurable fun y hy =>
    inversion_pair_identity (abs_pos.mp hy.1) β

private theorem whole_J_critical (h : Integrable (signedKernel (1 / 2))) :
    (∫ y, signedKernel (1 / 2) y) = 0 := by
  rw [whole_J_eq_paired _ h]
  have hz : Set.EqOn (pairedKernel (1 / 2)) (fun _ => 0) inner := by
    intro y hy
    unfold pairedKernel
    rw [paired_critical hy.1, mul_zero]
  rw [setIntegral_congr_fun inner_measurable hz]
  exact integral_zero _ _

private theorem whole_J_linear_gap {β : ℝ} (hβ : 1 / 2 ≤ β) (h : Integrable (signedKernel β)) :
    gapConstant * (β - 1 / 2) / 4 ≤ ∫ y, signedKernel β y := by
  have hi : IntegrableOn (pairedKernel β) inner := by
    apply (integrableOn_congr_fun (fun y hy => inversion_pair_identity (abs_pos.mp hy.1) β)
      inner_measurable).mp
    exact h.integrableOn.add (integrable_inverse_inner β h)
  have hn : ∀ᵐ y ∂volume.restrict inner, 0 ≤ pairedKernel β y := by
    apply (ae_restrict_iff' inner_measurable).2
    exact Filter.Eventually.of_forall fun y hy =>
      mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (paired_nonneg hy.1 hy.2.le hβ)
  have hsub : Set.Ioc (1 / 4 : ℝ) (1 / 2 : ℝ) ⊆ inner := by
    intro y hy
    have hp : 0 < y := lt_trans (by norm_num) hy.1
    change 0 < |y| ∧ |y| < 1
    rw [abs_of_pos hp]
    exact ⟨hp, hy.2.trans_lt (by norm_num)⟩
  rw [whole_J_eq_paired _ h]
  have hc := compact_Kelvin_integral_lower hβ
  rw [intervalIntegral.integral_of_le (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)] at hc
  exact hc.trans (setIntegral_mono_set hi hn hsub.eventuallySubset)

private theorem numerator_lipschitz_near_one (β : ℝ) (hβ : 0 ≤ β) :
    ∀ y ∈ Set.Icc (1 / 2 : ℝ) (3 / 2 : ℝ),
      |y ^ (-β) - 1| ≤ (β * (1 / 2 : ℝ)^(-β-1)) * |1-y| := by
  let S := Set.Icc (1 / 2 : ℝ) (3 / 2 : ℝ)
  have hD (t : ℝ) (ht : t ∈ S) :
      HasDerivWithinAt (fun x : ℝ => x ^ (-β)) ((-β) * t ^ (-β-1)) S t := by
    have hpos : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
    exact (Real.hasDerivAt_rpow_const (Or.inl hpos.ne')).hasDerivWithinAt
  have hbound (t : ℝ) (ht : t ∈ S) :
      ‖(-β) * t ^ (-β-1)‖ ≤ β * (1 / 2 : ℝ)^(-β-1) := by
    have hpos : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hβ,
      abs_of_nonneg (Real.rpow_nonneg hpos.le _)]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by norm_num) ht.1 (by linarith)) hβ
  intro y hy
  have h := (convex_Icc (1 / 2 : ℝ) (3 / 2 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hD hbound (show (1 : ℝ) ∈ S from ⟨by norm_num, by norm_num⟩) hy
  simpa only [Real.norm_eq_abs, Real.one_rpow, abs_sub_comm y 1] using h

private theorem abs_rpow_intervalIntegrable {r T : ℝ} (hr : -1 < r) (hT : 0 ≤ T) :
    IntervalIntegrable (fun x : ℝ => |x| ^ r) volume (-T) T := by
  have hp : IntervalIntegrable (fun x : ℝ => |x| ^ r) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
    have h := (intervalIntegrable_iff_integrableOn_Icc_of_le
      (μ := volume) (f := fun x : ℝ => x ^ r) hT).mp
      (intervalIntegral.intervalIntegrable_rpow' hr)
    exact h.congr_fun (fun x hx => by rw [abs_of_nonneg hx.1]) measurableSet_Icc
  have hm : IntervalIntegrable (fun x : ℝ => |x| ^ r) volume (-T) 0 := by
    rw [IntervalIntegrable.iff_comp_neg]
    simpa only [abs_neg, neg_neg, neg_zero] using hp.symm
  exact hm.trans hp

private theorem signedKernel_integrable_near_one {β : ℝ} (hβ : 0 ≤ β) :
    IntegrableOn (signedKernel β) (Set.Icc (1 / 2 : ℝ) (3 / 2 : ℝ)) := by
  let C := β * (1 / 2 : ℝ)^(-β-1)
  have hbase :
      IntervalIntegrable (fun x : ℝ => C * |x - 1| ^ (-(1 / 2 : ℝ))) volume (1 / 2) (3 / 2) := by
    have h := abs_rpow_intervalIntegrable (r := -(1 / 2 : ℝ)) (T := 1 / 2)
      (by norm_num) (by norm_num)
    have h := (h.comp_sub_right 1).const_mul C
    convert h using 1 <;> norm_num
  have hMajor := (intervalIntegrable_iff_integrableOn_Icc_of_le
    (show (1 / 2 : ℝ) ≤ 3 / 2 by norm_num)).mp hbase
  have hf : Measurable (signedKernel β) := by unfold signedKernel; fun_prop
  apply hMajor.mono' hf.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae (volume.ae_ne (1 : ℝ))]
    with y hy hn
  have hp : 0 < y := lt_of_lt_of_le (by norm_num) hy.1
  have hdist : 0 < |1-y| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hn))
  unfold signedKernel
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hdist.le _), abs_of_pos hp]
  have h := mul_le_mul_of_nonneg_right (numerator_lipschitz_near_one β hβ y hy)
    (Real.rpow_nonneg hdist.le (-(3 / 2 : ℝ)))
  apply h.trans_eq
  change (C * |1-y|) * |1-y| ^ (-(3 / 2 : ℝ)) = C * |y-1| ^ (-(1 / 2 : ℝ))
  rw [mul_assoc]
  have heq : |1-y| * |1-y| ^ (-(3 / 2 : ℝ)) = |1-y| ^ (-(1 / 2 : ℝ)) := by
    rw [← show (1 + -(3 / 2 : ℝ)) = -(1 / 2 : ℝ) by norm_num,
      Real.rpow_add hdist, Real.rpow_one]
  rw [heq, abs_sub_comm 1 y]

private theorem signedKernel_integrable_near_zero {β : ℝ} (h₀ : 0 ≤ β) (h₁ : β < 1) :
    IntegrableOn (signedKernel β) (Set.Icc (-1 / 2 : ℝ) (1 / 2 : ℝ)) := by
  let C := (1 / 2 : ℝ) ^ (-(3 / 2 : ℝ))
  have hbase := (abs_rpow_intervalIntegrable (r := -β) (T := 1 / 2)
    (by linarith) (by norm_num)).const_mul C
  have hMajor := (intervalIntegrable_iff_integrableOn_Icc_of_le
    (f := fun x : ℝ => C * |x| ^ (-β))
    (show (-1 / 2 : ℝ) ≤ 1 / 2 by norm_num)).mp (by simpa only [neg_div] using hbase)
  have hf : Measurable (signedKernel β) := by unfold signedKernel; fun_prop
  apply hMajor.mono' hf.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae (volume.ae_ne (0 : ℝ))]
    with y hy hn
  have hdist : (1 / 2 : ℝ) ≤ |1-y| := by
    rw [abs_of_pos (by linarith [hy.2] : 0 < 1-y)]
    linarith [hy.2]
  have hyle : |y| ≤ 1 := (abs_le.mpr ⟨by linarith [hy.1], hy.2⟩).trans (by norm_num)
  have hnum := Real.one_le_rpow_of_pos_of_le_one_of_nonpos (abs_pos.mpr hn) hyle (neg_nonpos.mpr h₀)
  unfold signedKernel
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
    abs_of_nonneg (sub_nonneg.mpr hnum)]
  calc
    _ ≤ |y| ^ (-β) * |1-y| ^ (-(3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right (sub_le_self _ zero_le_one) (Real.rpow_nonneg (abs_nonneg _) _)
    _ ≤ _ := by
      rw [mul_comm C]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by norm_num) hdist (by norm_num))
        (Real.rpow_nonneg (abs_nonneg _) _)

private theorem tail_pointwise {β y : ℝ} (hβ : 0 ≤ β) (hy : 2 < |y|) :
    ‖signedKernel β y‖ ≤ (1 / 2 : ℝ) ^ (-(3 / 2 : ℝ)) * |y| ^ (-(3 / 2 : ℝ)) := by
  have htriangle : |y| ≤ |1-y| + 1 := by
    have h := abs_add_le (y-1) (1 : ℝ)
    rw [sub_add_cancel, abs_one, abs_sub_comm y 1] at h
    exact h
  have hdist : (1 / 2 : ℝ) * |y| ≤ |1-y| := by linarith
  have hpos : 0 < (1 / 2 : ℝ) * |y| := by linarith
  have hnum := Real.rpow_le_one_of_one_le_of_nonpos (show 1 ≤ |y| by linarith) (neg_nonpos.mpr hβ)
  unfold signedKernel
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (1-y)) _),
    abs_of_nonpos (sub_nonpos.mpr hnum)]
  have hp := Real.rpow_nonneg (abs_nonneg y) (-β)
  calc
    _ ≤ 1 * |1-y| ^ (-(3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (abs_nonneg _) _)
    _ ≤ _ := by
      rw [one_mul, ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) (abs_nonneg y)]
      exact Real.rpow_le_rpow_of_nonpos hpos hdist (by norm_num)

private theorem signedKernel_integrable_right_tail {β : ℝ} (hβ : 0 ≤ β) :
    IntegrableOn (signedKernel β) (Set.Ioi (2 : ℝ)) := by
  have h := (integrableOn_Ioi_rpow_of_lt (show (-(3 / 2 : ℝ)) < -1 by norm_num)
    (show (0 : ℝ) < 2 by norm_num)).const_mul ((1 / 2 : ℝ) ^ (-(3 / 2 : ℝ)))
  have hf : Measurable (signedKernel β) := by unfold signedKernel; fun_prop
  refine h.mono' hf.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hp : 0 < y := lt_trans (by norm_num) hy
  simpa only [abs_of_pos hp] using tail_pointwise hβ (show 2 < |y| by rwa [abs_of_pos hp])

private theorem signedKernel_integrable_left_tail {β : ℝ} (hβ : 0 ≤ β) :
    IntegrableOn (signedKernel β) (Set.Iio (-2 : ℝ)) := by
  have hp := (integrableOn_Ioi_rpow_of_lt (show (-(3 / 2 : ℝ)) < -1 by norm_num)
    (show (0 : ℝ) < 2 by norm_num)).const_mul ((1 / 2 : ℝ) ^ (-(3 / 2 : ℝ)))
  have hneg : (fun y : ℝ => -y) ⁻¹' Set.Ioi (2 : ℝ) = Set.Iio (-2 : ℝ) := by
    ext y
    change 2 < -y ↔ y < -2
    constructor <;> intro h <;> linarith
  have hn : IntegrableOn (fun y : ℝ => (1 / 2 : ℝ)^(-(3 / 2 : ℝ)) * (-y)^(-(3 / 2 : ℝ)))
      (Set.Iio (-2 : ℝ)) := by
    rw [← hneg]
    exact ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding).mpr hp
  have hf : Measurable (signedKernel β) := by unfold signedKernel; fun_prop
  refine hn.mono' hf.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
  have hp' : y < 0 := lt_trans hy (by norm_num)
  have hy' : 2 < |y| := by rw [abs_of_neg hp']; linarith [Set.mem_Iio.mp hy]
  simpa only [abs_of_neg hp'] using tail_pointwise hβ hy'

private theorem kernel_continuous_away_on (β : ℝ) (s : Set ℝ)
    (hs : ∀ y ∈ s, y ≠ 0 ∧ y ≠ 1) : ContinuousOn (signedKernel β) s := by
  intro y hy
  have h := hs y hy
  have hc0 : ContinuousAt (fun z : ℝ => |1-z|) y := by
    have hc : ContinuousAt (fun _ : ℝ => (1 : ℝ)) y := continuousAt_const
    exact (hc.sub continuousAt_id).abs
  have ha := ContinuousAt.comp (f := fun z : ℝ => |1-z|)
    (Real.continuousAt_rpow_const |1-y| (-(3 / 2 : ℝ))
      (Or.inl (abs_ne_zero.mpr (sub_ne_zero.mpr h.2.symm)))) hc0
  have hb := ContinuousAt.comp (f := fun z : ℝ => |z|)
    (Real.continuousAt_rpow_const |y| (-β) (Or.inl (abs_ne_zero.mpr h.1))) continuousAt_id.abs
  exact ((hb.sub continuousAt_const).mul ha).continuousWithinAt

private theorem signedKernel_integrable {β : ℝ} (h₀ : 0 ≤ β) (h₁ : β < 1) :
    Integrable (signedKernel β) := by
  have hcc {a b : ℝ} (hab : a ≤ b) (hs : ∀ y ∈ Set.Icc a b, y ≠ 0 ∧ y ≠ 1) :
      IntegrableOn (signedKernel β) (Set.Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp
      ((kernel_continuous_away_on β _ hs).intervalIntegrable_of_Icc hab)
  have hleft : IntegrableOn (signedKernel β) (Set.Icc (-2 : ℝ) (-1 / 2 : ℝ)) :=
    hcc (by norm_num) (fun y hy => ⟨by linarith [hy.2], by linarith [hy.2]⟩)
  have hright : IntegrableOn (signedKernel β) (Set.Icc (3 / 2 : ℝ) 2) :=
    hcc (by norm_num) (fun y hy => ⟨by linarith [hy.1], by linarith [hy.1]⟩)
  have hcover : (Set.univ : Set ℝ) = Set.Iio (-2 : ℝ) ∪
      (Set.Icc (-2 : ℝ) (-1 / 2 : ℝ) ∪ (Set.Icc (-1 / 2 : ℝ) (1 / 2 : ℝ) ∪
        (Set.Icc (1 / 2 : ℝ) (3 / 2 : ℝ) ∪ (Set.Icc (3 / 2 : ℝ) 2 ∪ Set.Ioi (2 : ℝ))))) := by
    ext y
    simp only [Set.mem_univ, Set.mem_union, Set.mem_Iio, Set.mem_Ioi, Set.mem_Icc, true_iff]
    rcases lt_or_ge y (-2) with h | h
    · exact Or.inl h
    right
    rcases le_or_gt y (-1 / 2) with h' | h'
    · exact Or.inl ⟨h, h'⟩
    right
    rcases le_or_gt y (1 / 2) with h'' | h''
    · exact Or.inl ⟨h'.le, h''⟩
    right
    rcases le_or_gt y (3 / 2) with h''' | h'''
    · exact Or.inl ⟨h''.le, h'''⟩
    right
    rcases le_or_gt y 2 with ht | ht
    · exact Or.inl ⟨h'''.le, ht⟩
    · exact Or.inr ht
  rw [← integrableOn_univ, hcover]
  simp only [integrableOn_union]
  exact ⟨signedKernel_integrable_left_tail h₀, hleft, signedKernel_integrable_near_zero h₀ h₁,
    signedKernel_integrable_near_one h₀, hright, signedKernel_integrable_right_tail h₀⟩

/-- The signed Mellin integral over the whole real line. -/
noncomputable def J (β : ℝ) : ℝ := ∫ y, signedKernel β y

/-- Fixed positive coefficient of the linear supercritical lower bound. -/
noncomputable def gapCoefficient : ℝ :=
  (1 - Real.exp (-(Real.log 2 / 2))) * Real.log 2 / 4

/-- The signed kernel is integrable throughout the exponent range 0 ≤ β < 1.
At β = 1 / 2 the Kelvin pairs cancel exactly; above it the same pairs give a
fixed positive linear lower bound. -/
theorem signed_mellin_cancellation_and_gap :
    (∀ β : ℝ, 0 ≤ β → β < 1 → Integrable (signedKernel β)) ∧
    J (1 / 2) = 0 ∧ 0 < gapCoefficient ∧
    (∀ β : ℝ, 1 / 2 ≤ β → β < 1 → gapCoefficient * (β - 1 / 2) ≤ J β) := by
  refine ⟨fun _ h₀ h₁ => signedKernel_integrable h₀ h₁, ?_,
    div_pos gapConstant_pos (by norm_num), ?_⟩
  · exact whole_J_critical (signedKernel_integrable (by norm_num) (by norm_num))
  · intro β h₀ h₁
    change gapConstant / 4 * (β - 1 / 2) ≤ ∫ y, signedKernel β y
    rw [div_mul_eq_mul_div]
    exact whole_J_linear_gap h₀ (signedKernel_integrable (by linarith) h₁)

end D5.S1.Words.Patterns.Separable.OccupiedMellinKelvin
