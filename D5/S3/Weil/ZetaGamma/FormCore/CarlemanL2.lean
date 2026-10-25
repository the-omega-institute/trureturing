/- GID: D5/S3/Weil/ZetaGamma/FormCore/CarlemanL2
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:actual-Carleman-halfline-L2-domain)
   anchors: []
   utility: none
   digest: Actual absolute Carleman double-integral domain and pi bound on arbitrary complex half-line L2 sources. -/

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Actual Carleman double integral on half-line L2

The true Schur row and its product-measure majorant pay the actual
absolute double-integral domain and pi bound. The positive Hankel
half-rate domain consumes this independent Carleman estimate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Weil.ZetaGamma.FormCore.CarlemanL2
open MeasureTheory Set Filter
open scoped ENNReal Topology

abbrev halfline : Measure ℝ := volume.restrict (Ioi (0 : ℝ))

def schurRow (s t : ℝ) : ℝ :=
  Real.sqrt s / (Real.sqrt t * (s + t))

private def normalizedRow (y : ℝ) : ℝ :=
  1 / (Real.sqrt y * (1 + y))

private theorem normalized_row_substitution (x : ℝ) (hx : 0 < x) :
    (|(2 : ℝ)| * x ^ ((2 : ℝ) - 1)) • normalizedRow (x ^ (2 : ℝ)) =
      2 * (1 + x ^ 2)⁻¹ := by
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2),
    show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two,
    smul_eq_mul]
  rw [normalizedRow, Real.sqrt_sq_eq_abs, abs_of_pos hx]
  field_simp [hx.ne', show 1 + x ^ 2 ≠ 0 by positivity]
  <;> ring

private theorem normalized_row_integrable : Integrable normalizedRow halfline := by
  have hb : Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹) halfline :=
    (show IntegrableOn (fun x : ℝ => (1 + x ^ 2)⁻¹) (Ioi 0) from
      integrable_inv_one_add_sq.integrableOn).integrable
  have ht : IntegrableOn
      (fun x : ℝ => (|(2 : ℝ)| * x ^ ((2 : ℝ) - 1)) • normalizedRow (x ^ (2 : ℝ)))
      (Ioi 0) := by
    change Integrable _ halfline
    apply (hb.const_mul (2 : ℝ)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (normalized_row_substitution x hx).symm
  exact ((integrableOn_Ioi_comp_rpow_iff normalizedRow
    (by norm_num : (2 : ℝ) ≠ 0)).1 ht).integrable

private theorem normalized_row_integral :
    (∫ y : ℝ in Ioi 0, normalizedRow y) = Real.pi := by
  calc
    _ = ∫ x : ℝ in Ioi 0,
        (|(2 : ℝ)| * x ^ ((2 : ℝ) - 1)) • normalizedRow (x ^ (2 : ℝ)) :=
      (integral_comp_rpow_Ioi normalizedRow (by norm_num : (2 : ℝ) ≠ 0)).symm
    _ = ∫ x : ℝ in Ioi 0, 2 * (1 + x ^ 2)⁻¹ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact normalized_row_substitution x hx
    _ = Real.pi := by
      rw [integral_const_mul, integral_Ioi_inv_one_add_sq, Real.arctan_zero]
      ring

private theorem schur_row_scaled (s y : ℝ) (hs : 0 < s) (hy : 0 < y) :
    schurRow s (s * y) = s⁻¹ * normalizedRow y := by
  unfold schurRow normalizedRow
  rw [Real.sqrt_mul hs.le]
  have hss : Real.sqrt s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  have hsy : Real.sqrt y ≠ 0 := (Real.sqrt_pos.2 hy).ne'
  field_simp [hss, hsy, hs.ne', show s + s * y ≠ 0 by positivity,
    show 1 + y ≠ 0 by positivity]
  <;> ring

private theorem schur_row_nonneg {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    0 ≤ schurRow s t := by unfold schurRow; positivity

private theorem schur_row_integrable {s : ℝ} (hs : 0 < s) :
    Integrable (schurRow s) halfline := by
  have hi : IntegrableOn (fun y => schurRow s (s * y)) (Ioi 0) := by
    change Integrable _ halfline
    apply (normalized_row_integrable.const_mul s⁻¹).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact (schur_row_scaled s y hs hy).symm
  have hj : IntegrableOn (schurRow s) (Ioi 0) := by
    simpa only [mul_zero] using
      (integrableOn_Ioi_comp_mul_left_iff (schurRow s) 0 hs).1 hi
  exact hj.integrable

private theorem schur_row_integral {s : ℝ} (hs : 0 < s) :
    (∫ t : ℝ, schurRow s t ∂halfline) = Real.pi := by
  have hc : (∫ y : ℝ in Ioi 0, schurRow s (s * y)) = s⁻¹ * Real.pi := by
    calc
      _ = ∫ y : ℝ in Ioi 0, s⁻¹ * normalizedRow y := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
        exact schur_row_scaled s y hs hy
      _ = _ := by rw [integral_const_mul, normalized_row_integral]
  calc
    _ = s * ∫ y : ℝ in Ioi 0, schurRow s (s * y) := by
      simpa only [mul_zero, smul_eq_mul] using
        (integral_comp_mul_left_Ioi' (schurRow s) 0 hs).symm
    _ = Real.pi := by rw [hc]; field_simp [hs.ne']

private theorem positive_pair_ae :
    ∀ᵐ z : ℝ × ℝ ∂halfline.prod halfline, 0 < z.1 ∧ 0 < z.2 := by
  rw [halfline, Measure.prod_restrict]
  exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)

private theorem schur_amgm (s t a b : ℝ) (hs : 0 < s) (ht : 0 < t) :
    a * b / (s + t) ≤
      (a ^ 2 * schurRow s t + b ^ 2 * schurRow t s) / 2 := by
  let D := Real.sqrt s * Real.sqrt t * (s + t)
  have hD : 0 < D := by dsimp [D]; positivity
  have h1 : schurRow s t * D = s := by
    unfold schurRow D
    calc
      _ = Real.sqrt s ^ 2 := by
        field_simp [(Real.sqrt_pos.2 ht).ne', show s + t ≠ 0 by positivity]
        <;> ring
      _ = s := Real.sq_sqrt hs.le
  have h2 : schurRow t s * D = t := by
    unfold schurRow D
    rw [show t + s = s + t by ring]
    calc
      _ = Real.sqrt t ^ 2 := by
        field_simp [(Real.sqrt_pos.2 hs).ne', show s + t ≠ 0 by positivity]
        <;> ring
      _ = t := Real.sq_sqrt ht.le
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  apply (mul_le_mul_iff_left₀ hD).1
  calc
    (a * b / (s + t) * 2) * D =
        2 * a * b * Real.sqrt s * Real.sqrt t := by
      dsimp [D]
      field_simp [show s + t ≠ 0 by positivity]
      <;> ring
    _ ≤ a ^ 2 * s + b ^ 2 * t := by
      have hsq := sq_nonneg (a * Real.sqrt s - b * Real.sqrt t)
      simp only [sub_sq, mul_pow, Real.sq_sqrt hs.le, Real.sq_sqrt ht.le] at hsq
      nlinarith only [hsq]
    _ = (a ^ 2 * schurRow s t + b ^ 2 * schurRow t s) * D := by
      rw [add_mul, mul_assoc, h1, mul_assoc, h2]

private def schurMajorant (u : ℝ → ℂ) (z : ℝ × ℝ) : ℝ :=
  ‖u z.1‖ ^ 2 * schurRow z.1 z.2

private theorem schur_majorant_domain (u : ℝ → ℂ) (hu : MemLp u 2 halfline) :
    Integrable (schurMajorant u) (halfline.prod halfline) ∧
      (∫ z : ℝ × ℝ, schurMajorant u z ∂halfline.prod halfline) =
        Real.pi * ∫ s : ℝ, ‖u s‖ ^ 2 ∂halfline := by
  have hsq : Integrable (fun s : ℝ => ‖u s‖ ^ 2) halfline :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu
  have hmrow : Measurable (fun z : ℝ × ℝ => schurRow z.1 z.2) := by
    unfold schurRow
    fun_prop
  have hm : AEStronglyMeasurable (schurMajorant u) (halfline.prod halfline) :=
    (hu.aestronglyMeasurable.comp_fst.norm.pow 2).mul hmrow.aestronglyMeasurable
  have hnorm (s : ℝ) (hs : 0 < s) :
      (∫ t : ℝ, ‖schurMajorant u (s, t)‖ ∂halfline) = ‖u s‖ ^ 2 * Real.pi := by
    calc
      _ = ∫ t : ℝ, ‖u s‖ ^ 2 * schurRow s t ∂halfline := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact Real.norm_of_nonneg
          (mul_nonneg (sq_nonneg _) (schur_row_nonneg hs ht))
      _ = _ := by rw [integral_const_mul, schur_row_integral hs]
  have hi : Integrable (schurMajorant u) (halfline.prod halfline) := by
    apply (integrable_prod_iff hm).2
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      change Integrable (fun t : ℝ => ‖u s‖ ^ 2 * schurRow s t) halfline
      exact (schur_row_integrable hs).const_mul _
    · apply (hsq.mul_const Real.pi).congr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact (hnorm s hs).symm
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hi]
  calc
    _ = ∫ s : ℝ, ‖u s‖ ^ 2 * Real.pi ∂halfline := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      change (∫ t : ℝ, ‖u s‖ ^ 2 * schurRow s t ∂halfline) = _
      rw [integral_const_mul, schur_row_integral hs]
    _ = _ := by rw [integral_mul_const]; ring

def carlemanAbsolute (u : ℝ → ℂ) (z : ℝ × ℝ) : ℝ :=
  ‖u z.1‖ * ‖u z.2‖ / (z.1 + z.2)

/-- The literal L2 premise pays the actual absolute Carleman double integral. -/
theorem carleman_actual_l2_domain (u : ℝ → ℂ) (hu : MemLp u 2 halfline) :
    Integrable (carlemanAbsolute u) (halfline.prod halfline) ∧
      (∫ z : ℝ × ℝ, carlemanAbsolute u z ∂halfline.prod halfline) ≤
        Real.pi * ∫ s : ℝ, ‖u s‖ ^ 2 ∂halfline := by
  obtain ⟨hF, hmass⟩ := schur_majorant_domain u hu
  let M : ℝ × ℝ → ℝ := fun z =>
    (schurMajorant u z + schurMajorant u z.swap) / 2
  have hFswap : Integrable (fun z : ℝ × ℝ => schurMajorant u z.swap)
      (halfline.prod halfline) := by
    simpa only [Function.comp_def] using hF.swap
  have hM : Integrable M (halfline.prod halfline) := (hF.add hFswap).div_const 2
  have hm : AEStronglyMeasurable (carlemanAbsolute u) (halfline.prod halfline) := by
    have hd : Measurable (fun z : ℝ × ℝ => z.1 + z.2) := by fun_prop
    change AEStronglyMeasurable
      ((fun z : ℝ × ℝ => ‖u z.1‖ * ‖u z.2‖) / (fun z => z.1 + z.2))
      (halfline.prod halfline)
    exact (hu.aestronglyMeasurable.comp_fst.norm.mul
      hu.aestronglyMeasurable.comp_snd.norm).div₀ hd.aestronglyMeasurable
  have hbound : ∀ᵐ z : ℝ × ℝ ∂halfline.prod halfline,
      ‖carlemanAbsolute u z‖ ≤ M z := by
    filter_upwards [positive_pair_ae] with z hz
    have hnonneg : 0 ≤ carlemanAbsolute u z := by
      unfold carlemanAbsolute
      exact div_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (add_pos hz.1 hz.2).le
    rw [Real.norm_of_nonneg hnonneg]
    exact schur_amgm z.1 z.2 ‖u z.1‖ ‖u z.2‖ hz.1 hz.2
  have hi := hM.mono' hm hbound
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ z : ℝ × ℝ, M z ∂halfline.prod halfline :=
      integral_mono_ae hi hM (hbound.mono fun z hz => (le_abs_self _).trans hz)
    _ = Real.pi * ∫ s : ℝ, ‖u s‖ ^ 2 ∂halfline := by
      dsimp only [M]
      rw [integral_div, integral_add hF hFswap,
        integral_prod_swap (schurMajorant u), hmass]
      ring

#print axioms carleman_actual_l2_domain
end D5.S3.Weil.ZetaGamma.FormCore.CarlemanL2
