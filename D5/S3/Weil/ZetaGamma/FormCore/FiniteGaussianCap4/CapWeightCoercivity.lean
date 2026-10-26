/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/CapWeightCoercivity
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Positive cap coercivity forces tail mass and a strict scaled quotient for arbitrary real functions. -/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.Cap4CompactMultiplier
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! General integral comparison; no Gaussian, parity, or analytic premise.
The two density identities are relocated unchanged from the fixed
CompactMatrixActualRatio supplier b8f1b1a750fe3c7c26c752f1527b5891d5b513d3,
with only private visibility removed so both actual consumers reuse them. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter

namespace FiniteGaussianCap475
open FiniteGaussianCap4

theorem capWeight_density_above_pi (x : ℝ) (hx : Real.pi < x) :
    x ^ (7 / 2 : ℝ) * capWeight x =
      Real.pi ^ (-5 / 2 : ℝ) * x ^ 6 - 4 * Real.pi ^ (7 / 2 : ℝ) := by
  have hx0 : 0 < x := lt_trans Real.pi_pos hx
  have hprod : x ^ (7 / 2 : ℝ) * x ^ (5 / 2 : ℝ) = x ^ 6 := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hcancel : x ^ (7 / 2 : ℝ) * x ^ (-7 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hp5 : Real.pi ^ (-5 / 2 : ℝ) = (Real.pi ^ (5 / 2 : ℝ))⁻¹ := by
    rw [show (-5 / 2 : ℝ) = -(5 / 2 : ℝ) by ring, Real.rpow_neg Real.pi_pos.le]
  have hp7 : Real.pi ^ (-7 / 2 : ℝ) = (Real.pi ^ (7 / 2 : ℝ))⁻¹ := by
    rw [show (-7 / 2 : ℝ) = -(7 / 2 : ℝ) by ring, Real.rpow_neg Real.pi_pos.le]
  calc
    x ^ (7 / 2 : ℝ) * capWeight x =
        (x ^ (7 / 2 : ℝ) * x ^ (5 / 2 : ℝ)) / Real.pi ^ (5 / 2 : ℝ) -
          4 * (x ^ (7 / 2 : ℝ) * x ^ (-7 / 2 : ℝ)) / Real.pi ^ (-7 / 2 : ℝ) := by
      rw [capWeight, if_pos hx, Real.div_rpow hx0.le Real.pi_pos.le,
        Real.div_rpow hx0.le Real.pi_pos.le]
      ring
    _ = x ^ 6 / Real.pi ^ (5 / 2 : ℝ) - 4 / Real.pi ^ (-7 / 2 : ℝ) := by
      rw [hprod, hcancel]
      ring
    _ = Real.pi ^ (-5 / 2 : ℝ) * x ^ 6 - 4 * Real.pi ^ (7 / 2 : ℝ) := by
      rw [hp5, hp7]
      simp only [div_inv_eq_mul]
      ring

theorem capWeight_density_indicator (F : ℝ → ℝ) :
    (fun x : ℝ => x ^ (7 / 2 : ℝ) * capWeight x * F x ^ 2) =
      (Ioi Real.pi).indicator (fun x : ℝ =>
        Real.pi ^ (-5 / 2 : ℝ) * (x ^ 6 * F x ^ 2) -
          (4 * Real.pi ^ (7 / 2 : ℝ)) * F x ^ 2) := by
  funext x
  by_cases hx : Real.pi < x
  · rw [indicator_of_mem (s := Ioi Real.pi) hx, capWeight_density_above_pi x hx]
    ring
  · simp [capWeight, hx]


/-- Positive tail mass forces strict endpoint-weighted domination for an
arbitrary real function; no continuity or analyticity is needed. -/
theorem strict_weighted_mass_of_tail_pos (F : ℝ → ℝ) (b p : ℝ)
    (hb : 0 < b) (hp : 0 < p)
    (hF : IntegrableOn (fun x : ℝ => F x ^ 2) (Ioi b))
    (hW : IntegrableOn (fun x : ℝ => x ^ p * F x ^ 2) (Ioi 0))
    (hD : 0 < ∫ x : ℝ in Ioi b, F x ^ 2) :
    b ^ p * (∫ x : ℝ in Ioi b, F x ^ 2) <
      ∫ x : ℝ in Ioi 0, x ^ p * F x ^ 2 := by
  have hw := hW.mono_set (Ioi_subset_Ioi hb.le)
  let g : ℝ → ℝ := fun x => (x ^ p - b ^ p) * F x ^ 2
  have hgi : IntegrableOn g (Ioi b) :=
    (hw.sub (hF.const_mul (b ^ p))).congr_fun
      (fun x _ => by dsimp [g]; ring) measurableSet_Ioi
  have hgn : 0 ≤ᵐ[volume.restrict (Ioi b)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg
      (sub_nonneg.mpr (Real.rpow_le_rpow hb.le hx.le hp.le)) (sq_nonneg _)
  have hgp : 0 < ∫ x : ℝ in Ioi b, g x := by
    by_contra hn
    have hz : (∫ x : ℝ in Ioi b, g x) = 0 :=
      le_antisymm (le_of_not_gt hn) (integral_nonneg_of_ae hgn)
    have hzae := (integral_eq_zero_iff_of_nonneg_ae hgn hgi).1 hz
    have hsqae : (fun x : ℝ => F x ^ 2) =ᵐ[volume.restrict (Ioi b)] 0 := by
      filter_upwards [hzae, ae_restrict_mem measurableSet_Ioi] with x hx hbx
      have hweight : 0 < x ^ p - b ^ p :=
        sub_pos.mpr (Real.rpow_lt_rpow hb.le hbx hp)
      exact (mul_eq_zero.mp hx).resolve_left hweight.ne'
    have hzero : (∫ x : ℝ in Ioi b, F x ^ 2) = 0 :=
      (integral_eq_zero_iff_of_nonneg_ae
        (Eventually.of_forall (fun x : ℝ => sq_nonneg (F x))) hF).2 hsqae
    linarith
  have he : (∫ x : ℝ in Ioi b, g x) =
      (∫ x : ℝ in Ioi b, x ^ p * F x ^ 2) -
        b ^ p * (∫ x : ℝ in Ioi b, F x ^ 2) := by
    dsimp [g]
    simp_rw [sub_mul]
    rw [integral_sub hw (hF.const_mul _), integral_const_mul]
  have hm : (∫ x : ℝ in Ioi b, x ^ p * F x ^ 2) ≤
      ∫ x : ℝ in Ioi 0, x ^ p * F x ^ 2 := by
    apply setIntegral_mono_set hW
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_nonneg (Real.rpow_nonneg hx.le _) (sq_nonneg _)
    · exact Eventually.of_forall (fun x hx => lt_trans hb hx)
  exact lt_of_lt_of_le (sub_pos.mp (he ▸ hgp)) hm

/-- A positive actual cap coercivity bound supplies tail positivity and the
strict original scaled quotient for every real function. Positive totalized
integrals themselves imply the needed genuine integrability. -/
theorem capWeight_coercivity_tail_pos_and_ratio (F : ℝ → ℝ) (γ : ℝ)
    (hγ : 0 < γ)
    (hH : 0 < ∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * F x ^ 2)
    (hcoerce :
      γ * (∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * F x ^ 2) ≤
        ∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * capWeight x * F x ^ 2) :
    0 < (∫ x in Ioi Real.pi, F x ^ 2) ∧
      4 + γ < (∫ x in Ioi Real.pi, x ^ 6 * F x ^ 2) /
        (Real.pi ^ 6 * (∫ x in Ioi Real.pi, F x ^ 2)) := by
  have hHi : IntegrableOn (fun x : ℝ => x ^ (7 / 2 : ℝ) * F x ^ 2) (Ioi 0) :=
    Integrable.of_integral_ne_zero hH.ne'
  have hQpos : 0 <
      ∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * capWeight x * F x ^ 2 :=
    lt_of_lt_of_le (mul_pos hγ hH) hcoerce
  have hQi : IntegrableOn
      (fun x : ℝ => x ^ (7 / 2 : ℝ) * capWeight x * F x ^ 2) (Ioi 0) :=
    Integrable.of_integral_ne_zero hQpos.ne'
  have hHt := hHi.mono_set (Ioi_subset_Ioi Real.pi_pos.le)
  have hsqmeas : AEStronglyMeasurable (fun x : ℝ => F x ^ 2)
      (volume.restrict (Ioi Real.pi)) := by
    have hw : AEStronglyMeasurable (fun x : ℝ => x ^ (7 / 2 : ℝ))
        (volume.restrict (Ioi Real.pi)) :=
      (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 7 / 2)).aestronglyMeasurable
    apply (hHt.aestronglyMeasurable.div₀ hw).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 := lt_trans Real.pi_pos hx
    dsimp
    field_simp [(Real.rpow_pos_of_pos hx0 (7 / 2 : ℝ)).ne']
  have hDi : IntegrableOn (fun x : ℝ => F x ^ 2) (Ioi Real.pi) := by
    apply hHt.mono' hsqmeas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hw : 1 ≤ x ^ (7 / 2 : ℝ) :=
      Real.one_le_rpow (by linarith [Real.pi_gt_three]) (by norm_num)
    nlinarith [sq_nonneg (F x)]
  have hQt := hQi.mono_set (Ioi_subset_Ioi Real.pi_pos.le)
  have hNi : IntegrableOn (fun x : ℝ => x ^ 6 * F x ^ 2) (Ioi Real.pi) := by
    have hi := (hQt.add (hDi.const_mul (4 * Real.pi ^ (7 / 2 : ℝ)))).const_mul
      (Real.pi ^ (-5 / 2 : ℝ))⁻¹
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    dsimp
    rw [capWeight_density_above_pi x hx]
    field_simp [(Real.rpow_pos_of_pos Real.pi_pos (-5 / 2 : ℝ)).ne']
    <;> ring
  have hQeq :
      (∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * capWeight x * F x ^ 2) =
        Real.pi ^ (-5 / 2 : ℝ) * (∫ x in Ioi Real.pi, x ^ 6 * F x ^ 2) -
          4 * Real.pi ^ (7 / 2 : ℝ) * (∫ x in Ioi Real.pi, F x ^ 2) := by
    rw [capWeight_density_indicator, setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi Real.pi_pos.le)]
    rw [integral_sub (hNi.const_mul _) (hDi.const_mul _),
      integral_const_mul, integral_const_mul]
  have hD : 0 < ∫ x in Ioi Real.pi, F x ^ 2 := by
    have hn : 0 ≤ ∫ x in Ioi Real.pi, F x ^ 2 :=
      integral_nonneg (fun _ => sq_nonneg _)
    by_contra hnot
    have hz : (∫ x in Ioi Real.pi, F x ^ 2) = 0 :=
      le_antisymm (le_of_not_gt hnot) hn
    have hzae := (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall (fun x : ℝ => sq_nonneg (F x))) hDi).1 hz
    have hNz : (∫ x in Ioi Real.pi, x ^ 6 * F x ^ 2) = 0 := by
      calc
        _ = ∫ x in Ioi Real.pi, (0 : ℝ) := by
          apply integral_congr_ae
          filter_upwards [hzae] with x hx
          simp only [Pi.zero_apply] at hx
          rw [hx, mul_zero]
        _ = 0 := by simp
    rw [hNz, hz] at hQeq
    linarith only [hQeq, hQpos]
  have hstrict := strict_weighted_mass_of_tail_pos F Real.pi (7 / 2 : ℝ)
    Real.pi_pos (by norm_num) hDi hHi hD
  rw [hQeq] at hcoerce
  have hraw :
      (4 + γ) * Real.pi ^ (7 / 2 : ℝ) * (∫ x in Ioi Real.pi, F x ^ 2) <
        Real.pi ^ (-5 / 2 : ℝ) * (∫ x in Ioi Real.pi, x ^ 6 * F x ^ 2) := by
    have h := mul_lt_mul_of_pos_left hstrict hγ
    linarith only [h, hcoerce]
  have hscale : Real.pi ^ (5 / 2 : ℝ) * Real.pi ^ (7 / 2 : ℝ) = Real.pi ^ 6 := by
    rw [← Real.rpow_add Real.pi_pos]
    norm_num [Real.rpow_natCast]
  have hcancel : Real.pi ^ (5 / 2 : ℝ) * Real.pi ^ (-5 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add Real.pi_pos]
    norm_num
  have hnum : (4 + γ) * (Real.pi ^ 6 * (∫ x in Ioi Real.pi, F x ^ 2)) <
      ∫ x in Ioi Real.pi, x ^ 6 * F x ^ 2 := by
    calc
      _ = Real.pi ^ (5 / 2 : ℝ) *
          ((4 + γ) * Real.pi ^ (7 / 2 : ℝ) * (∫ x in Ioi Real.pi, F x ^ 2)) := by
        rw [← hscale]
        ring
      _ < Real.pi ^ (5 / 2 : ℝ) *
          (Real.pi ^ (-5 / 2 : ℝ) * (∫ x in Ioi Real.pi, x ^ 6 * F x ^ 2)) :=
        mul_lt_mul_of_pos_left hraw (Real.rpow_pos_of_pos Real.pi_pos _)
      _ = _ := by rw [← mul_assoc, hcancel, one_mul]
  exact ⟨hD, (lt_div_iff₀ (mul_pos (pow_pos Real.pi_pos 6) hD)).2 hnum⟩

end FiniteGaussianCap475

