/- GID: D5/S3/Quantum/PositiveResolvent/SwapDifferentiation
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Differentiation of a fixed signed density along a constant-sum resolvent path. -/

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic

namespace D5.S3.Quantum.PositiveResolvent.SwapDifferentiation

open Set MeasureTheory Filter
open scoped Topology

private lemma reciprocal_square_bound {a s h m : ℝ} (ha : 0 < a) (hs : 0 ≤ s)
    (hm : 0 < m) (hma : m ≤ a) (hh : |h| < m / 2) :
    1 / (a + h + s) ^ 2 ≤ (4 / m) * (1 / (a + s)) := by
  have hsmall : -m / 2 < h := by simpa only [neg_div] using (abs_lt.mp hh).1
  have hu : 0 < a + h + s := by linarith
  have hv : 0 < a + s := by positivity
  have hhalf : a + s ≤ 2 * (a + h + s) := by linarith
  have hlow : m / 2 ≤ a + h + s := by linarith
  rw [div_le_iff₀ (sq_pos_of_pos hu)]
  have h1 : m * (a + s) ≤ 4 * (a + h + s) ^ 2 := by
    nlinarith [mul_le_mul hlow hhalf (by positivity : 0 ≤ a + s) hu.le]
  have he : (4 / m) * (1 / (a + s)) * (a + h + s) ^ 2 =
      4 * (a + h + s) ^ 2 / (m * (a + s)) := by field_simp
  rw [he, le_div_iff₀ (mul_pos hm hv)]
  simpa using h1

private lemma path_derivative {x y s h : ℝ} (hx : x + h + s ≠ 0)
    (hy : y - h + s ≠ 0) (d : ℝ) :
    HasDerivAt (fun v => (1 / (x + v + s) + 1 / (y - v + s)) * d)
      ((-1 / (x + h + s) ^ 2 + 1 / (y - h + s) ^ 2) * d) h := by
  have h1 := (((hasDerivAt_id h).const_add x).add_const s).inv hx
  have h2 := (((hasDerivAt_const h y).sub (hasDerivAt_id h)).add_const s).inv hy
  convert! (h1.add h2).mul_const d using 1 <;> (try simp [one_div]) <;> ring

/-- No sign condition is imposed on the density. Absolute domination comes from
    the integrable base resolvent, since its scalar weight is positive. -/
theorem signed_swap_hasDerivAt {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    {d : ℝ → ℝ} (hd : Measurable d)
    (hi : IntegrableOn (fun s => (1 / (x + s) + 1 / (y + s)) * d s) (Ioi 0)) :
    IntegrableOn (fun s => (x + y + 2 * s) / ((x + s) ^ 2 * (y + s) ^ 2) * d s)
        (Ioi 0) ∧
    HasDerivAt (fun h => ∫ s in Ioi (0 : ℝ),
        (1 / (x + h + s) + 1 / (y - h + s)) * d s)
      (-(y - x) * ∫ s in Ioi (0 : ℝ),
        (x + y + 2 * s) / ((x + s) ^ 2 * (y + s) ^ 2) * d s) 0 := by
  let m := min x y
  have hm : 0 < m := lt_min hx hy
  let W := fun s : ℝ => (1 / (x + s) + 1 / (y + s)) * d s
  let D := fun h s : ℝ => (-1 / (x + h + s) ^ 2 + 1 / (y - h + s) ^ 2) * d s
  let J := fun s : ℝ => (x + y + 2 * s) / ((x + s) ^ 2 * (y + s) ^ 2) * d s
  have hbound : ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)), ∀ h ∈ Ioo (-m / 2) (m / 2),
      ‖D h s‖ ≤ (4 / m) * ‖W s‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    change 0 < s at hs
    intro h hh
    have hab : |h| < m / 2 := abs_lt.mpr ⟨by simpa only [neg_div] using hh.1, hh.2⟩
    have habn : |-h| < m / 2 := by simpa using hab
    have hxp : 0 < x + h + s := by have := (abs_lt.mp hab).1; dsimp [m] at *; linarith [min_le_left x y]
    have hyp : 0 < y - h + s := by have := (abs_lt.mp hab).2; dsimp [m] at *; linarith [min_le_right x y]
    have hx0 : 0 < x + s := by positivity
    have hy0 : 0 < y + s := by positivity
    have hb1 := reciprocal_square_bound hx hs.le hm (min_le_left x y) hab
    have hb2 := reciprocal_square_bound hy hs.le hm (min_le_right x y) habn
    have hb2 : 1 / (y - h + s) ^ 2 ≤ (4 / m) * (1 / (y + s)) := by simpa [sub_eq_add_neg] using hb2
    have ha : ‖-1 / (x + h + s) ^ 2 + 1 / (y - h + s) ^ 2‖ ≤
        (4 / m) * (1 / (x + s) + 1 / (y + s)) := by
      calc
        _ ≤ ‖-1 / (x + h + s) ^ 2‖ + ‖1 / (y - h + s) ^ 2‖ := norm_add_le _ _
        _ = 1 / (x + h + s) ^ 2 + 1 / (y - h + s) ^ 2 := by
          rw [norm_div, norm_div, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos (sq_pos_of_pos hxp), abs_of_pos (sq_pos_of_pos hyp)]
          norm_num
        _ ≤ _ := by nlinarith [hb1, hb2]
    simp only [D, W]
    rw [norm_mul, norm_mul, Real.norm_eq_abs (1 / (x + s) + 1 / (y + s)),
      abs_of_pos (by positivity : 0 < 1 / (x + s) + 1 / (y + s))]
    nlinarith [mul_le_mul_of_nonneg_right ha (norm_nonneg (d s))]
  have hdiff : ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)), ∀ h ∈ Ioo (-m / 2) (m / 2),
      HasDerivAt (fun v => (1 / (x + v + s) + 1 / (y - v + s)) * d s) (D h s) h := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    change 0 < s at hs
    intro h hh
    have hxp : 0 < x + h + s := by have := hh.1; dsimp [m] at this; linarith [min_le_left x y]
    have hyp : 0 < y - h + s := by have := hh.2; dsimp [m] at this; linarith [min_le_right x y]
    exact path_derivative hxp.ne' hyp.ne' (d s)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (show -m / 2 < 0 by linarith) (show 0 < m / 2 by positivity))
    (Eventually.of_forall (fun h => (show Measurable (fun s =>
      (1 / (x + h + s) + 1 / (y - h + s)) * d s) by fun_prop).aestronglyMeasurable))
    (show Integrable (fun s => (1 / (x + 0 + s) + 1 / (y - 0 + s)) * d s)
      (volume.restrict (Ioi 0)) by simpa [IntegrableOn] using hi)
    (show AEStronglyMeasurable (D 0) (volume.restrict (Ioi 0)) by
      apply Measurable.aestronglyMeasurable; dsimp [D]; fun_prop)
    hbound (hi.norm.const_mul (4 / m)) hdiff
  have he : ∀ s ∈ Ioi (0 : ℝ), D 0 s = -(y - x) * J s := by
    intro s hs
    have hxs : x + s ≠ 0 := (add_pos hx hs).ne'
    have hys : y + s ≠ 0 := (add_pos hy hs).ne'
    dsimp [D, J]
    simp only [add_zero, sub_zero]
    field_simp [hxs, hys]
    <;> ring
  have hJ : IntegrableOn J (Ioi 0) := by
    apply (hi.norm.const_mul (2 / m ^ 2)).mono'
    · exact (show Measurable J by dsimp [J]; fun_prop).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      change 0 < s at hs
      have hxs : 0 < x + s := by positivity
      have hys : 0 < y + s := by positivity
      have hm2 : 0 < m ^ 2 := sq_pos_of_pos hm
      have hmx : m ≤ x + s := (min_le_left x y).trans (by linarith)
      have hmy : m ≤ y + s := (min_le_right x y).trans (by linarith)
      have hw : 0 < 1 / (x + s) + 1 / (y + s) := by positivity
      have hj : 0 < (x + y + 2 * s) / ((x + s) ^ 2 * (y + s) ^ 2) := by positivity
      have hid : (x + y + 2 * s) / ((x + s) ^ 2 * (y + s) ^ 2) =
          (1 / (x + s) + 1 / (y + s)) / ((x + s) * (y + s)) := by field_simp; ring
      have hp : m ^ 2 ≤ (x + s) * (y + s) := by nlinarith [mul_le_mul hmx hmy hm.le hxs.le]
      have hb : (x + y + 2 * s) / ((x + s) ^ 2 * (y + s) ^ 2) ≤
          (2 / m ^ 2) * (1 / (x + s) + 1 / (y + s)) := by
        rw [hid]
        calc
          _ ≤ (1 / (x + s) + 1 / (y + s)) / m ^ 2 := div_le_div_of_nonneg_left hw.le hm2 hp
          _ ≤ _ := by
            have hh := mul_nonneg hw.le (inv_pos.mpr hm2).le
            simp only [div_eq_mul_inv, one_mul] at *
            nlinarith
      simp only [J]
      rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_pos hj, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hw]
      nlinarith [mul_le_mul_of_nonneg_right hb (abs_nonneg (d s))]
  refine ⟨hJ, ?_⟩
  have hint : (∫ s in Ioi (0 : ℝ), D 0 s) = -(y - x) * ∫ s in Ioi (0 : ℝ), J s := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi he
  rw [hint] at h
  exact h.2

end D5.S3.Quantum.PositiveResolvent.SwapDifferentiation
