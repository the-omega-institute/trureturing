/- GID: D5/S3/Quantum/Analysis/BosonicRenyiStieltjes/PoissonWeight
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/BosonicRenyiStieltjes/PoissonWeight
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Positive-axis Stieltjes transform of the power Poisson density. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! The positive-axis transform used by the logarithmic Renyi representation. -/

namespace D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight

open Real Set MeasureTheory

noncomputable section

/-- Positivity of the signed trigonometric factor on the required order range. -/
theorem sine_factor_pos {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2) (ha1 : α ≠ 1) :
    0 < -Real.sin (Real.pi * α) / (α - 1) := by
  rcases lt_or_gt_of_ne ha1 with ha | ha
  · have hs : 0 < Real.sin (Real.pi * α) :=
      Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ha0)
        (by nlinarith [Real.pi_pos])
    exact div_pos_of_neg_of_neg (neg_neg_of_pos hs) (sub_neg.mpr ha)
  · have hs : 0 < Real.sin (Real.pi * α - Real.pi) :=
      Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos])
        (by nlinarith [Real.pi_pos])
    rw [Real.sin_sub_pi] at hs
    exact div_pos hs (sub_pos.mpr ha)

/-- The Poisson angle is nondegenerate on the required order range. -/
theorem cosine_lt_one {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2) (ha1 : α ≠ 1) :
    Real.cos (Real.pi * α) < 1 := by
  have hs := sine_factor_pos ha0 ha2 ha1
  have hsin : Real.sin (Real.pi * α) ≠ 0 := by
    intro hz
    rw [hz, neg_zero, zero_div] at hs
    exact lt_irrefl 0 hs
  refine lt_of_le_of_ne (Real.cos_le_one _) ?_
  intro he
  have hsq := Real.sin_sq_add_cos_sq (Real.pi * α)
  rw [he] at hsq
  have hz : Real.sin (Real.pi * α) = 0 := by nlinarith
  exact hsin hz

/-- The power Poisson density after the substitution `p = q ^ α`. -/
def density (α q : ℝ) : ℝ :=
  α * q ^ (α - 1) * (-Real.sin (Real.pi * α)) /
    (Real.pi * (α - 1) * (1 - 2 * q ^ α * Real.cos (Real.pi * α) + (q ^ α) ^ 2))

/-- Reciprocal reflection preserves the density with its change-of-variables factor. -/
theorem density_reflection {α q : ℝ} (hq : 0 < q)
    (ha1 : α ≠ 1) (hc : Real.cos (Real.pi * α) < 1) :
    density α q⁻¹ / q ^ 2 = density α q := by
  have hp := Real.rpow_pos_of_pos hq α
  have hD : 0 < 1 - 2 * q ^ α * Real.cos (Real.pi * α) + (q ^ α) ^ 2 := by
    nlinarith [mul_pos hp (sub_pos.mpr hc), sq_nonneg (q ^ α - 1)]
  dsimp only [density]
  rw [Real.inv_rpow hq.le, Real.inv_rpow hq.le, Real.rpow_sub_one hq.ne']
  field_simp (disch := first | positivity | assumption | exact sub_ne_zero.mpr ha1 |
    nlinarith [hD])
  ring

private lemma density_integrable_unit {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) : IntegrableOn (density α) (Ioo 0 1) := by
  let f := fun q : ℝ => α * (-Real.sin (Real.pi * α)) /
    (Real.pi * (α - 1) * (1 - 2 * q ^ α * Real.cos (Real.pi * α) + (q ^ α) ^ 2))
  have hc : ContinuousOn f (Icc 0 1) := by
    intro q hq
    have hp := Real.rpow_nonneg hq.1 α
    have hcos := cosine_lt_one ha0 ha2 ha1
    have hD : 0 < 1 - 2 * q ^ α * Real.cos (Real.pi * α) + (q ^ α) ^ 2 := by
      by_cases hz : q ^ α = 0
      · rw [hz]
        norm_num
      · have hpos := lt_of_le_of_ne hp (Ne.symm hz)
        nlinarith [mul_pos hpos (sub_pos.mpr hcos), sq_nonneg (q ^ α - 1)]
    have hpow : ContinuousAt (fun y : ℝ => y ^ α) q :=
      (Real.continuous_rpow_const ha0.le).continuousAt
    have hden : ContinuousAt (fun y : ℝ =>
        1 - 2 * y ^ α * Real.cos (Real.pi * α) + (y ^ α) ^ 2) q :=
      (continuousAt_const.sub ((hpow.const_mul 2).mul_const
        (Real.cos (Real.pi * α)))).add (hpow.pow 2)
    exact (continuousAt_const.div (hden.const_mul (Real.pi * (α - 1)))
      (mul_ne_zero (mul_ne_zero Real.pi_ne_zero (sub_ne_zero.mpr ha1)) hD.ne')).continuousWithinAt
  have hi : IntegrableOn (fun q : ℝ => q ^ (α - 1)) (Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by linarith)
  apply (hi.mul_continuousOn_of_subset hc measurableSet_Ioo
    isCompact_Icc Ioo_subset_Icc_self).congr_fun _ measurableSet_Ioo
  intro q _
  dsimp only [density, f]
  ring

private lemma density_resolvent_integrable {α r : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hr0 : 0 < r) :
    IntegrableOn (fun q => density α q / (r + q)) (Ioi 0) := by
  let g := fun q => density α q / (r + q)
  have hi := density_integrable_unit ha0 ha2 ha1
  have hhead : IntegrableOn g (Ioo 0 1) := by
    have hc : ContinuousOn (fun q : ℝ => 1 / (r + q)) (Icc 0 1) := by
      intro q hq
      exact (continuousAt_const.div (continuousAt_const.add continuousAt_id)
        (add_pos_of_pos_of_nonneg hr0 hq.1).ne').continuousWithinAt
    simpa only [g, div_eq_mul_inv, one_mul] using
      hi.mul_continuousOn_of_subset hc measurableSet_Ioo isCompact_Icc Ioo_subset_Icc_self
  have hreflect : IntegrableOn (fun q => density α q * q / (1 + r * q)) (Ioo 0 1) := by
    have hc : ContinuousOn (fun q : ℝ => q / (1 + r * q)) (Icc 0 1) := by
      intro q hq
      exact (continuousAt_id.div
        (continuousAt_const.add (continuousAt_const.mul continuousAt_id))
        (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hr0.le hq.1)).ne').continuousWithinAt
    simpa only [mul_div_assoc] using
      hi.mul_continuousOn_of_subset hc measurableSet_Ioo isCompact_Icc Ioo_subset_Icc_self
  have him : (fun q : ℝ => q⁻¹) '' Ioo (0 : ℝ) 1 = Ioi 1 := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact (one_lt_inv₀ hq.1).mpr hq.2
    · intro hy
      have hy0 : 0 < y := lt_trans zero_lt_one hy
      exact ⟨y⁻¹, ⟨inv_pos.mpr hy0, (inv_lt_one₀ hy0).mpr hy⟩, inv_inv y⟩
  have hinj : InjOn (fun q : ℝ => q⁻¹) (Ioo 0 1) :=
    fun _ _ _ _ h => inv_injective h
  have hd : ∀ q ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt (fun q : ℝ => q⁻¹) (-(q ^ 2)⁻¹) (Ioo 0 1) q :=
    fun q hq => (hasDerivAt_inv hq.1.ne').hasDerivWithinAt
  have htail : IntegrableOn g (Ioi 1) := by
    rw [← him]
    apply (integrableOn_image_iff_integrableOn_abs_deriv_smul
      measurableSet_Ioo hd hinj g).mpr
    apply hreflect.congr_fun _ measurableSet_Ioo
    intro q hq
    have hq0 := hq.1
    dsimp only
    rw [abs_neg, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg q)), smul_eq_mul]
    dsimp only [g]
    symm
    calc
      _ = (density α q⁻¹ / q ^ 2) / (r + q⁻¹) := by ring
      _ = density α q / (r + q⁻¹) := by
        rw [density_reflection hq.1 ha1 (cosine_lt_one ha0 ha2 ha1)]
      _ = _ := by
        field_simp (disch := positivity)
        ring
  have hsets : Ioo (0 : ℝ) 1 ∪ Ici 1 = Ioi 0 := by
    ext q
    simp only [mem_union, mem_Ioo, mem_Ici, mem_Ioi]
    constructor
    · rintro (hq | hq) <;> linarith
    · intro hq
      rcases lt_or_ge q 1 with h | h
      · exact Or.inl ⟨hq, h⟩
      · exact Or.inr h
  have hu := hhead.union ((integrableOn_Ici_iff_integrableOn_Ioi).mpr htail)
  simpa only [hsets] using hu

private lemma stieltjes_value {α r : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hr0 : 0 < r) (hr1 : r < 1) :
    (∫ q in Ioi (0 : ℝ), density α q / (r + q)) =
      1 / ((α - 1) * (1 - r)) -
        α * r ^ (α - 1) / ((α - 1) * (1 - r ^ α)) := by
  sorry

/-- Stieltjes transform on the positive axis, with its pole at `r = 1` subtracted. -/
theorem stieltjes_integral {α r : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hr0 : 0 < r) (hr1 : r < 1) :
    IntegrableOn (fun q => density α q / (r + q)) (Ioi 0) ∧
      (∫ q in Ioi (0 : ℝ), density α q / (r + q)) =
        1 / ((α - 1) * (1 - r)) -
          α * r ^ (α - 1) / ((α - 1) * (1 - r ^ α)) := by
  exact ⟨density_resolvent_integrable ha0 ha2 ha1 hr0, stieltjes_value ha0 ha2 ha1 hr0 hr1⟩

end

end D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight
