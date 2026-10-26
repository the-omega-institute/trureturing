/- GID: D5/S3/Analytic/Interpolation/CapWeightedEnergySharpness
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/CapWeightedEnergySharpness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Explicit scalar extremizers attain the cap-weighted-energy interpolation constant. -/

import D5.S3.Analytic.Interpolation.CapWeightedEnergy

/-! Scalar extremizers attain the abstract cap and weighted-energy coefficient. -/

noncomputable section
open Set MeasureTheory

open D5.S3.Analytic.Interpolation.CapWeightedEnergy

namespace D5.S3.Analytic.Interpolation.CapWeightedEnergySharpness

/-- The cap is saturated up to the cutoff; the free quadratic optimum follows it. -/
def extremizer (alpha B a t : ℝ) : ℝ :=
  if t ≤ a then B else B * (a / t) ^ (alpha + 1)

private theorem extremizer_nonneg (alpha B a t : ℝ) (hB : 0 ≤ B) (ha : 0 ≤ a)
    (ht : 0 < t) : 0 ≤ extremizer alpha B a t := by
  unfold extremizer
  split_ifs <;> positivity

private theorem extremizer_cap (alpha B a t : ℝ) (halpha : 0 < alpha)
    (hB : 0 ≤ B) (ha : 0 ≤ a) (ht : 0 < t) :
    ‖extremizer alpha B a t‖ ≤ B := by
  rw [Real.norm_eq_abs, abs_of_nonneg (extremizer_nonneg alpha B a t hB ha ht)]
  unfold extremizer
  split_ifs with hta
  · exact le_rfl
  · have hratio : a / t ≤ 1 := (div_le_one ht).2 (lt_of_not_ge hta).le
    exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_one (div_nonneg ha ht.le) hratio (by linarith)) hB).trans_eq
        (mul_one B)

private theorem extremizer_measurable (alpha B a : ℝ) :
    Measurable (extremizer alpha B a) := by
  change Measurable ((Iic a).piecewise (fun _ : ℝ => B)
    (fun t : ℝ => B * (a / t) ^ (alpha + 1)))
  exact measurable_const.piecewise measurableSet_Iic
    (measurable_const.mul ((measurable_const.div measurable_id).pow_const _))

private theorem extremizer_energy_tail (alpha B a t : ℝ) (ha : 0 < a)
    (ht : a < t) :
    t * ‖extremizer alpha B a t‖ ^ 2 =
      B ^ 2 * a ^ (2 * alpha + 2) * t ^ (-2 * alpha - 1) := by
  have ht0 : 0 < t := ha.trans ht
  rw [extremizer, if_neg ht.not_ge, Real.norm_eq_abs, sq_abs, mul_pow,
    ← Real.rpow_natCast ((a / t) ^ (alpha + 1)) 2,
    ← Real.rpow_mul (div_nonneg ha.le ht0.le)]
  norm_num only [Nat.cast_ofNat]
  rw [show (alpha + 1) * 2 = 2 * alpha + 2 by ring,
    Real.div_rpow ha.le ht0.le,
    show -2 * alpha - 1 = 1 - (2 * alpha + 2) by ring,
    Real.rpow_sub ht0, Real.rpow_one]
  ring

private theorem extremizer_readout_tail (alpha B a t : ℝ) (ha : 0 < a)
    (ht : a < t) :
    t ^ (-alpha) * extremizer alpha B a t =
      B * a ^ (alpha + 1) * t ^ (-2 * alpha - 1) := by
  have ht0 : 0 < t := ha.trans ht
  rw [extremizer, if_neg ht.not_ge, Real.div_rpow ha.le ht0.le,
    show -2 * alpha - 1 = -alpha - (alpha + 1) by ring,
    Real.rpow_sub ht0]
  ring

private theorem cutoff_disjoint (a : ℝ) :
    Disjoint (Ioc (0 : ℝ) a) (Ioi a) :=
  Set.disjoint_left.mpr fun _ ht ht' => ht'.not_ge ht.2

private theorem extremizer_energy (alpha B a : ℝ) (halpha : 0 < alpha)
    (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t * ‖extremizer alpha B a t‖ ^ 2) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), t * ‖extremizer alpha B a t‖ ^ 2) =
        B ^ 2 * a ^ 2 * ((alpha + 1) / (2 * alpha)) := by
  let f : ℝ → ℝ := fun t => t * ‖extremizer alpha B a t‖ ^ 2
  have hn : EqOn f (fun t => B ^ 2 * t) (Ioc (0 : ℝ) a) := by
    intro t ht
    simp only [f, extremizer, if_pos ht.2, Real.norm_eq_abs, sq_abs]
    ring
  have ht : EqOn f (fun t => B ^ 2 * a ^ (2 * alpha + 2) *
      t ^ (-2 * alpha - 1)) (Ioi a) := by
    intro t ht
    exact extremizer_energy_tail alpha B a t ha ht
  obtain ⟨hil, hvl⟩ := linear_integral_near a ha
  obtain ⟨hip, hvp⟩ := power_integral_tail alpha a halpha ha
  have hin : IntegrableOn f (Ioc (0 : ℝ) a) :=
    IntegrableOn.congr_fun (hil.const_mul (B ^ 2))
      (fun t ht => (hn ht).symm) measurableSet_Ioc
  have hit : IntegrableOn f (Ioi a) :=
    IntegrableOn.congr_fun (hip.const_mul (B ^ 2 * a ^ (2 * alpha + 2)))
      (fun t ht' => (ht ht').symm) measurableSet_Ioi
  have hi : IntegrableOn f (Ioi (0 : ℝ)) := by
    rw [← Ioc_union_Ioi_eq_Ioi ha.le, integrableOn_union]
    exact ⟨hin, hit⟩
  refine ⟨hi, ?_⟩
  change (∫ t in Ioi (0 : ℝ), f t) = _
  rw [← Ioc_union_Ioi_eq_Ioi ha.le,
    setIntegral_union (cutoff_disjoint a) measurableSet_Ioi hin hit,
    setIntegral_congr_fun measurableSet_Ioc hn,
    setIntegral_congr_fun measurableSet_Ioi ht,
    integral_const_mul, integral_const_mul, hvl, hvp]
  have hprod : a ^ (2 * alpha + 2) * a ^ (-2 * alpha) = a ^ 2 := by
    rw [← Real.rpow_add ha]
    norm_num [show 2 * alpha + 2 + -2 * alpha = 2 by ring]
  calc
    _ = B ^ 2 * a ^ 2 / 2 +
        B ^ 2 * (a ^ (2 * alpha + 2) * a ^ (-2 * alpha)) / (2 * alpha) := by ring
    _ = _ := by rw [hprod]; field_simp [halpha.ne']

private theorem extremizer_readout (alpha B a : ℝ) (halpha0 : 0 < alpha)
    (halpha1 : alpha < 1) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ (-alpha) * extremizer alpha B a t) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), t ^ (-alpha) * extremizer alpha B a t) =
        B * a ^ (1 - alpha) * (1 / (1 - alpha) + 1 / (2 * alpha)) := by
  let f : ℝ → ℝ := fun t => t ^ (-alpha) * extremizer alpha B a t
  have hn : EqOn f (fun t => B * t ^ (-alpha)) (Ioc (0 : ℝ) a) := by
    intro t ht
    simp only [f, extremizer, if_pos ht.2]
    ring
  have ht : EqOn f (fun t => B * a ^ (alpha + 1) *
      t ^ (-2 * alpha - 1)) (Ioi a) := by
    intro t ht
    exact extremizer_readout_tail alpha B a t ha ht
  obtain ⟨hinp, hvnp⟩ := power_integral_near alpha a halpha1 ha
  obtain ⟨hitp, hvtp⟩ := power_integral_tail alpha a halpha0 ha
  have hin : IntegrableOn f (Ioc (0 : ℝ) a) :=
    IntegrableOn.congr_fun (hinp.const_mul B)
      (fun t ht => (hn ht).symm) measurableSet_Ioc
  have hit : IntegrableOn f (Ioi a) :=
    IntegrableOn.congr_fun (hitp.const_mul (B * a ^ (alpha + 1)))
      (fun t ht' => (ht ht').symm) measurableSet_Ioi
  have hi : IntegrableOn f (Ioi (0 : ℝ)) := by
    rw [← Ioc_union_Ioi_eq_Ioi ha.le, integrableOn_union]
    exact ⟨hin, hit⟩
  refine ⟨hi, ?_⟩
  change (∫ t in Ioi (0 : ℝ), f t) = _
  rw [← Ioc_union_Ioi_eq_Ioi ha.le,
    setIntegral_union (cutoff_disjoint a) measurableSet_Ioi hin hit,
    setIntegral_congr_fun measurableSet_Ioc hn,
    setIntegral_congr_fun measurableSet_Ioi ht,
    integral_const_mul, integral_const_mul, hvnp, hvtp]
  have hprod : a ^ (alpha + 1) * a ^ (-2 * alpha) = a ^ (1 - alpha) := by
    rw [← Real.rpow_add ha]
    congr 1; ring
  calc
    _ = B * a ^ (1 - alpha) / (1 - alpha) +
        B * (a ^ (alpha + 1) * a ^ (-2 * alpha)) / (2 * alpha) := by ring
    _ = _ := by rw [hprod]; ring

/-- Actual integrable moments of an admissible scalar extremizer. -/
theorem extremizer_admissible_and_moments (alpha B a : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) (hB : 0 ≤ B) (ha : 0 < a) :
    AEStronglyMeasurable (extremizer alpha B a) (volume.restrict (Ioi (0 : ℝ))) ∧
    (∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), ‖extremizer alpha B a t‖ ≤ B) ∧
    (IntegrableOn (fun t : ℝ => t * ‖extremizer alpha B a t‖ ^ 2) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), t * ‖extremizer alpha B a t‖ ^ 2) =
        B ^ 2 * a ^ 2 * ((alpha + 1) / (2 * alpha))) ∧
    (IntegrableOn (fun t : ℝ => t ^ (-alpha) * extremizer alpha B a t) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), t ^ (-alpha) * extremizer alpha B a t) =
        B * a ^ (1 - alpha) * (1 / (1 - alpha) + 1 / (2 * alpha))) := by
  refine ⟨(extremizer_measurable alpha B a).aestronglyMeasurable, ?_,
    extremizer_energy alpha B a halpha0 ha,
    extremizer_readout alpha B a halpha0 halpha1 ha⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact extremizer_cap alpha B a t halpha0 hB ha.le ht

/-- Any coefficient valid for every admissible scalar function is at least
the coefficient proved for all Banach carriers in `norm_integral_le_sharp_cap_energy`. -/
theorem sharp_constant_le_of_uniform_bound (alpha C : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (huniform : ∀ (w : ℝ → ℝ) (B delta : ℝ), 0 ≤ B → 0 ≤ delta →
      AEStronglyMeasurable w (volume.restrict (Ioi (0 : ℝ))) →
      (∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), ‖w t‖ ≤ B) →
      IntegrableOn (fun t : ℝ => t * ‖w t‖ ^ 2) (Ioi 0) →
      (∫ t in Ioi (0 : ℝ), t * ‖w t‖ ^ 2) ≤ delta →
      ‖∫ t in Ioi (0 : ℝ), t ^ (-alpha) * w t‖ ≤
        C * B ^ alpha * delta ^ ((1 - alpha) / 2)) :
    sharpConstant alpha ≤ C := by
  have hgap : 0 < 1 - alpha := sub_pos.mpr halpha1
  let q : ℝ := (alpha + 1) / (2 * alpha)
  have hq : 0 < q := div_pos (by linarith) (by positivity)
  obtain ⟨hm, hc, ⟨he, hev⟩, ⟨_, hrv⟩⟩ :=
    extremizer_admissible_and_moments alpha 1 1 halpha0 halpha1 (by norm_num) (by norm_num)
  simp only [one_pow, Real.one_rpow, one_mul, mul_one] at hev hrv
  have h := huniform (extremizer alpha 1 1) 1 q (by norm_num) hq.le hm hc he (by
    change _ ≤ (alpha + 1) / (2 * alpha)
    exact hev.le)
  rw [hrv, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h
  simp only [Real.one_rpow, mul_one] at h
  have hfactor : sharpConstant alpha * q ^ ((1 - alpha) / 2) =
      1 / (1 - alpha) + 1 / (2 * alpha) := by
    unfold sharpConstant
    change ((1 - alpha)⁻¹ * q ^ ((alpha + 1) / 2)) * q ^ ((1 - alpha) / 2) = _
    rw [mul_assoc, ← Real.rpow_add hq,
      show (alpha + 1) / 2 + (1 - alpha) / 2 = 1 by ring, Real.rpow_one]
    dsimp only [q]
    field_simp [halpha0.ne', hgap.ne']
    ring
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hq ((1 - alpha) / 2))).mp
  rwa [hfactor]

#print axioms sharp_constant_le_of_uniform_bound

end D5.S3.Analytic.Interpolation.CapWeightedEnergySharpness
