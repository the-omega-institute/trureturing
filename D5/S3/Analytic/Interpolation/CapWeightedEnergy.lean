/- GID: D5/S3/Analytic/Interpolation/CapWeightedEnergy
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/CapWeightedEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An essential cap and weighted energy control inverse-power integrals. -/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
For 0 < alpha < 1, the cap and the actual weighted energy control the
Bochner integral of t^(-alpha) w(t). Integrability is a conclusion, not
an assumption on an integral which might otherwise default to zero.

The new analytic step is the cap-sensitive quadratic majorant. Neither
Holder alone nor the existing near/tail split gives this coefficient.
The abstract sharp coefficient does not assert optimality for resolvents.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace D5.S3.Analytic.Interpolation.CapWeightedEnergy

/-- The scale-invariant coefficient for the cap and weighted-energy bound. -/
def sharpConstant (alpha : ℝ) : ℝ :=
  (1 - alpha)⁻¹ * ((alpha + 1) / (2 * alpha)) ^ ((alpha + 1) / 2)

/-- The inverse power is integrable at zero precisely in the range used here. -/
theorem power_integral_near (alpha a : ℝ) (halpha : alpha < 1) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ (-alpha)) (Ioc 0 a) ∧
      (∫ t in Ioc (0 : ℝ) a, t ^ (-alpha)) = a ^ (1 - alpha) / (1 - alpha) := by
  have hi := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := a)
    (r := -alpha) (by linarith)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le] at hi
  refine ⟨hi, ?_⟩
  rw [← intervalIntegral.integral_of_le ha.le, integral_rpow (Or.inl (by linarith))]
  simp only [show -alpha + 1 = 1 - alpha by ring,
    Real.zero_rpow (by linarith : 1 - alpha ≠ 0), sub_zero]

/-- The quadratic-majorant tail has its exact positive improper integral. -/
theorem power_integral_tail (alpha a : ℝ) (halpha : 0 < alpha) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ (-2 * alpha - 1)) (Ioi a) ∧
      (∫ t in Ioi a, t ^ (-2 * alpha - 1)) = a ^ (-2 * alpha) / (2 * alpha) := by
  refine ⟨integrableOn_Ioi_rpow_of_lt (by linarith) ha, ?_⟩
  have h := integral_Ioi_rpow_of_lt (a := -2 * alpha - 1) (by linarith) ha
  rw [show -2 * alpha - 1 + 1 = -2 * alpha by ring] at h
  calc
    (∫ t in Ioi a, t ^ (-2 * alpha - 1)) = -a ^ (-2 * alpha) / (-2 * alpha) := h
    _ = a ^ (-2 * alpha) / (2 * alpha) := by
      field_simp [halpha.ne']

/-- The capped profile has an exactly integrable linear energy near zero. -/
theorem linear_integral_near (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t) (Ioc 0 a) ∧
      (∫ t in Ioc (0 : ℝ) a, t) = a ^ 2 / 2 := by
  have hi := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := a)
    (r := (1 : ℝ)) (by norm_num)
  simp only [Real.rpow_one] at hi
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le] at hi
  refine ⟨hi, ?_⟩
  rw [← intervalIntegral.integral_of_le ha.le]
  simpa using (integral_id (a := (0 : ℝ)) (b := a))

private theorem quadratic_cap_bound (p q B x : ℝ)
    (hq : 0 ≤ q) (hxB : x ≤ B) (hp : 2 * q * B ≤ p) :
    p * x ≤ q * x ^ 2 + (p * B - q * B ^ 2) := by
  have hprod := mul_nonneg (sub_nonneg.mpr hxB)
    (show 0 ≤ p - q * (B + x) by nlinarith [mul_nonneg hq (sub_nonneg.mpr hxB)])
  nlinarith

private theorem quadratic_free_bound (p q x : ℝ) (hq : 0 < q) :
    p * x ≤ q * x ^ 2 + p ^ 2 / (4 * q) := by
  have h := sq_nonneg (2 * q * x - p)
  have hd : 0 < 4 * q := by positivity
  have hle : (p * x - q * x ^ 2) * (4 * q) ≤ p ^ 2 := by nlinarith
  have h := (le_div_iff₀ hd).2 hle
  linarith

private theorem near_threshold (alpha a B lambda t : ℝ)
    (halpha : 0 < alpha) (hB : 0 < B) (hlambda : 0 < lambda)
    (hscale : 2 * lambda * B * a ^ (alpha + 1) = 1)
    (ht : 0 < t) (hta : t ≤ a) :
    2 * (lambda * t) * B ≤ t ^ (-alpha) := by
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos ht alpha)).mp
  calc
    (2 * (lambda * t) * B) * t ^ alpha =
        2 * lambda * B * t ^ (alpha + 1) := by
      rw [Real.rpow_add_one ht.ne']; ring
    _ ≤ 2 * lambda * B * a ^ (alpha + 1) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht.le hta (by linarith)) (by positivity)
    _ = 1 := hscale
    _ = t ^ (-alpha) * t ^ alpha := by
      rw [← Real.rpow_add ht]; simp

private theorem tail_majorant_identity (alpha lambda t : ℝ)
    (ht : 0 < t) :
    (t ^ (-alpha)) ^ 2 / (4 * (lambda * t)) =
      (4 * lambda)⁻¹ * t ^ (-2 * alpha - 1) := by
  rw [show -2 * alpha - 1 = (-alpha) * 2 - 1 by ring,
    Real.rpow_sub_one ht.ne', Real.rpow_mul ht.le, Real.rpow_two]
  ring

/-- The cap-sensitive majorant estimate at an arbitrary positive cutoff.
The weighted integral is genuinely Bochner integrable under the stated hypotheses. -/
private theorem cutoff_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (w : ℝ → E) (alpha B delta a lambda : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hB : 0 < B) (ha : 0 < a) (hlambda : 0 < lambda)
    (hscale : 2 * lambda * B * a ^ (alpha + 1) = 1)
    (hw : AEStronglyMeasurable w (volume.restrict (Ioi (0 : ℝ))))
    (hcap : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), ‖w t‖ ≤ B)
    (henergy : IntegrableOn (fun t : ℝ => t * ‖w t‖ ^ 2) (Ioi 0))
    (hbudget : (∫ t in Ioi (0 : ℝ), t * ‖w t‖ ^ 2) ≤ delta) :
    IntegrableOn (fun t : ℝ => t ^ (-alpha) • w t) (Ioi 0) ∧
      ‖∫ t in Ioi (0 : ℝ), t ^ (-alpha) • w t‖ ≤
        lambda * delta + B * a ^ (1 - alpha) / (1 - alpha) -
          lambda * B ^ 2 * a ^ 2 / 2 +
          (4 * lambda)⁻¹ * (a ^ (-2 * alpha) / (2 * alpha)) := by
  let N : ℝ → ℝ := fun t => ‖t ^ (-alpha) • w t‖
  let energy : ℝ → ℝ := fun t => t * ‖w t‖ ^ 2
  let near : ℝ → ℝ := fun t => B * t ^ (-alpha) - lambda * B ^ 2 * t
  let tail : ℝ → ℝ := fun t => (4 * lambda)⁻¹ * t ^ (-2 * alpha - 1)
  have hnear_subset : Ioc (0 : ℝ) a ⊆ Ioi 0 := fun _ ht => ht.1
  have htail_subset : Ioi a ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi ha.le
  have hpower : AEStronglyMeasurable (fun t : ℝ => t ^ (-alpha))
      (volume.restrict (Ioi (0 : ℝ))) := by
    exact (continuousOn_id.rpow_const (fun t ht => Or.inl ht.ne')).aestronglyMeasurable
      measurableSet_Ioi
  have hNm : AEStronglyMeasurable N (volume.restrict (Ioi (0 : ℝ))) :=
    (hpower.smul hw).norm
  have hN_eq (t : ℝ) (ht : 0 < t) : N t = t ^ (-alpha) * ‖w t‖ := by
    dsimp only [N]
    rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)]
  obtain ⟨hknear, hvnear⟩ := power_integral_near alpha a halpha1 ha
  obtain ⟨hlinear, hvlinear⟩ := linear_integral_near a ha
  obtain ⟨hktail, hvtail⟩ := power_integral_tail alpha a halpha0 ha
  have hnear : IntegrableOn near (Ioc (0 : ℝ) a) :=
    (hknear.const_mul B).sub (hlinear.const_mul (lambda * B ^ 2))
  have htail : IntegrableOn tail (Ioi a) := hktail.const_mul (4 * lambda)⁻¹
  have hEn : IntegrableOn energy (Ioc (0 : ℝ) a) := henergy.mono_set hnear_subset
  have hEt : IntegrableOn energy (Ioi a) := henergy.mono_set htail_subset
  have hmajorant_near : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) a),
      N t ≤ lambda * energy t + near t := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hnear_subset hcap,
      ae_restrict_mem measurableSet_Ioc] with t hct ht
    rw [hN_eq t ht.1]
    simpa only [energy, near, mul_assoc, mul_comm, mul_left_comm] using
      quadratic_cap_bound (t ^ (-alpha)) (lambda * t) B ‖w t‖
        (mul_nonneg hlambda.le ht.1.le) hct
        (near_threshold alpha a B lambda t halpha0 hB hlambda hscale ht.1 ht.2)
  have hmajorant_tail : ∀ᵐ t ∂volume.restrict (Ioi a),
      N t ≤ lambda * energy t + tail t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ha.trans ht
    rw [hN_eq t ht0]
    have hb := quadratic_free_bound (t ^ (-alpha)) (lambda * t) ‖w t‖
      (mul_pos hlambda ht0)
    rw [tail_majorant_identity alpha lambda t ht0] at hb
    simpa only [energy, tail, mul_assoc] using hb
  have hNn : IntegrableOn N (Ioc (0 : ℝ) a) := by
    apply ((hEn.const_mul lambda).add hnear).mono'
      (hNm.mono_set hnear_subset)
    filter_upwards [hmajorant_near] with t ht
    change |N t| ≤ lambda * energy t + near t
    rw [abs_of_nonneg (show 0 ≤ N t from norm_nonneg _)]
    exact ht
  have hNt : IntegrableOn N (Ioi a) := by
    apply ((hEt.const_mul lambda).add htail).mono' (hNm.mono_set htail_subset)
    filter_upwards [hmajorant_tail] with t ht
    change |N t| ≤ lambda * energy t + tail t
    rw [abs_of_nonneg (show 0 ≤ N t from norm_nonneg _)]
    exact ht
  have hNi : IntegrableOn N (Ioi (0 : ℝ)) := by
    rw [← Ioc_union_Ioi_eq_Ioi ha.le, integrableOn_union]
    exact ⟨hNn, hNt⟩
  have hwi : IntegrableOn (fun t : ℝ => t ^ (-alpha) • w t) (Ioi 0) :=
    ⟨hpower.smul hw, (hasFiniteIntegral_norm_iff _).mp hNi.hasFiniteIntegral⟩
  refine ⟨hwi, ?_⟩
  have hdisj : Disjoint (Ioc (0 : ℝ) a) (Ioi a) := by
    exact Set.disjoint_left.mpr (fun _ ht ht' => (not_lt_of_ge ht.2) ht')
  have hsplitN : (∫ t in Ioi (0 : ℝ), N t) =
      (∫ t in Ioc (0 : ℝ) a, N t) + (∫ t in Ioi a, N t) := by
    rw [← Ioc_union_Ioi_eq_Ioi ha.le]
    exact setIntegral_union hdisj measurableSet_Ioi hNn hNt
  have hsplitE : (∫ t in Ioc (0 : ℝ) a, energy t) + (∫ t in Ioi a, energy t) =
      ∫ t in Ioi (0 : ℝ), energy t := by
    rw [← Ioc_union_Ioi_eq_Ioi ha.le]
    exact (setIntegral_union hdisj measurableSet_Ioi hEn hEt).symm
  have hboundn : (∫ t in Ioc (0 : ℝ) a, N t) ≤
      ∫ t in Ioc (0 : ℝ) a, lambda * energy t + near t :=
    integral_mono_ae hNn ((hEn.const_mul lambda).add hnear) hmajorant_near
  have hboundt : (∫ t in Ioi a, N t) ≤
      ∫ t in Ioi a, lambda * energy t + tail t :=
    integral_mono_ae hNt ((hEt.const_mul lambda).add htail) hmajorant_tail
  have hnear_val : (∫ t in Ioc (0 : ℝ) a, near t) =
      B * a ^ (1 - alpha) / (1 - alpha) - lambda * B ^ 2 * a ^ 2 / 2 := by
    rw [integral_sub (hknear.const_mul B) (hlinear.const_mul (lambda * B ^ 2)),
      integral_const_mul, integral_const_mul, hvnear, hvlinear]
    ring
  have htail_val : (∫ t in Ioi a, tail t) =
      (4 * lambda)⁻¹ * (a ^ (-2 * alpha) / (2 * alpha)) := by
    rw [integral_const_mul, hvtail]
  rw [integral_add (hEn.const_mul lambda) hnear, integral_const_mul, hnear_val] at hboundn
  rw [integral_add (hEt.const_mul lambda) htail, integral_const_mul, htail_val] at hboundt
  calc
    ‖∫ t in Ioi (0 : ℝ), t ^ (-alpha) • w t‖ ≤ ∫ t in Ioi (0 : ℝ), N t :=
      norm_integral_le_integral_norm _
    _ ≤ lambda * (∫ t in Ioi (0 : ℝ), energy t) +
        B * a ^ (1 - alpha) / (1 - alpha) - lambda * B ^ 2 * a ^ 2 / 2 +
        (4 * lambda)⁻¹ * (a ^ (-2 * alpha) / (2 * alpha)) := by
      rw [hsplitN, ← hsplitE]
      linarith
    _ ≤ _ := by gcongr


private theorem optimize_coefficient (alpha B a lambda delta : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) (hB : 0 < B)
    (ha : 0 < a) (hlambda : 0 < lambda)
    (hscale : 2 * lambda * B * a ^ (alpha + 1) = 1)
    (hdelta : delta = B ^ 2 * a ^ 2 * ((alpha + 1) / (2 * alpha))) :
    lambda * delta + B * a ^ (1 - alpha) / (1 - alpha) -
        lambda * B ^ 2 * a ^ 2 / 2 +
        (4 * lambda)⁻¹ * (a ^ (-2 * alpha) / (2 * alpha)) =
      sharpConstant alpha * B ^ alpha * delta ^ ((1 - alpha) / 2) := by
  let q := (alpha + 1) / (2 * alpha)
  let beta := (1 - alpha) / 2
  have hq : 0 < q := div_pos (by linarith) (by positivity)
  have ha_split : a ^ 2 = a ^ (alpha + 1) * a ^ (1 - alpha) := by
    rw [← Real.rpow_add ha, show alpha + 1 + (1 - alpha) = (2 : ℝ) by ring,
      Real.rpow_two]
  have ha_tail : a ^ (alpha + 1) * a ^ (-2 * alpha) = a ^ (1 - alpha) := by
    rw [← Real.rpow_add ha]
    congr 1; ring
  have henergy_factor : lambda * B ^ 2 * a ^ 2 = B * a ^ (1 - alpha) / 2 := by
    rw [ha_split]
    nlinarith [congrArg (fun z : ℝ => z * (B * a ^ (1 - alpha))) hscale]
  have hlambda_inv : (4 * lambda)⁻¹ = B * a ^ (alpha + 1) / 2 := by
    field_simp [hlambda.ne']
    nlinarith [hscale]
  have htail_factor : (4 * lambda)⁻¹ * (a ^ (-2 * alpha) / (2 * alpha)) =
      B * a ^ (1 - alpha) / (4 * alpha) := by
    rw [hlambda_inv]
    calc
      _ = B * (a ^ (alpha + 1) * a ^ (-2 * alpha)) / (4 * alpha) := by ring
      _ = _ := by rw [ha_tail]
  have hnormalized : lambda * delta + B * a ^ (1 - alpha) / (1 - alpha) -
        lambda * B ^ 2 * a ^ 2 / 2 +
        (4 * lambda)⁻¹ * (a ^ (-2 * alpha) / (2 * alpha)) =
      B * a ^ (1 - alpha) * q / (1 - alpha) := by
    rw [hdelta, htail_factor]
    have he : lambda * (B ^ 2 * a ^ 2 * ((alpha + 1) / (2 * alpha))) =
        B * a ^ (1 - alpha) / 2 * q := by
      change _ = _ * ((alpha + 1) / (2 * alpha))
      rw [← henergy_factor]
      ring
    rw [he, henergy_factor]
    dsimp only [q]
    field_simp
    ring
  rw [hnormalized]
  have hBpower : B ^ alpha * (B ^ 2) ^ beta = B := by
    rw [← Real.rpow_natCast B 2, ← Real.rpow_mul hB.le, ← Real.rpow_add hB]
    norm_num only [Nat.cast_ofNat]
    rw [show alpha + (2 : ℝ) * beta = 1 by dsimp [beta]; ring, Real.rpow_one]
  have hapower : (a ^ 2) ^ beta = a ^ (1 - alpha) := by
    rw [← Real.rpow_natCast a 2, ← Real.rpow_mul ha.le]
    congr 1
    dsimp only [beta]
    ring
  have hqpower : q ^ ((alpha + 1) / 2) * q ^ beta = q := by
    rw [← Real.rpow_add hq,
      show (alpha + 1) / 2 + beta = 1 by dsimp [beta]; ring, Real.rpow_one]
  have hdelta_power : delta ^ beta =
      (B ^ 2) ^ beta * (a ^ 2) ^ beta * q ^ beta := by
    rw [hdelta, Real.mul_rpow (by positivity) hq.le,
      Real.mul_rpow (sq_nonneg B) (sq_nonneg a)]
  change _ = ((1 - alpha)⁻¹ * q ^ ((alpha + 1) / 2)) * B ^ alpha * delta ^ beta
  rw [hdelta_power]
  calc
    B * a ^ (1 - alpha) * q / (1 - alpha) =
        (1 - alpha)⁻¹ * (B ^ alpha * (B ^ 2) ^ beta) *
          (a ^ 2) ^ beta * (q ^ ((alpha + 1) / 2) * q ^ beta) := by
      rw [hBpower, hapower, hqpower]
      ring
    _ = _ := by ring

/-- A sharp bound from an essential cap and an actual integrable weighted
quadratic energy. The Bochner integrability conclusion rules out default-zero
improper-integral readings. The constant is sharp for this abstract class. -/
theorem norm_integral_le_sharp_cap_energy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (w : ℝ → E) (alpha B delta : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) (hB : 0 ≤ B) (hdelta : 0 ≤ delta)
    (hw : AEStronglyMeasurable w (volume.restrict (Ioi (0 : ℝ))))
    (hcap : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), ‖w t‖ ≤ B)
    (henergy : IntegrableOn (fun t : ℝ => t * ‖w t‖ ^ 2) (Ioi 0))
    (hbudget : (∫ t in Ioi (0 : ℝ), t * ‖w t‖ ^ 2) ≤ delta) :
    IntegrableOn (fun t : ℝ => t ^ (-alpha) • w t) (Ioi 0) ∧
      ‖∫ t in Ioi (0 : ℝ), t ^ (-alpha) • w t‖ ≤
        sharpConstant alpha * B ^ alpha * delta ^ ((1 - alpha) / 2) := by
  have henergy_nonneg : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      0 ≤ t * ‖w t‖ ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg ht.le (sq_nonneg _)
  by_cases hB0 : B = 0
  · have hz : (fun t : ℝ => t ^ (-alpha) • w t) =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
      filter_upwards [hcap] with t ht
      have hwt : w t = 0 := norm_eq_zero.mp (le_antisymm (hB0 ▸ ht) (norm_nonneg _))
      simp only [hwt, smul_zero, Pi.zero_apply]
    refine ⟨(integrable_zero ℝ E (volume.restrict (Ioi (0 : ℝ)))).congr hz.symm, ?_⟩
    rw [integral_congr_ae hz]
    simp [hB0, Real.zero_rpow halpha0.ne']
  by_cases hdelta0 : delta = 0
  · have he0 : (∫ t in Ioi (0 : ℝ), t * ‖w t‖ ^ 2) = 0 :=
      le_antisymm (hdelta0 ▸ hbudget) (integral_nonneg_of_ae henergy_nonneg)
    have heAE := (integral_eq_zero_iff_of_nonneg_ae henergy_nonneg henergy).mp he0
    have hz : (fun t : ℝ => t ^ (-alpha) • w t) =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
      filter_upwards [heAE, ae_restrict_mem measurableSet_Ioi] with t hzt ht
      have hnorm : ‖w t‖ ^ 2 = 0 := (mul_eq_zero.mp hzt).resolve_left ht.ne'
      have hwt : w t = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
      simp only [hwt, smul_zero, Pi.zero_apply]
    refine ⟨(integrable_zero ℝ E (volume.restrict (Ioi (0 : ℝ)))).congr hz.symm, ?_⟩
    rw [integral_congr_ae hz]
    simp [hdelta0, Real.zero_rpow (by linarith : (1 - alpha) / 2 ≠ 0)]
  have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
  have hdpos : 0 < delta := lt_of_le_of_ne hdelta (Ne.symm hdelta0)
  let q : ℝ := (alpha + 1) / (2 * alpha)
  have hq : 0 < q := div_pos (by linarith) (by positivity)
  let a : ℝ := Real.sqrt (delta / (B ^ 2 * q))
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have ha2 : a ^ 2 = delta / (B ^ 2 * q) := Real.sq_sqrt (by positivity)
  have hdscale : delta = B ^ 2 * a ^ 2 * ((alpha + 1) / (2 * alpha)) := by
    change delta = B ^ 2 * a ^ 2 * q
    rw [ha2]
    field_simp [hBpos.ne', hq.ne'] <;> ring
  let lambda : ℝ := (2 * B * a ^ (alpha + 1))⁻¹
  have hlambda : 0 < lambda := by dsimp only [lambda]; positivity
  have hscale : 2 * lambda * B * a ^ (alpha + 1) = 1 := by
    dsimp only [lambda]
    field_simp [hBpos.ne', (Real.rpow_pos_of_pos ha (alpha + 1)).ne'] <;> ring
  obtain ⟨hi, hb⟩ := cutoff_bound w alpha B delta a lambda halpha0 halpha1
    hBpos ha hlambda hscale hw hcap henergy hbudget
  refine ⟨hi, ?_⟩
  rw [optimize_coefficient alpha B a lambda delta halpha0 halpha1 hBpos
    ha hlambda hscale hdscale] at hb
  exact hb

#print axioms norm_integral_le_sharp_cap_energy

end D5.S3.Analytic.Interpolation.CapWeightedEnergy
