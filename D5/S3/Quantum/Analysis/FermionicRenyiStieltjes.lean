/- GID: D5/S3/Quantum/Analysis/FermionicRenyiStieltjes
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/FermionicRenyiStieltjes
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Positive Stieltjes representation for the fermionic Gaussian Renyi function. -/

import D5.S3.Quantum.Analysis.BosonicRenyiStieltjes
import D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity

/-! The sum of two powers is obtained by dividing the difference of their squares
by their difference. Applying the bosonic representation at orders `2 * α` and `α`
therefore gives the fermionic representation, including the pure-mode endpoint. -/

namespace D5.S3.Quantum.Analysis.FermionicRenyiStieltjes

open Real Set MeasureTheory
open D5.S3.Entropy.RenyiCombining.BinaryRenyiCombining

noncomputable section

/-- Single-mode fermionic Gaussian Renyi entropy. -/
def fermionicRenyiFunction (α σ : ℝ) : ℝ :=
  hRenyi α ((1 + σ) / 2)

/-- Density of the positive logarithmic representation on `(0, 1)`. -/
def fermionicWeight (α u : ℝ) : ℝ :=
  (2 * α * Real.sin (Real.pi * α) * (1 - u ^ 2) ^ (α - 1)) /
    (Real.pi * (1 - α) * ((1 + u) ^ (2 * α) + (1 - u) ^ (2 * α) +
      2 * (1 - u ^ 2) ^ α * Real.cos (Real.pi * α)))

private lemma weight_denominator_pos {α u : ℝ} (ha0 : 0 < α) (ha1 : α < 1)
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    0 < (1 + u) ^ (2 * α) + (1 - u) ^ (2 * α) +
      2 * (1 - u ^ 2) ^ α * Real.cos (Real.pi * α) := by
  have hp : 0 < 1 + u := add_pos_of_pos_of_nonneg zero_lt_one hu0
  have hm : 0 < 1 - u := sub_pos.mpr hu1
  have hr : 1 - u ^ 2 = (1 + u) * (1 - u) := by
    simpa (config := { congrConsts := false }) only [one_pow] using sq_sub_sq (1 : ℝ) u
  have htwo : 2 * α = α * (2 : ℕ) := mul_comm _ _
  rw [htwo, Real.rpow_mul_natCast hp.le, Real.rpow_mul_natCast hm.le,
    hr, Real.mul_rpow hp.le hm.le]
  let a := (1 + u) ^ α
  let b := (1 - u) ^ α
  have hb : 0 < b := Real.rpow_pos_of_pos hm _
  have heq : a ^ 2 + b ^ 2 + 2 * (a * b) * Real.cos (Real.pi * α) =
      b ^ 2 * (1 - 2 * (-a / b) * Real.cos (Real.pi * α) + (-a / b) ^ 2) := by
    simpa (config := { congrConsts := false }) only [neg_sq, neg_mul, mul_neg, sub_neg_eq_add] using
      BosonicRenyiStieltjes.power_poisson_rescale (-a) b α hb.ne'
  change 0 < a ^ 2 + b ^ 2 + 2 * (a * b) * Real.cos (Real.pi * α)
  rw [heq]
  exact mul_pos (sq_pos_of_pos hb)
    (BosonicRenyiStieltjes.PoissonWeight.power_poisson_denominator_pos
      ha0 (by linarith) (ne_of_lt ha1))

/-- The fermionic density is strictly positive throughout `[0, 1)`. -/
theorem weight_pos {α u : ℝ} (ha0 : 0 < α) (ha1 : α < 1)
    (hu0 : 0 ≤ u) (hu1 : u < 1) : 0 < fermionicWeight α u := by
  have hs : 0 < Real.sin (Real.pi * α) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ha0)
      (by nlinarith [Real.pi_pos])
  have hu : 0 < 1 - u ^ 2 :=
    sub_pos.mpr ((sq_lt_one_iff_abs_lt_one u).mpr
      (by simpa (config := { congrConsts := false }) only [abs_of_nonneg hu0] using hu1))
  exact div_pos (mul_pos (mul_pos (mul_pos (by norm_num) ha0) hs)
    (Real.rpow_pos_of_pos hu _))
    (mul_pos (mul_pos Real.pi_pos (sub_pos.mpr ha1))
      (weight_denominator_pos ha0 ha1 hu0 hu1))

private def scaledWeight (β u : ℝ) : ℝ :=
  (β - 1) * BosonicRenyiStieltjes.renyiWeight β u

private lemma scaled_weight_formula (β u : ℝ) :
    scaledWeight β u =
      (-2 * β * Real.sin (Real.pi * β) * (1 - u ^ 2) ^ (β - 1)) /
        (Real.pi * ((1 + u) ^ (2 * β) + (1 - u) ^ (2 * β) -
          2 * (1 - u ^ 2) ^ β * Real.cos (Real.pi * β))) := by
  by_cases hb1 : β = 1
  · subst β
    simp (config := { congrConsts := false }) only
      [scaledWeight, sub_self, zero_mul, mul_one, Real.sin_pi, mul_zero, zero_div]
  · dsimp only [scaledWeight, BosonicRenyiStieltjes.renyiWeight]
    rw [← mul_div_assoc,
      show Real.pi * (β - 1) * ((1 + u) ^ (2 * β) + (1 - u) ^ (2 * β) -
          2 * (1 - u ^ 2) ^ β * Real.cos (Real.pi * β)) =
        (β - 1) * (Real.pi * ((1 + u) ^ (2 * β) + (1 - u) ^ (2 * β) -
          2 * (1 - u ^ 2) ^ β * Real.cos (Real.pi * β))) by ring]
    exact mul_div_mul_left _ _ (sub_ne_zero.mpr hb1)

private lemma weight_decomposition {α u : ℝ} (ha0 : 0 < α) (ha1 : α < 1)
    (hu : u ∈ Ioo 0 1) :
    fermionicWeight α u =
      (scaledWeight (2 * α) u - scaledWeight α u) / (1 - α) := by
  have hp : 0 < 1 + u := add_pos_of_pos_of_nonneg zero_lt_one hu.1.le
  have hm : 0 < 1 - u := sub_pos.mpr hu.2
  have hr : 0 < 1 - u ^ 2 :=
    sub_pos.mpr ((sq_lt_one_iff_abs_lt_one u).mpr
      (by simpa (config := { congrConsts := false }) only [abs_of_pos hu.1] using hu.2))
  have hprod : (1 - u ^ 2) ^ α = (1 + u) ^ α * (1 - u) ^ α := by
    rw [show 1 - u ^ 2 = (1 + u) * (1 - u) from
      by simpa (config := { congrConsts := false }) only
          [one_pow] using sq_sub_sq (1 : ℝ) u, Real.mul_rpow hp.le hm.le]
  have htwo (x : ℝ) (hx : 0 ≤ x) : x ^ (2 * α) = (x ^ α) ^ 2 := by
    rw [show 2 * α = α * (2 : ℕ) from mul_comm _ _, Real.rpow_mul_natCast hx]
  have hfour (x : ℝ) (hx : 0 ≤ x) : x ^ (2 * (2 * α)) = (x ^ α) ^ 4 := by
    rw [show 2 * (2 * α) = α * (4 : ℕ) by ring, Real.rpow_mul_natCast hx]
  have hsin : Real.sin (Real.pi * (2 * α)) =
      2 * Real.sin (Real.pi * α) * Real.cos (Real.pi * α) := by
    rw [show Real.pi * (2 * α) = 2 * (Real.pi * α) from mul_left_comm _ _ _, Real.sin_two_mul]
  have hcos : Real.cos (Real.pi * (2 * α)) = 2 * Real.cos (Real.pi * α) ^ 2 - 1 := by
    rw [show Real.pi * (2 * α) = 2 * (Real.pi * α) from mul_left_comm _ _ _, Real.cos_two_mul]
  have hdminus : 0 < ((1 + u) ^ α) ^ 2 + ((1 - u) ^ α) ^ 2 -
      2 * ((1 + u) ^ α * (1 - u) ^ α) * Real.cos (Real.pi * α) := by
    simpa (config := { congrConsts := false }) only [htwo _ hp.le, htwo _ hm.le, hprod] using
      BosonicRenyiStieltjes.weight_denominator_pos ha0 (by linarith)
        (ne_of_lt ha1) hu.1.le hu.2
  have hdplus := weight_denominator_pos ha0 ha1 hu.1.le hu.2
  rw [htwo _ hp.le, htwo _ hm.le, hprod] at hdplus
  have hdprod : ((1 + u) ^ α) ^ 4 + ((1 - u) ^ α) ^ 4 -
      2 * ((1 + u) ^ α * (1 - u) ^ α) ^ 2 *
        (2 * Real.cos (Real.pi * α) ^ 2 - 1) =
      (((1 + u) ^ α) ^ 2 + ((1 - u) ^ α) ^ 2 -
        2 * ((1 + u) ^ α * (1 - u) ^ α) * Real.cos (Real.pi * α)) *
      (((1 + u) ^ α) ^ 2 + ((1 - u) ^ α) ^ 2 +
        2 * ((1 + u) ^ α * (1 - u) ^ α) * Real.cos (Real.pi * α)) := by ring
  rw [scaled_weight_formula, scaled_weight_formula]
  dsimp only [fermionicWeight]
  rw [Real.rpow_sub_one hr.ne', Real.rpow_sub_one hr.ne']
  rw [htwo _ hp.le, htwo _ hm.le, hfour _ hp.le, hfour _ hm.le,
    htwo _ hr.le, hprod, hsin, hcos, hdprod]
  generalize (1 + u) ^ α = a at hdminus hdplus ⊢
  generalize (1 - u) ^ α = b at hdminus hdplus ⊢
  generalize Real.cos (Real.pi * α) = c at hdminus hdplus ⊢
  generalize Real.sin (Real.pi * α) = t
  have hdiff : (a ^ 2 + b ^ 2 + 2 * (a * b) * c) -
      (a ^ 2 + b ^ 2 - 2 * (a * b) * c) = 4 * a * b * c := by ring
  generalize a ^ 2 + b ^ 2 - 2 * (a * b) * c = d at hdminus hdiff ⊢
  generalize a ^ 2 + b ^ 2 + 2 * (a * b) * c = e at hdplus hdiff ⊢
  field_simp (disch := positivity)
  have hmul := congrArg (fun z : ℝ => t * a * b * z) hdiff
  nlinarith only [hmul]

private lemma scaled_weight_integrable {β : ℝ} (hb0 : 0 < β) (hb2 : β < 2) :
    IntegrableOn (scaledWeight β) (Ioo 0 1) := by
  have hscale (u : ℝ) : scaledWeight β u =
      (β - 1) * BosonicRenyiStieltjes.renyiWeight β u := scaledWeight.eq_1 β u
  by_cases hb1 : β = 1
  · subst β
    change IntegrableOn
      (fun u => (1 - 1 : ℝ) * BosonicRenyiStieltjes.renyiWeight 1 u) (Ioo 0 1)
    simpa (config := { congrConsts := false }) only
      [IntegrableOn, scaledWeight, sub_self, zero_mul] using
      (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioo 0 1))
  · have hi : IntegrableOn
        (fun u => (β - 1) * BosonicRenyiStieltjes.renyiWeight β u) (Ioo 0 1) :=
      (BosonicRenyiStieltjes.weight_integrable hb0 hb2 hb1).const_mul (β - 1)
    exact hi.congr_fun (fun u _ => (hscale u).symm) measurableSet_Ioo

/-- The fermionic density is integrable on `(0, 1)`. -/
theorem weight_integrable {α : ℝ} (ha0 : 0 < α) (ha1 : α < 1) :
    IntegrableOn (fermionicWeight α) (Ioo 0 1) := by
  have hi : IntegrableOn
      (fun u => (scaledWeight (2 * α) u - scaledWeight α u) / (1 - α)) (Ioo 0 1) :=
    ((scaled_weight_integrable (by linarith : 0 < 2 * α) (by linarith)).sub
      (scaled_weight_integrable ha0 (by linarith))).div_const (1 - α)
  apply hi.congr_fun _ measurableSet_Ioo
  intro u hu
  exact (weight_decomposition ha0 ha1 hu).symm

private lemma scaled_stieltjes {β s : ℝ} (hb0 : 0 < β) (hb2 : β < 2)
    (hs0 : 0 < s) (hs1 : s ≤ 1) :
    IntegrableOn (fun u => scaledWeight β u * Real.log (1 - u ^ 2 * s ^ 2))
      (Ioo 0 1) ∧
    Real.log (((1 + s) / 2) ^ β - ((1 - s) / 2) ^ β) =
      Real.log β + Real.log s - (β - 1) * Real.log 2 +
        ∫ u in Ioo (0 : ℝ) 1, scaledWeight β u * Real.log (1 - u ^ 2 * s ^ 2) := by
  by_cases hb1 : β = 1
  · subst β
    constructor
    · simpa (config := { congrConsts := false }) only [scaledWeight, sub_self, zero_mul] using
        (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioo 0 1))
    · simp (config := { congrConsts := false }) only
      [scaledWeight, sub_self, zero_mul, integral_zero, Real.rpow_one,
        Real.log_one, zero_add, sub_zero, add_zero]
      congr 1
      ring
  have hv : 1 ≤ s⁻¹ := (one_le_inv₀ hs0).mpr hs1
  obtain ⟨hi, he⟩ := BosonicRenyiStieltjes.stieltjes_representation hb0 hb2 hb1 hv
  have hn : IntegrableOn
      (fun u => BosonicRenyiStieltjes.renyiWeight β u * Real.log (1 - u ^ 2 * s ^ 2))
      (Ioo 0 1) ∧
      (∫ u in Ioo (0 : ℝ) 1,
        BosonicRenyiStieltjes.renyiWeight β u * Real.log (1 - u ^ 2 * s ^ 2)) =
        (∫ u in Ioo (0 : ℝ) 1,
          BosonicRenyiStieltjes.renyiWeight β u * Real.log ((s⁻¹) ^ 2 - u ^ 2)) -
            Real.log s⁻¹ := by
    rcases eq_or_lt_of_le hv with hv | hv
    · have hs : s = 1 := by
        apply inv_injective
        simpa (config := { congrConsts := false }) only [inv_one] using hv.symm
      subst s
      simpa (config := { congrConsts := false }) only
        [inv_one, one_pow, mul_one, Real.log_one, sub_zero] using
        (show IntegrableOn
          (fun u => BosonicRenyiStieltjes.renyiWeight β u * Real.log (1 - u ^ 2))
          (Ioo 0 1) ∧
          (∫ u in Ioo (0 : ℝ) 1,
            BosonicRenyiStieltjes.renyiWeight β u * Real.log (1 - u ^ 2)) =
          (∫ u in Ioo (0 : ℝ) 1,
            BosonicRenyiStieltjes.renyiWeight β u * Real.log (1 - u ^ 2)) from
          ⟨by simpa (config := { congrConsts := false }) only [inv_one, one_pow] using hi, rfl⟩)
    · simpa (config := { congrConsts := false }) only [div_inv_eq_mul, mul_pow] using
        (And.intro (BosonicRenyiStieltjes.normalized_log_integrable hb0 hb2 hb1 hv)
          (BosonicRenyiStieltjes.normalized_integral_eq hb0 hb2 hb1 hv))
  have hscaled :
      (∫ u in Ioo (0 : ℝ) 1, scaledWeight β u * Real.log (1 - u ^ 2 * s ^ 2)) =
      (β - 1) * (∫ u in Ioo (0 : ℝ) 1,
        BosonicRenyiStieltjes.renyiWeight β u * Real.log (1 - u ^ 2 * s ^ 2)) := by
    simp (config := { congrConsts := false }) only [scaledWeight, mul_assoc, integral_const_mul]
  constructor
  · simpa (config := { congrConsts := false }) only
    [IntegrableOn, scaledWeight, mul_assoc] using hn.1.const_mul (β - 1)
  · have hplus : (1 + s) / 2 = s * ((s⁻¹ + 1) / 2) := by
      field_simp (disch := positivity)
    have hminus : (1 - s) / 2 = s * ((s⁻¹ - 1) / 2) := by
      field_simp (disch := positivity)
    have hdiff : ((1 + s) / 2) ^ β - ((1 - s) / 2) ^ β =
        s ^ β * (((s⁻¹ + 1) / 2) ^ β - ((s⁻¹ - 1) / 2) ^ β) := by
      rw [hplus, hminus, Real.mul_rpow hs0.le (by positivity),
        Real.mul_rpow hs0.le (by linarith)]
      ring
    have hd := BosonicRenyiStieltjes.entropy_difference_pos hb0 hv
    rw [hdiff, Real.log_mul (Real.rpow_pos_of_pos hs0 β).ne' hd.ne',
      Real.log_rpow hs0, hscaled, hn.2]
    dsimp only [BosonicRenyiStieltjes.renyiFunction, BosonicRenyiStieltjes.renyiConstant] at he
    rw [Real.log_inv]
    have hc := congrArg (fun z : ℝ => (β - 1) * z) he
    simp (config := { congrConsts := false }) only [mul_add, mul_sub] at hc
    rw [mul_div_cancel₀ _ (sub_ne_zero.mpr hb1),
      mul_div_cancel₀ _ (sub_ne_zero.mpr hb1)] at hc
    nlinarith only [hc]

private lemma representation_pos {α s : ℝ} (ha0 : 0 < α) (ha1 : α < 1)
    (hs0 : 0 < s) (hs1 : s ≤ 1) :
    IntegrableOn (fun u => fermionicWeight α u * Real.log (1 - u ^ 2 * s ^ 2))
      (Ioo 0 1) ∧
    fermionicRenyiFunction α s = Real.log 2 +
      ∫ u in Ioo (0 : ℝ) 1, fermionicWeight α u * Real.log (1 - u ^ 2 * s ^ 2) := by
  obtain ⟨hi, he⟩ := scaled_stieltjes ha0 (by linarith) hs0 hs1
  obtain ⟨hi2, he2⟩ := scaled_stieltjes (by linarith : 0 < 2 * α) (by linarith) hs0 hs1
  have hfun (u : ℝ) (hu : u ∈ Ioo 0 1) :
      (scaledWeight (2 * α) u * Real.log (1 - u ^ 2 * s ^ 2) -
        scaledWeight α u * Real.log (1 - u ^ 2 * s ^ 2)) / (1 - α) =
      fermionicWeight α u * Real.log (1 - u ^ 2 * s ^ 2) := by
    rw [weight_decomposition ha0 ha1 hu]
    ring
  have hint :
      (∫ u in Ioo (0 : ℝ) 1, fermionicWeight α u * Real.log (1 - u ^ 2 * s ^ 2)) =
      ((∫ u in Ioo (0 : ℝ) 1, scaledWeight (2 * α) u * Real.log (1 - u ^ 2 * s ^ 2)) -
        (∫ u in Ioo (0 : ℝ) 1, scaledWeight α u * Real.log (1 - u ^ 2 * s ^ 2))) /
        (1 - α) := by
    rw [← integral_sub hi2 hi, ← integral_div]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro u hu
    exact (hfun u hu).symm
  constructor
  · have hi' : IntegrableOn
        (fun u => (scaledWeight (2 * α) u * Real.log (1 - u ^ 2 * s ^ 2) -
          scaledWeight α u * Real.log (1 - u ^ 2 * s ^ 2)) / (1 - α)) (Ioo 0 1) :=
      (hi2.sub hi).div_const (1 - α)
    exact hi'.congr_fun hfun measurableSet_Ioo
  · have hp : 0 < (1 + s) / 2 :=
      div_pos (add_pos_of_pos_of_nonneg zero_lt_one hs0.le) zero_lt_two
    have hm : 0 ≤ (1 - s) / 2 := div_nonneg (sub_nonneg.mpr hs1) zero_le_two
    have hd : 0 < ((1 + s) / 2) ^ α - ((1 - s) / 2) ^ α :=
      sub_pos.mpr (Real.rpow_lt_rpow hm (by linarith) ha0)
    have hsum : 0 < ((1 + s) / 2) ^ α + ((1 - s) / 2) ^ α := by
      simpa (config := { congrConsts := false }) only
        [show 1 - (1 - s) / 2 = (1 + s) / 2 by ring, add_comm] using
        (D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity.powerSum_pos
          (α := α) (p := (1 - s) / 2) ⟨hm, by linarith⟩)
    have htwo (x : ℝ) (hx : 0 ≤ x) : x ^ (2 * α) = (x ^ α) ^ 2 := by
      rw [show 2 * α = α * (2 : ℕ) from mul_comm _ _, Real.rpow_mul_natCast hx]
    rw [htwo _ hp.le, htwo _ hm,
      show (((1 + s) / 2) ^ α) ^ 2 - (((1 - s) / 2) ^ α) ^ 2 =
        (((1 + s) / 2) ^ α - ((1 - s) / 2) ^ α) *
          (((1 + s) / 2) ^ α + ((1 - s) / 2) ^ α) from
          (sq_sub_sq _ _).trans (mul_comm _ _),
      Real.log_mul hd.ne' hsum.ne', he, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ha0.ne'] at he2
    rw [fermionicRenyiFunction, hRenyi, one_div (1 - α),
      show 1 - (1 + s) / 2 = (1 - s) / 2 by ring, hint]
    have hlog : Real.log (((1 + s) / 2) ^ α + ((1 - s) / 2) ^ α) =
        (1 - α) * Real.log 2 +
          (∫ u in Ioo (0 : ℝ) 1, scaledWeight (2 * α) u * Real.log (1 - u ^ 2 * s ^ 2)) -
          (∫ u in Ioo (0 : ℝ) 1, scaledWeight α u * Real.log (1 - u ^ 2 * s ^ 2)) := by
      linarith
    rw [hlog]
    calc
      _ = (1 - α)⁻¹ * (1 - α) * Real.log 2 +
          (1 - α)⁻¹ *
            ((∫ u in Ioo (0 : ℝ) 1, scaledWeight (2 * α) u * Real.log (1 - u ^ 2 * s ^ 2)) -
              (∫ u in Ioo (0 : ℝ) 1,
                scaledWeight α u * Real.log (1 - u ^ 2 * s ^ 2))) := by ring
      _ = _ := by rw [inv_mul_cancel₀ (sub_pos.mpr ha1).ne']; ring

/-- Positive logarithmic Stieltjes representation, including both pure-mode endpoints. -/
theorem stieltjes_representation {α σ : ℝ} (ha0 : 0 < α) (ha1 : α < 1)
    (hs : |σ| ≤ 1) :
    IntegrableOn (fun u => fermionicWeight α u * Real.log (1 - u ^ 2 * σ ^ 2))
      (Ioo 0 1) ∧
    fermionicRenyiFunction α σ = Real.log 2 +
      ∫ u in Ioo (0 : ℝ) 1, fermionicWeight α u * Real.log (1 - u ^ 2 * σ ^ 2) := by
  by_cases hs0 : σ = 0
  · subst σ
    constructor
    · have hi : IntegrableOn (fun u => fermionicWeight α u * 0) (Ioo (0 : ℝ) 1) :=
        (weight_integrable ha0 ha1).mul_const 0
      simpa (config := { congrConsts := false }) only
        [zero_pow (by norm_num : 2 ≠ 0), mul_zero, sub_zero,
        Real.log_one, mul_zero] using hi
    · simpa (config := { congrConsts := false }) only [fermionicRenyiFunction,
        D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity.h,
        if_neg (ne_of_lt ha1), add_zero,
        zero_pow (by norm_num : 2 ≠ 0), mul_zero, sub_zero, Real.log_one,
        integral_zero] using
        (D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity.h_half ha0)
  · have hr := representation_pos ha0 ha1 (abs_pos.mpr hs0) hs
    have heven : fermionicRenyiFunction α |σ| = fermionicRenyiFunction α σ := by
      rcases le_or_gt 0 σ with hσ | hσ
      · rw [abs_of_nonneg hσ]
      · rw [abs_of_neg hσ]
        simp (config := { congrConsts := false }) only [fermionicRenyiFunction, hRenyi]
        rw [show 1 - (1 + -σ) / 2 = (1 + σ) / 2 by ring,
          show (1 + -σ) / 2 = 1 - (1 + σ) / 2 by ring, add_comm]
    simpa (config := { congrConsts := false }) only [sq_abs, heven] using hr

end

end D5.S3.Quantum.Analysis.FermionicRenyiStieltjes
