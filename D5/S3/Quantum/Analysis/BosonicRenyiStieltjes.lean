/- GID: D5/S3/Quantum/Analysis/BosonicRenyiStieltjes
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/BosonicRenyiStieltjes
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Positive Stieltjes representation for the bosonic Gaussian Renyi function. -/

import D5.S3.Arith.Robin.LogarithmicMellinReserve
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The scalar positive representation used in the Gaussian covariance entropy inequality.
The mass follows from an arctangent primitive after the substitutions
`q = (1 - x) / (1 + x)` and `p = q ^ α`. The logarithmic representation is obtained
by matching derivatives for `ν > 1`, fixing the constant at infinity, and extending to `ν = 1`
using integrability of the logarithmic endpoint singularity. -/

namespace D5.S3.Quantum.Analysis.BosonicRenyiStieltjes

open Real Set MeasureTheory Filter

noncomputable section

/-- Single-mode bosonic Gaussian Renyi entropy. -/
def renyiFunction (α ν : ℝ) : ℝ :=
  Real.log (((ν + 1) / 2) ^ α - ((ν - 1) / 2) ^ α) / (α - 1)

/-- Constant in the positive logarithmic representation. -/
def renyiConstant (α : ℝ) : ℝ := Real.log α / (α - 1) - Real.log 2

/-- Density of the positive logarithmic representation on `(0, 1)`. -/
def renyiWeight (α x : ℝ) : ℝ :=
  (-2 * α * Real.sin (Real.pi * α) * (1 - x ^ 2) ^ (α - 1)) /
    (Real.pi * (α - 1) * ((1 + x) ^ (2 * α) + (1 - x) ^ (2 * α) -
      2 * (1 - x ^ 2) ^ α * Real.cos (Real.pi * α)))

private def poissonAngle (α p : ℝ) : ℝ :=
  Real.arctan (p * Real.sin (Real.pi * α) / (1 - p * Real.cos (Real.pi * α)))

private def weightPrimitive (α x : ℝ) : ℝ :=
  poissonAngle α (((1 - x) / (1 + x)) ^ α) / (Real.pi * (α - 1))

private lemma sine_factor_pos {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2) (ha1 : α ≠ 1) :
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

private lemma cosine_lt_one {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2) (ha1 : α ≠ 1) :
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

private lemma weight_denominator_pos {α x : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    0 < (1 + x) ^ (2 * α) + (1 - x) ^ (2 * α) -
      2 * (1 - x ^ 2) ^ α * Real.cos (Real.pi * α) := by
  have hc := cosine_lt_one ha0 ha2 ha1
  have hp : 0 < 1 + x := by linarith
  have hm : 0 < 1 - x := by linarith
  have hr : 1 - x ^ 2 = (1 + x) * (1 - x) := by ring
  have htwo : 2 * α = α * (2 : ℕ) := by ring
  rw [htwo, Real.rpow_mul_natCast hp.le, Real.rpow_mul_natCast hm.le,
    hr, Real.mul_rpow hp.le hm.le]
  have hprod : 0 < (1 + x) ^ α * (1 - x) ^ α :=
    mul_pos (Real.rpow_pos_of_pos hp _) (Real.rpow_pos_of_pos hm _)
  nlinarith [sq_nonneg ((1 + x) ^ α - (1 - x) ^ α), mul_pos hprod (sub_pos.mpr hc)]

/-- The Stieltjes density is strictly positive throughout `[0, 1)`. -/
theorem weight_pos {α x : ℝ} (ha0 : 0 < α) (ha2 : α < 2) (ha1 : α ≠ 1)
    (hx0 : 0 ≤ x) (hx1 : x < 1) : 0 < renyiWeight α x := by
  have hs := sine_factor_pos ha0 ha2 ha1
  have hd := weight_denominator_pos ha0 ha2 ha1 hx0 hx1
  have hx : 0 < 1 - x ^ 2 := by nlinarith [sq_nonneg x]
  have heq : renyiWeight α x =
      (2 * α * (-Real.sin (Real.pi * α) / (α - 1)) * (1 - x ^ 2) ^ (α - 1)) /
        (Real.pi * ((1 + x) ^ (2 * α) + (1 - x) ^ (2 * α) -
          2 * (1 - x ^ 2) ^ α * Real.cos (Real.pi * α))) := by
    dsimp only [renyiWeight]
    field_simp [sub_ne_zero.mpr ha1, Real.pi_ne_zero, hd.ne']
  rw [heq]
  exact div_pos (mul_pos (mul_pos (mul_pos (by norm_num) ha0) hs)
    (Real.rpow_pos_of_pos hx _)) (mul_pos Real.pi_pos hd)

private lemma mobius_mem {x : ℝ} (hx : x ∈ Ioo 0 1) :
    (1 - x) / (1 + x) ∈ Ioo 0 1 := by
  have hp : 0 < 1 + x := by linarith [hx.1]
  exact ⟨div_pos (by linarith [hx.2]) hp,
    (div_lt_one hp).mpr (by linarith [hx.1])⟩

private lemma mobius_hasDerivAt {x : ℝ} (hx : x ∈ Ioo 0 1) :
    HasDerivAt (fun y : ℝ => (1 - y) / (1 + y)) (-2 / (1 + x) ^ 2) x := by
  have hp : 1 + x ≠ 0 := ne_of_gt (by linarith [hx.1])
  convert! ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).div
    ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)) hp using 1
  dsimp
  field_simp
  ring

private lemma power_substitution_hasDerivAt {α x : ℝ} (hx : x ∈ Ioo 0 1) :
    HasDerivAt (fun y : ℝ => ((1 - y) / (1 + y)) ^ α)
      (-2 * α * ((1 - x) / (1 + x)) ^ (α - 1) / (1 + x) ^ 2) x := by
  have hq := mobius_mem hx
  have hd := mobius_hasDerivAt hx
  convert hd.rpow_const (p := α) (Or.inl hq.1.ne') using 1
  ring

private lemma weight_substitution {α x : ℝ} (ha0 : 0 < α) (hx : x ∈ Ioo 0 1) :
    renyiWeight α x =
      (2 * α * Real.sin (Real.pi * α) * ((1 - x) / (1 + x)) ^ (α - 1)) /
        (Real.pi * (α - 1) * (1 + x) ^ 2 *
          (1 - 2 * ((1 - x) / (1 + x)) ^ α * Real.cos (Real.pi * α) +
            (((1 - x) / (1 + x)) ^ α) ^ 2)) * (-1) := by
  have hp : 0 < 1 + x := by linarith [hx.1]
  have hm : 0 < 1 - x := by linarith [hx.2]
  have hA := Real.rpow_pos_of_pos hp α
  have hB := Real.rpow_pos_of_pos hm α
  have hAB : (1 - x) ^ α < (1 + x) ^ α :=
    Real.rpow_lt_rpow hm.le (by linarith [hx.1]) ha0
  have hprod : 0 < (1 + x) ^ α * (1 - x) ^ α := mul_pos hA hB
  have hD : 0 < ((1 + x) ^ α) ^ 2 + ((1 - x) ^ α) ^ 2 -
      2 * (1 + x) ^ α * (1 - x) ^ α * Real.cos (Real.pi * α) := by
    nlinarith [sq_pos_of_pos (sub_pos.mpr hAB),
      mul_le_mul_of_nonneg_left (Real.cos_le_one (Real.pi * α)) hprod.le]
  have hq := mobius_mem hx
  have hp0 := Real.rpow_pos_of_pos hq.1 α
  have hp1 := Real.rpow_lt_one hq.1.le hq.2 ha0
  have hQ : 0 < 1 - 2 * ((1 - x) / (1 + x)) ^ α * Real.cos (Real.pi * α) +
      (((1 - x) / (1 + x)) ^ α) ^ 2 := by
    nlinarith [sq_pos_of_pos (sub_pos.mpr hp1),
      mul_le_mul_of_nonneg_left (Real.cos_le_one (Real.pi * α)) hp0.le]
  have hr : 1 - x ^ 2 = (1 + x) * (1 - x) := by ring
  have hr0 : 0 < 1 - x ^ 2 := by rw [hr]; exact mul_pos hp hm
  have htwo : 2 * α = α * (2 : ℕ) := by ring
  dsimp only [renyiWeight]
  rw [Real.rpow_sub_one hr0.ne', hr, Real.mul_rpow hp.le hm.le,
    htwo, Real.rpow_mul_natCast hp.le, Real.rpow_mul_natCast hm.le,
    Real.div_rpow hm.le hp.le, Real.rpow_sub_one hm.ne', Real.rpow_sub_one hp.ne',
    Real.div_rpow hm.le hp.le]
  rw [Real.div_rpow hm.le hp.le] at hQ
  by_cases ha1 : α = 1
  · subst α
    norm_num [Real.sin_pi]
  · field_simp [hp.ne', hm.ne', hA.ne', hB.ne', hD.ne', hQ.ne', sub_ne_zero.mpr ha1]
    ring

private lemma poissonAngle_hasDerivAt {α p : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hp : p ∈ Ioo 0 1) :
    HasDerivAt (poissonAngle α)
      (Real.sin (Real.pi * α) /
        (1 - 2 * p * Real.cos (Real.pi * α) + p ^ 2)) p := by
  have hc := cosine_lt_one ha0 ha2 ha1
  have hden : 0 < 1 - p * Real.cos (Real.pi * α) := by
    have hpc := mul_lt_mul_of_pos_left hc hp.1
    nlinarith [hp.2]
  have hd := ((hasDerivAt_id p).mul_const (Real.sin (Real.pi * α))).div
    ((hasDerivAt_const p (1 : ℝ)).sub
      ((hasDerivAt_id p).mul_const (Real.cos (Real.pi * α)))) hden.ne'
  have hk : 0 < 1 - 2 * p * Real.cos (Real.pi * α) + p ^ 2 := by
    nlinarith [sq_nonneg (1 - p), mul_pos hp.1 (sub_pos.mpr hc)]
  unfold poissonAngle
  convert! hd.arctan using 1
  dsimp
  field_simp
  have hid : (1 - p * Real.cos (Real.pi * α)) ^ 2 +
      Real.sin (Real.pi * α) ^ 2 * p ^ 2 = 1 - 2 * p * Real.cos (Real.pi * α) + p ^ 2 := by
    nlinarith [congrArg (fun z : ℝ => p ^ 2 * z) (Real.sin_sq_add_cos_sq (Real.pi * α))]
  rw [hid]
  ring

private lemma weightPrimitive_continuousOn {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) : ContinuousOn (weightPrimitive α) (Icc 0 1) := by
  have hc := cosine_lt_one ha0 ha2 ha1
  intro x hx
  have hp : 0 < 1 + x := by linarith [hx.1]
  have hq0 : 0 ≤ (1 - x) / (1 + x) := div_nonneg (by linarith [hx.2]) hp.le
  have hq1 : (1 - x) / (1 + x) ≤ 1 := (div_le_one hp).mpr (by linarith [hx.1])
  have hr0 := Real.rpow_nonneg hq0 α
  have hr1 : ((1 - x) / (1 + x)) ^ α ≤ 1 :=
    Real.rpow_le_one hq0 hq1 ha0.le
  have hden : 1 - ((1 - x) / (1 + x)) ^ α * Real.cos (Real.pi * α) ≠ 0 := by
    have hmul := mul_le_mul_of_nonneg_left hc.le hr0
    by_cases hr : ((1 - x) / (1 + x)) ^ α = 0
    · rw [hr, zero_mul, sub_zero]
      exact one_ne_zero
    · have hpos := lt_of_le_of_ne hr0 (Ne.symm hr)
      have hlt := mul_lt_mul_of_pos_left hc hpos
      linarith
  have hq : ContinuousAt (fun y : ℝ => (1 - y) / (1 + y)) x :=
    (continuousAt_const.sub continuousAt_id).div
      (continuousAt_const.add continuousAt_id) hp.ne'
  have hr := hq.rpow_const (Or.inr ha0.le)
  have hfrac := (hr.mul_const (Real.sin (Real.pi * α))).div
    (continuousAt_const.sub (hr.mul_const (Real.cos (Real.pi * α)))) hden
  exact ((Real.continuousAt_arctan.comp hfrac).div_const
    (Real.pi * (α - 1))).continuousWithinAt

private lemma weightPrimitive_hasDerivAt {α x : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hx : x ∈ Ioo 0 1) :
    HasDerivAt (weightPrimitive α) (renyiWeight α x) x := by
  have hp := power_substitution_hasDerivAt (α := α) hx
  have hq := mobius_mem hx
  have hangle := fun p (hp : p ∈ Ioo (0 : ℝ) 1) =>
    poissonAngle_hasDerivAt ha0 ha2 ha1 hp
  have hw := weight_substitution ha0 hx
  have hpr : ((1 - x) / (1 + x)) ^ α ∈ Ioo (0 : ℝ) 1 :=
    ⟨Real.rpow_pos_of_pos hq.1 _, Real.rpow_lt_one hq.1.le hq.2 ha0⟩
  have hd := ((hangle _ hpr).comp x hp).div_const (Real.pi * (α - 1))
  change HasDerivAt (fun y => poissonAngle α (((1 - y) / (1 + y)) ^ α) /
    (Real.pi * (α - 1))) _ x
  convert! hd using 1
  rw [hw]
  field_simp

private lemma weightPrimitive_endpoints {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) : weightPrimitive α 1 - weightPrimitive α 0 = 1 / 2 := by
  have hs : 0 < Real.sin (Real.pi * α / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos])
  have hsin : Real.sin (Real.pi * α) =
      2 * Real.sin (Real.pi * α / 2) * Real.cos (Real.pi * α / 2) := by
    convert Real.sin_two_mul (Real.pi * α / 2) using 1
    congr 1
    ring
  have hcos : Real.cos (Real.pi * α) = 1 - 2 * Real.sin (Real.pi * α / 2) ^ 2 := by
    convert Real.cos_two_mul_eq_one_sub (Real.pi * α / 2) using 1
    congr 1
    ring
  have ht : Real.tan (Real.pi / 2 - Real.pi * α / 2) =
      Real.sin (Real.pi * α) / (1 - Real.cos (Real.pi * α)) := by
    rw [Real.tan_eq_sin_div_cos, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub,
      hsin, hcos]
    field_simp [hs.ne']
    ring
  have hat : Real.arctan (Real.sin (Real.pi * α) / (1 - Real.cos (Real.pi * α))) =
      Real.pi / 2 - Real.pi * α / 2 := by
    rw [← ht]
    exact Real.arctan_tan (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  dsimp only [weightPrimitive, poissonAngle]
  norm_num [Real.zero_rpow ha0.ne', Real.one_rpow, Real.arctan_zero]
  rw [hat]
  field_simp [sub_ne_zero.mpr ha1, Real.pi_ne_zero]
  ring

/-- The endpoint singularity of the positive density is integrable. -/
theorem weight_integrable {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2) (ha1 : α ≠ 1) :
    IntegrableOn (renyiWeight α) (Ioo 0 1) := by
  have hc := weightPrimitive_continuousOn ha0 ha2 ha1
  have hd := fun x (hx : x ∈ Ioo (0 : ℝ) 1) =>
    weightPrimitive_hasDerivAt ha0 ha2 ha1 hx
  have hp := fun x (hx : x ∈ Ioo (0 : ℝ) 1) =>
    (weight_pos ha0 ha2 ha1 hx.1.le hx.2).le
  exact (intervalIntegral.integrableOn_deriv_of_nonneg hc hd hp).mono_set Ioo_subset_Ioc_self

/-- Every order in the stated range gives a density of mass one half. -/
theorem weight_mass {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2) (ha1 : α ≠ 1) :
    ∫ x in Ioo (0 : ℝ) 1, renyiWeight α x = 1 / 2 := by
  have hi := weight_integrable ha0 ha2 ha1
  have hc := weightPrimitive_continuousOn ha0 ha2 ha1
  have hd := fun x (hx : x ∈ Ioo (0 : ℝ) 1) =>
    weightPrimitive_hasDerivAt ha0 ha2 ha1 hx
  have he := weightPrimitive_endpoints ha0 ha2 ha1
  have hioc : IntegrableOn (renyiWeight α) (Ioc 0 1) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo).mpr hi
  have hint := (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by norm_num : (0 : ℝ) ≤ 1)).mpr hioc
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num)]
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hc hd hint).trans he

private def weightFactor (α x : ℝ) : ℝ :=
  (-2 * α * Real.sin (Real.pi * α) * (1 + x) ^ (α - 1)) /
    (Real.pi * (α - 1) * ((1 + x) ^ (2 * α) + (1 - x) ^ (2 * α) -
      2 * (1 - x ^ 2) ^ α * Real.cos (Real.pi * α)))

private lemma weight_factorization {α x : ℝ} (hx : x ∈ Ioo 0 1) :
    renyiWeight α x = weightFactor α x * (1 - x) ^ (α - 1) := by
  have hp : 0 < 1 + x := by linarith [hx.1]
  have hm : 0 < 1 - x := by linarith [hx.2]
  have hr : 1 - x ^ 2 = (1 + x) * (1 - x) := by ring
  dsimp only [renyiWeight, weightFactor]
  rw [hr, Real.mul_rpow hp.le hm.le]
  ring

private lemma weightFactor_continuousOn {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) : ContinuousOn (weightFactor α) (Icc 0 1) := by
  intro x hx
  have hp : 0 < 1 + x := by linarith [hx.1]
  have hden : (1 + x) ^ (2 * α) + (1 - x) ^ (2 * α) -
      2 * (1 - x ^ 2) ^ α * Real.cos (Real.pi * α) ≠ 0 := by
    rcases eq_or_lt_of_le hx.2 with hx1 | hx1
    · subst x
      norm_num [Real.zero_rpow (by linarith : 2 * α ≠ 0), Real.zero_rpow ha0.ne']
      positivity
    · exact (weight_denominator_pos ha0 ha2 ha1 hx.1 hx1).ne'
  have hpow : ContinuousAt (fun y : ℝ => (1 + y) ^ (α - 1)) x :=
    (continuousAt_const.add continuousAt_id).rpow_const (Or.inl hp.ne')
  have hA : ContinuousAt (fun y : ℝ => (1 + y) ^ (2 * α)) x :=
    (continuousAt_const.add continuousAt_id).rpow_const (Or.inr (by linarith))
  have hB : ContinuousAt (fun y : ℝ => (1 - y) ^ (2 * α)) x :=
    (continuousAt_const.sub continuousAt_id).rpow_const (Or.inr (by linarith))
  have hC : ContinuousAt (fun y : ℝ => (1 - y ^ 2) ^ α) x :=
    (continuousAt_const.sub (continuousAt_id.pow 2)).rpow_const (Or.inr ha0.le)
  have hc := (hA.add hB).sub ((hC.const_mul 2).mul_const
    (Real.cos (Real.pi * α)))
  exact ((hpow.const_mul (-2 * α * Real.sin (Real.pi * α))).div
    (hc.const_mul (Real.pi * (α - 1))) (mul_ne_zero (mul_ne_zero Real.pi_ne_zero
      (sub_ne_zero.mpr ha1)) hden)).continuousWithinAt

private lemma logarithmic_integrable_at_one {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) :
    IntegrableOn (fun x => renyiWeight α x * Real.log (1 - x ^ 2)) (Ioo 0 1) := by
  have hlow := D5.S3.Arith.Robin.LogarithmicMellinReserve.low_log_integrable ha0
  have hlowI := (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by norm_num : (0 : ℝ) ≤ 1)).mpr hlow
  have hreflect := (hlowI.comp_sub_left 1).symm
  have hreflect' : IntegrableOn
      (fun x : ℝ => -Real.log (1 - x) * (1 - x) ^ (α - 1)) (Ioo 0 1) := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mp
    simpa only [sub_zero, sub_self] using hreflect
  have hc := weightFactor_continuousOn ha0 ha2 ha1
  have hlog : IntegrableOn (fun x : ℝ => renyiWeight α x * Real.log (1 - x))
      (Ioo 0 1) := by
    have hi := hreflect'.neg.mul_continuousOn_of_subset hc measurableSet_Ioo
      isCompact_Icc Ioo_subset_Icc_self
    apply hi.congr_fun _ measurableSet_Ioo
    intro x hx
    change -(-Real.log (1 - x) * (1 - x) ^ (α - 1)) * weightFactor α x =
      renyiWeight α x * Real.log (1 - x)
    rw [weight_factorization hx]
    ring
  have hcplus : ContinuousOn (fun x : ℝ => Real.log (1 + x)) (Icc 0 1) := by
    intro x hx
    exact ((continuousAt_const.add continuousAt_id).log
      (ne_of_gt (by linarith [hx.1] : 0 < 1 + x))).continuousWithinAt
  have hi := hlog.add ((weight_integrable ha0 ha2 ha1).mul_continuousOn_of_subset
    hcplus measurableSet_Ioo isCompact_Icc Ioo_subset_Icc_self)
  apply hi.congr_fun _ measurableSet_Ioo
  intro x hx
  have hp : 0 < 1 + x := by linarith [hx.1]
  have hm : 0 < 1 - x := by linarith [hx.2]
  change renyiWeight α x * Real.log (1 - x) + renyiWeight α x * Real.log (1 + x) =
    renyiWeight α x * Real.log (1 - x ^ 2)
  rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring,
    Real.log_mul hm.ne' hp.ne']
  ring

private lemma logarithmic_integrable {α ν : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hv : 1 ≤ ν) :
    IntegrableOn (fun x => renyiWeight α x * Real.log (ν ^ 2 - x ^ 2)) (Ioo 0 1) := by
  rcases eq_or_lt_of_le hv with hv | hv
  · subst ν
    simpa only [one_pow] using logarithmic_integrable_at_one ha0 ha2 ha1
  · have hc : ContinuousOn (fun x : ℝ => Real.log (ν ^ 2 - x ^ 2)) (Icc 0 1) := by
      intro x hx
      have hp : 0 < ν ^ 2 - x ^ 2 := by nlinarith [sq_nonneg x, hx.1, hx.2]
      exact ((continuousAt_const.sub (continuousAt_id.pow 2)).log hp.ne').continuousWithinAt
    exact (weight_integrable ha0 ha2 ha1).mul_continuousOn_of_subset hc
      measurableSet_Ioo isCompact_Icc Ioo_subset_Icc_self

private lemma logarithmic_derivative {α ν : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hv : 1 < ν) :
    HasDerivAt (fun v => ∫ x in Ioo (0 : ℝ) 1,
      renyiWeight α x * Real.log (v ^ 2 - x ^ 2))
      (∫ x in Ioo (0 : ℝ) 1, renyiWeight α x * (2 * ν / (ν ^ 2 - x ^ 2))) ν := by
  sorry

private lemma entropy_difference_pos {α ν : ℝ} (ha0 : 0 < α) (hv : 1 ≤ ν) :
    0 < ((ν + 1) / 2) ^ α - ((ν - 1) / 2) ^ α := by
  exact sub_pos.mpr (Real.rpow_lt_rpow (by linarith) (by linarith) ha0)

private lemma renyiFunction_derivative {α ν : ℝ} (ha0 : 0 < α)
    (ha1 : α ≠ 1) (hv : 1 < ν) :
    HasDerivAt (renyiFunction α)
      (α * (((ν + 1) / 2) ^ (α - 1) - ((ν - 1) / 2) ^ (α - 1)) /
        (2 * (α - 1) * (((ν + 1) / 2) ^ α - ((ν - 1) / 2) ^ α))) ν := by
  have hp : 0 < (ν + 1) / 2 := by linarith
  have hm : 0 < (ν - 1) / 2 := by linarith
  have hdA := (((hasDerivAt_id ν).add_const 1).div_const 2).rpow_const
    (p := α) (Or.inl hp.ne')
  have hdB := (((hasDerivAt_id ν).sub_const 1).div_const 2).rpow_const
    (p := α) (Or.inl hm.ne')
  have hpos := entropy_difference_pos ha0 hv.le
  have hd := ((hdA.sub hdB).log hpos.ne').div_const (α - 1)
  unfold renyiFunction
  convert! hd using 1
  dsimp
  field_simp

private lemma resolvent_integral {α ν : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hv : 1 < ν) :
    (∫ x in Ioo (0 : ℝ) 1, renyiWeight α x * (2 * ν / (ν ^ 2 - x ^ 2))) =
      α * (((ν + 1) / 2) ^ (α - 1) - ((ν - 1) / 2) ^ (α - 1)) /
        (2 * (α - 1) * (((ν + 1) / 2) ^ α - ((ν - 1) / 2) ^ α)) := by
  sorry

private lemma renyiFunction_hasDerivAt {α ν : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hv : 1 < ν) :
    HasDerivAt (renyiFunction α)
      (∫ x in Ioo (0 : ℝ) 1, renyiWeight α x * (2 * ν / (ν ^ 2 - x ^ 2))) ν := by
  rw [resolvent_integral ha0 ha2 ha1 hv]
  exact renyiFunction_derivative ha0 ha1 hv

private lemma representation_atTop {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) :
    Tendsto (fun ν => renyiFunction α ν -
      ∫ x in Ioo (0 : ℝ) 1, renyiWeight α x * Real.log (ν ^ 2 - x ^ 2))
      atTop (nhds (renyiConstant α)) := by
  have hm := weight_mass ha0 ha2 ha1
  sorry

private lemma representation_of_one_lt {α ν : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hv : 1 < ν) :
    renyiFunction α ν = renyiConstant α +
      ∫ x in Ioo (0 : ℝ) 1, renyiWeight α x * Real.log (ν ^ 2 - x ^ 2) := by
  have hd := fun v (hv : 1 < v) => logarithmic_derivative ha0 ha2 ha1 hv
  have hs := fun v (hv : 1 < v) => renyiFunction_hasDerivAt ha0 ha2 ha1 hv
  have ht := representation_atTop ha0 ha2 ha1
  let f := fun v => renyiFunction α v -
    ∫ x in Ioo (0 : ℝ) 1, renyiWeight α x * Real.log (v ^ 2 - x ^ 2)
  have hz (v : ℝ) (hv : 1 < v) : HasDerivAt f 0 v := by
    dsimp only [f]
    convert! (hs v hv).sub (hd v hv) using 1
    simp only [sub_self]
  have heq (v : ℝ) (hv' : 1 < v) : f v = f ν :=
    isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi (1 : ℝ)).isPreconnected
      (fun v hv => (hz v hv).differentiableAt.differentiableWithinAt)
      (fun v hv => (hz v hv).deriv) hv' hv
  have hlim : Tendsto f atTop (nhds (f ν)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with v hv
    exact (heq v hv).symm
  have hc : f ν = renyiConstant α := tendsto_nhds_unique hlim ht
  dsimp only [f] at hc
  linarith

private lemma representation_at_one {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) :
    renyiFunction α 1 = renyiConstant α +
      ∫ x in Ioo (0 : ℝ) 1, renyiWeight α x * Real.log (1 ^ 2 - x ^ 2) := by
  have hr := fun v (hv : 1 < v) => representation_of_one_lt ha0 ha2 ha1 hv
  have hi := logarithmic_integrable ha0 ha2 ha1 (ν := 1) le_rfl
  sorry

/-- Positive logarithmic Stieltjes representation, including the pure-mode endpoint. -/
theorem stieltjes_representation {α ν : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hv : 1 ≤ ν) :
    IntegrableOn (fun x => renyiWeight α x * Real.log (ν ^ 2 - x ^ 2)) (Ioo 0 1) ∧
      renyiFunction α ν = renyiConstant α +
        ∫ x in Ioo (0 : ℝ) 1, renyiWeight α x * Real.log (ν ^ 2 - x ^ 2) := by
  refine ⟨logarithmic_integrable ha0 ha2 ha1 hv, ?_⟩
  rcases eq_or_lt_of_le hv with hv | hv
  · subst ν
    exact representation_at_one ha0 ha2 ha1
  · exact representation_of_one_lt ha0 ha2 ha1 hv

/-- The scalar input to the Gaussian covariance entropy settlement. -/
theorem result {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2) (ha1 : α ≠ 1) :
    (∀ x ∈ Ico (0 : ℝ) 1, 0 < renyiWeight α x) ∧
      IntegrableOn (renyiWeight α) (Ioo 0 1) ∧
      (∫ x in Ioo (0 : ℝ) 1, renyiWeight α x) = 1 / 2 ∧
      ∀ ν, 1 ≤ ν →
        IntegrableOn (fun x => renyiWeight α x * Real.log (ν ^ 2 - x ^ 2)) (Ioo 0 1) ∧
          renyiFunction α ν = renyiConstant α +
            ∫ x in Ioo (0 : ℝ) 1, renyiWeight α x * Real.log (ν ^ 2 - x ^ 2) := by
  exact ⟨fun x hx => weight_pos ha0 ha2 ha1 hx.1 hx.2,
    weight_integrable ha0 ha2 ha1, weight_mass ha0 ha2 ha1,
    fun ν hv => stieltjes_representation ha0 ha2 ha1 hv⟩

end

end D5.S3.Quantum.Analysis.BosonicRenyiStieltjes
