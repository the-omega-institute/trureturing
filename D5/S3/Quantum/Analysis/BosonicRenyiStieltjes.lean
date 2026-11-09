/- GID: D5/S3/Quantum/Analysis/BosonicRenyiStieltjes
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/BosonicRenyiStieltjes
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Positive Stieltjes representation for the bosonic Gaussian Renyi function. -/

import D5.S3.Arith.Robin.LogarithmicMellinReserve
import D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight

/-! The scalar positive representation used in the Gaussian covariance entropy inequality.
The mass follows from an arctangent primitive after the substitutions
`q = (1 - x) / (1 + x)` and `p = q ^ α`. The logarithmic representation is obtained
by matching derivatives for `ν > 1`, fixing the constant at infinity, and extending to `ν = 1`
using integrability of the logarithmic endpoint singularity. -/

namespace D5.S3.Quantum.Analysis.BosonicRenyiStieltjes

open Real Set MeasureTheory Filter PoissonWeight

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

private lemma weight_denominator_pos {α x : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    0 < (1 + x) ^ (2 * α) + (1 - x) ^ (2 * α) -
      2 * (1 - x ^ 2) ^ α * Real.cos (Real.pi * α) := by
  have hp : 0 < 1 + x := by linarith
  have hm : 0 < 1 - x := by linarith
  have hr : 1 - x ^ 2 = (1 + x) * (1 - x) := by ring
  have htwo : 2 * α = α * (2 : ℕ) := by ring
  rw [htwo, Real.rpow_mul_natCast hp.le, Real.rpow_mul_natCast hm.le,
    hr, Real.mul_rpow hp.le hm.le]
  let a := (1 + x) ^ α
  let b := (1 - x) ^ α
  have hb : 0 < b := Real.rpow_pos_of_pos hm _
  have heq : a ^ 2 + b ^ 2 - 2 * (a * b) * Real.cos (Real.pi * α) =
      b ^ 2 * (1 - 2 * (a / b) * Real.cos (Real.pi * α) + (a / b) ^ 2) := by
    field_simp
    ring
  change 0 < a ^ 2 + b ^ 2 - 2 * (a * b) * Real.cos (Real.pi * α)
  rw [heq]
  exact mul_pos (sq_pos_of_pos hb)
    (PoissonWeight.power_poisson_denominator_pos
      ha0 ha2 ha1)

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
    field_simp (disch := first | positivity | assumption | exact sub_ne_zero.mpr ha1)
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
  field_simp (disch := first | positivity | assumption)
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
  · field_simp (disch := first | positivity | assumption | exact sub_ne_zero.mpr ha1)
    ring

private def poissonDensity (α p : ℝ) : ℝ :=
  -Real.sin (Real.pi * α) /
    (Real.pi * (α - 1) * (1 - 2 * p * Real.cos (Real.pi * α) + p ^ 2))

private lemma power_substitution_integral {α : ℝ} (ha0 : 0 < α) (g : ℝ → ℝ) :
    (∫ x in Ioo (0 : ℝ) 1, renyiWeight α x * g x) =
      ∫ p in Ioo (0 : ℝ) 1, poissonDensity α p *
        g ((1 - p ^ α⁻¹) / (1 + p ^ α⁻¹)) := by
  let f := fun x : ℝ => ((1 - x) / (1 + x)) ^ α
  let f' := fun x : ℝ => -2 * α * ((1 - x) / (1 + x)) ^ (α - 1) / (1 + x) ^ 2
  let G := fun p : ℝ => poissonDensity α p * g ((1 - p ^ α⁻¹) / (1 + p ^ α⁻¹))
  have hf : ContinuousOn f (uIcc 0 1) := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    intro x hx
    have hp : 0 < 1 + x := by linarith [hx.1]
    exact (((continuousAt_const.sub continuousAt_id).div
      (continuousAt_const.add continuousAt_id) hp.ne').rpow_const
        (Or.inr ha0.le)).continuousWithinAt
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' x) x :=
    fun x hx => power_substitution_hasDerivAt (α := α) hx
  have hn : ∀ x ∈ Ioo (0 : ℝ) 1, f' x ≤ 0 := by
    intro x hx
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by nlinarith : -2 * α ≤ 0)
        (Real.rpow_nonneg (mobius_mem hx).1.le _)) (sq_nonneg _)
  have hs := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (a := 0) (b := 1) (g := G) hf
    (by simpa only [min_eq_left zero_le_one, max_eq_right zero_le_one] using hd)
    (by simpa only [min_eq_left zero_le_one, max_eq_right zero_le_one] using hn)
  have hzero : f 0 = 1 := by norm_num [f]
  have hone : f 1 = 0 := by norm_num [f, Real.zero_rpow ha0.ne']
  rw [hzero, hone, intervalIntegral.integral_symm (a := 0) (b := 1)] at hs
  have hleft : (∫ x in (0 : ℝ)..1, (G ∘ f) x * f' x) =
      -(∫ x in (0 : ℝ)..1, renyiWeight α x * g x) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro x hx
    have hq := mobius_mem hx
    have hback : (1 - (f x) ^ α⁻¹) / (1 + (f x) ^ α⁻¹) = x := by
      dsimp only [f]
      rw [Real.rpow_rpow_inv hq.1.le ha0.ne']
      have hp : 1 + x ≠ 0 := ne_of_gt (by linarith [hx.1])
      field_simp (disch := first | positivity | assumption | simp only [hp])
      ring
    change poissonDensity α (f x) * g ((1 - (f x) ^ α⁻¹) / (1 + (f x) ^ α⁻¹)) *
      f' x = -(renyiWeight α x * g x)
    rw [hback, weight_substitution ha0 hx]
    dsimp only [f, f', poissonDensity]
    field_simp (disch := first | positivity | assumption)
  rw [hleft] at hs
  have heq := neg_injective hs
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo] using heq

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
  have hk :=
    PoissonWeight.power_poisson_denominator_pos
      (r := p) ha0 ha2 ha1
  unfold poissonAngle
  convert! hd.arctan using 1
  dsimp
  field_simp (disch := first | positivity | assumption)
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
  field_simp (disch := first | positivity | assumption)

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
    apply (div_eq_div_iff hs.ne' (by nlinarith [sq_pos_of_pos hs])).mpr
    ring
  have hat : Real.arctan (Real.sin (Real.pi * α) / (1 - Real.cos (Real.pi * α))) =
      Real.pi / 2 - Real.pi * α / 2 := by
    rw [← ht]
    exact Real.arctan_tan (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  dsimp only [weightPrimitive, poissonAngle]
  norm_num [Real.zero_rpow ha0.ne', Real.one_rpow, Real.arctan_zero]
  rw [hat]
  field_simp (disch := first | positivity | assumption | exact sub_ne_zero.mpr ha1)
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

private lemma resolvent_integrable {α ν : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hv : 1 < ν) :
    IntegrableOn (fun x => renyiWeight α x * (2 * ν / (ν ^ 2 - x ^ 2))) (Ioo 0 1) := by
  have hc : ContinuousOn (fun x : ℝ => 2 * ν / (ν ^ 2 - x ^ 2)) (Icc 0 1) := by
    intro x hx
    have hp : 0 < ν ^ 2 - x ^ 2 := by nlinarith [hx.1, hx.2]
    exact (continuousAt_const.div (continuousAt_const.sub (continuousAt_id.pow 2))
      hp.ne').continuousWithinAt
  exact (weight_integrable ha0 ha2 ha1).mul_continuousOn_of_subset hc
    measurableSet_Ioo isCompact_Icc Ioo_subset_Icc_self

private lemma logarithmic_derivative {α ν : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hv : 1 < ν) :
    HasDerivAt (fun v => ∫ x in Ioo (0 : ℝ) 1,
      renyiWeight α x * Real.log (v ^ 2 - x ^ 2))
      (∫ x in Ioo (0 : ℝ) 1, renyiWeight α x * (2 * ν / (ν ^ 2 - x ^ 2))) ν := by
  let a : ℝ := (ν + 1) / 2
  let b : ℝ := ν + 1
  let C : ℝ := 2 * b / (a ^ 2 - 1)
  have ha : 1 < a := by dsimp only [a]; linarith
  have han : a < ν := by dsimp only [a]; linarith
  have hb : ν < b := by dsimp only [b]; linarith
  have hCden : 0 < a ^ 2 - 1 := by nlinarith
  have hmeas : ∀ᶠ v in nhds ν, AEStronglyMeasurable
      (fun x => renyiWeight α x * Real.log (v ^ 2 - x ^ 2))
      (volume.restrict (Ioo 0 1)) := by
    filter_upwards [lt_mem_nhds hv] with v hv'
    exact (logarithmic_integrable ha0 ha2 ha1 hv'.le).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1), ∀ v ∈ Ioo a b,
      ‖renyiWeight α x * (2 * v / (v ^ 2 - x ^ 2))‖ ≤ renyiWeight α x * C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    intro v hv'
    have hw := (weight_pos ha0 ha2 ha1 hx.1.le hx.2).le
    have hv1 : 1 < v := ha.trans hv'.1
    have hden : a ^ 2 - 1 ≤ v ^ 2 - x ^ 2 := by nlinarith [hx.1, hx.2, hv'.1]
    have hpos : 0 < v ^ 2 - x ^ 2 := lt_of_lt_of_le hCden hden
    have hq : 0 ≤ 2 * v / (v ^ 2 - x ^ 2) := div_nonneg (by linarith) hpos.le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw hq)]
    exact mul_le_mul_of_nonneg_left
      (div_le_div₀ (by dsimp only [b]; linarith) (by linarith [hv'.2]) hCden hden) hw
  have hdiff : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1), ∀ v ∈ Ioo a b,
      HasDerivAt (fun t => renyiWeight α x * Real.log (t ^ 2 - x ^ 2))
        (renyiWeight α x * (2 * v / (v ^ 2 - x ^ 2))) v := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    intro v hv'
    have hv1 : 1 < v := ha.trans hv'.1
    have hpos : 0 < v ^ 2 - x ^ 2 := by nlinarith [hx.1, hx.2]
    convert! ((((hasDerivAt_id v).pow 2).sub_const (x ^ 2)).log hpos.ne').const_mul
      (renyiWeight α x) using 1
    norm_num
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioo (0 : ℝ) 1)) (F := fun v x =>
      renyiWeight α x * Real.log (v ^ 2 - x ^ 2))
    (F' := fun v x => renyiWeight α x * (2 * v / (v ^ 2 - x ^ 2)))
    (bound := fun x => renyiWeight α x * C)
    (isOpen_Ioo.mem_nhds ⟨han, hb⟩) hmeas (logarithmic_integrable ha0 ha2 ha1 hv.le)
    (resolvent_integrable ha0 ha2 ha1 hv).aestronglyMeasurable hbound
    ((weight_integrable ha0 ha2 ha1).mul_const C) hdiff).2

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
  field_simp (disch := first | positivity | assumption)

private lemma poisson_power_integral {α : ℝ} (ha0 : 0 < α) (g : ℝ → ℝ) :
    (∫ p in Ioo (0 : ℝ) 1, poissonDensity α p * g (p ^ α⁻¹)) =
      ∫ q in Ioo (0 : ℝ) 1, PoissonWeight.density α q * g q := by
  let G := fun p : ℝ => poissonDensity α p * g (p ^ α⁻¹)
  have hf : ContinuousOn (fun q : ℝ => q ^ α) (uIcc 0 1) :=
    (Real.continuous_rpow_const ha0.le).continuousOn
  have hd : ∀ q ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun q : ℝ => q ^ α) (α * q ^ (α - 1)) q :=
    fun q hq => Real.hasDerivAt_rpow_const (Or.inl hq.1.ne')
  have hn : ∀ q ∈ Ioo (0 : ℝ) 1, 0 ≤ α * q ^ (α - 1) :=
    fun q hq => mul_nonneg ha0.le (Real.rpow_nonneg hq.1.le _)
  have he := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg (g := G) hf
    (by simpa only [min_eq_left zero_le_one, max_eq_right zero_le_one] using hd)
    (by simpa only [min_eq_left zero_le_one, max_eq_right zero_le_one] using hn)
  have hzero : (0 : ℝ) ^ α = 0 := Real.zero_rpow ha0.ne'
  rw [hzero, Real.one_rpow] at he
  have hleft : (∫ q in (0 : ℝ)..1, (G ∘ fun q : ℝ => q ^ α) q *
      (α * q ^ (α - 1))) = ∫ q in (0 : ℝ)..1, PoissonWeight.density α q * g q := by
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro q hq
    dsimp only [G, Function.comp_def, PoissonWeight.density, poissonDensity]
    rw [Real.rpow_rpow_inv hq.1.le ha0.ne']
    ring
  rw [hleft] at he
  simpa only [intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo] using he.symm

private lemma mellin_mass {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2) (ha1 : α ≠ 1) :
    ∫ q in Ioo (0 : ℝ) 1, PoissonWeight.density α q = 1 / 2 := by
  have hsub := power_substitution_integral ha0 (fun _ => (1 : ℝ))
  have hpow := poisson_power_integral ha0 (fun _ => (1 : ℝ))
  have he := hsub.trans hpow
  simpa only [mul_one] using he.symm.trans (by
    simpa only [mul_one] using weight_mass ha0 ha2 ha1)

private lemma mellin_stieltjes_integral {α r : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hr0 : 0 < r) (hr1 : r < 1) :
    (∫ q in Ioo (0 : ℝ) 1, PoissonWeight.density α q *
      (1 / (r + q) + q / (1 + r * q))) =
      1 / ((α - 1) * (1 - r)) -
        α * r ^ (α - 1) / ((α - 1) * (1 - r ^ α)) := by
  obtain ⟨hi, he⟩ := PoissonWeight.stieltjes_integral ha0 ha2 ha1 hr0 hr1
  let g := fun q => PoissonWeight.density α q / (r + q)
  have him : (fun q : ℝ => q⁻¹) '' Ioo (0 : ℝ) 1 = Ioi 1 := by
    simpa only [image_inv_eq_inv, inv_one] using
      (inv_Ioo_0_left (zero_lt_one : (0 : ℝ) < 1))
  have hinj : InjOn (fun q : ℝ => q⁻¹) (Ioo 0 1) :=
    fun _ _ _ _ h => inv_injective h
  have hd : ∀ q ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt (fun q : ℝ => q⁻¹) (-(q ^ 2)⁻¹) (Ioo 0 1) q :=
    fun q hq => (hasDerivAt_inv hq.1.ne').hasDerivWithinAt
  have hpoint (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1) :
      |-(q ^ 2)⁻¹| • g q⁻¹ = PoissonWeight.density α q * q / (1 + r * q) := by
    exact PoissonWeight.density_resolvent_reflection hr0 hq.1 ha1
      (cosine_lt_one ha0 ha2 ha1)
  have ht := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hd hinj g
  rw [him] at ht
  have htail : (∫ q in Ioi (1 : ℝ), g q) =
      ∫ q in Ioo (0 : ℝ) 1, PoissonWeight.density α q * q / (1 + r * q) :=
    ht.trans (setIntegral_congr_fun measurableSet_Ioo hpoint)
  have hti := (integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioo hd hinj g).mp (by
      rw [him]
      exact hi.mono_set (Ioi_subset_Ioi zero_le_one))
  have hright := hti.congr_fun hpoint measurableSet_Ioo
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi hi zero_le_one
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at hsplit
  change (∫ q in Ioi (0 : ℝ), g q) - (∫ q in Ioi (1 : ℝ), g q) =
    ∫ q in Ioo (0 : ℝ) 1, g q at hsplit
  rw [htail] at hsplit
  have hsum : (∫ q in Ioo (0 : ℝ) 1, PoissonWeight.density α q *
      (1 / (r + q) + q / (1 + r * q))) =
      (∫ q in Ioo (0 : ℝ) 1, g q) +
        ∫ q in Ioo (0 : ℝ) 1, PoissonWeight.density α q * q / (1 + r * q) := by
    calc
      _ = ∫ q in Ioo (0 : ℝ) 1, g q + PoissonWeight.density α q * q / (1 + r * q) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro q _
        dsimp only [g]
        ring
      _ = _ := integral_add (hi.mono_set Ioo_subset_Ioi_self) hright
  rw [hsum]
  change (∫ q in Ioi (0 : ℝ), g q) = _ at he
  linarith

private lemma poisson_resolvent_integral {α ν : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hv : 1 < ν) :
    (∫ p in Ioo (0 : ℝ) 1, poissonDensity α p *
      (2 * ν / (ν ^ 2 - ((1 - p ^ α⁻¹) / (1 + p ^ α⁻¹)) ^ 2))) =
      α * (((ν + 1) / 2) ^ (α - 1) - ((ν - 1) / 2) ^ (α - 1)) /
        (2 * (α - 1) * (((ν + 1) / 2) ^ α - ((ν - 1) / 2) ^ α)) := by
  rw [poisson_power_integral ha0
    (fun q : ℝ => 2 * ν / (ν ^ 2 - ((1 - q) / (1 + q)) ^ 2))]
  let r : ℝ := (ν - 1) / (ν + 1)
  have hvp : 0 < ν + 1 := by linarith
  have hr0 : 0 < r := div_pos (by linarith) hvp
  have hr1 : r < 1 := (div_lt_one hvp).mpr (by linarith)
  have hm := mellin_mass ha0 ha2 ha1
  have hi : IntegrableOn (PoissonWeight.density α) (Ioo 0 1) :=
    Integrable.of_integral_ne_zero (by rw [hm]; norm_num)
  have hk : ContinuousOn (fun q : ℝ => 1 / (r + q) + q / (1 + r * q)) (Icc 0 1) := by
    intro q hq
    have hq0 := hq.1
    exact ((continuousAt_const.div (continuousAt_const.add continuousAt_id)
      (add_pos_of_pos_of_nonneg hr0 hq0).ne').add (continuousAt_id.div
        (continuousAt_const.add (continuousAt_const.mul continuousAt_id))
          (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hr0.le hq0)).ne')).continuousWithinAt
  have hki := hi.mul_continuousOn_of_subset hk measurableSet_Ioo
    isCompact_Icc Ioo_subset_Icc_self
  have hdecomp : (∫ q in Ioo (0 : ℝ) 1, PoissonWeight.density α q *
      (2 * ν / (ν ^ 2 - ((1 - q) / (1 + q)) ^ 2))) =
      2 / (ν + 1) * (1 / 2) + 2 / (ν + 1) ^ 2 *
        (∫ q in Ioo (0 : ℝ) 1, PoissonWeight.density α q *
          (1 / (r + q) + q / (1 + r * q))) := by
    calc
      _ = ∫ q in Ioo (0 : ℝ) 1,
          2 / (ν + 1) * PoissonWeight.density α q + 2 / (ν + 1) ^ 2 *
            (PoissonWeight.density α q * (1 / (r + q) + q / (1 + r * q))) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro q hq
        dsimp only
        have hq0 := hq.1
        have hx := mobius_mem hq
        have hden : 0 < ν ^ 2 - ((1 - q) / (1 + q)) ^ 2 := by
          nlinarith [hx.1, hx.2]
        have hrq : 0 < r + q := by positivity
        have hrpq : 0 < 1 + r * q := by positivity
        have hkernel : 2 * ν / (ν ^ 2 - ((1 - q) / (1 + q)) ^ 2) =
            2 / (ν + 1) + 2 / (ν + 1) ^ 2 *
              (1 / (r + q) + q / (1 + r * q)) := by
          have hvm : 0 < ν - 1 := by linarith
          have hpoly : 0 < ν ^ 2 * (1 + q) ^ 2 - (1 - q) ^ 2 := by
            nlinarith [mul_pos (by nlinarith : 0 < ν ^ 2 - 1)
              (sq_pos_of_pos (by positivity : 0 < 1 + q))]
          dsimp only [r] at hrq hrpq ⊢
          field_simp (disch := first | positivity | assumption | nlinarith [hpoly])
          ring
        rw [hkernel]
        ring
      _ = _ := by rw [integral_add (hi.const_mul _) (hki.const_mul _),
        integral_const_mul, integral_const_mul, hm]
  rw [hdecomp, mellin_stieltjes_integral ha0 ha2 ha1 hr0 hr1]
  have ha : 0 < (ν + 1) / 2 := by positivity
  have hB : (ν - 1) / 2 = ((ν + 1) / 2) * r := by
    dsimp only [r]
    field_simp (disch := positivity)
  have hpow : r ^ α = r * r ^ (α - 1) := by
    rw [Real.rpow_sub_one hr0.ne']
    field_simp (disch := positivity)
  have hpowlt : r ^ α < 1 := Real.rpow_lt_one hr0.le hr1 ha0
  have hden : 0 < 1 - r ^ α := by linarith
  have hdiff := entropy_difference_pos ha0 hv.le
  have hA := Real.rpow_pos_of_pos ha α
  rw [hB, Real.mul_rpow ha.le hr0.le, Real.mul_rpow ha.le hr0.le,
    Real.rpow_sub_one ha.ne']
  have hrel : (ν + 1) * (1 - r) = 2 := by
    dsimp only [r]
    field_simp (disch := positivity)
    ring
  field_simp (disch := first | positivity | assumption | exact sub_ne_zero.mpr ha1)
  linear_combination
    ((α - 1) * (1 - r ^ α) - α * (1 - r ^ (α - 1))) * hrel - 2 * α * hpow

private lemma resolvent_integral {α ν : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hv : 1 < ν) :
    (∫ x in Ioo (0 : ℝ) 1, renyiWeight α x * (2 * ν / (ν ^ 2 - x ^ 2))) =
      α * (((ν + 1) / 2) ^ (α - 1) - ((ν - 1) / 2) ^ (α - 1)) /
        (2 * (α - 1) * (((ν + 1) / 2) ^ α - ((ν - 1) / 2) ^ α)) := by
  rw [power_substitution_integral ha0]
  exact poisson_resolvent_integral ha0 ha2 ha1 hv

private lemma renyiFunction_hasDerivAt {α ν : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hv : 1 < ν) :
    HasDerivAt (renyiFunction α)
      (∫ x in Ioo (0 : ℝ) 1, renyiWeight α x * (2 * ν / (ν ^ 2 - x ^ 2))) ν := by
  rw [resolvent_integral ha0 ha2 ha1 hv]
  exact renyiFunction_derivative ha0 ha1 hv

private lemma renyiFunction_normalized_limit {α : ℝ} (ha0 : 0 < α) (ha1 : α ≠ 1) :
    Tendsto (fun ν => renyiFunction α ν - Real.log ν) atTop (nhds (renyiConstant α)) := by
  have hdf : HasDerivAt (fun t : ℝ => (1 + t) ^ α - (1 - t) ^ α) (2 * α) 0 := by
    have hA := ((hasDerivAt_id (0 : ℝ)).const_add 1).rpow_const
      (p := α) (Or.inl (by norm_num))
    have hB := ((hasDerivAt_id (0 : ℝ)).const_sub 1).rpow_const
      (p := α) (Or.inl (by norm_num))
    convert! hA.sub hB using 1
    norm_num
    ring
  have hratio : Tendsto (fun ν : ℝ => ν * ((1 + ν⁻¹) ^ α - (1 - ν⁻¹) ^ α))
      atTop (nhds (2 * α)) := by
    simpa only [Function.comp_def, zero_add, add_zero, sub_zero, one_rpow, sub_self,
      inv_inv, smul_eq_mul]
      using hdf.tendsto_slope_zero_right.comp
        (tendsto_inv_atTop_nhdsGT_zero : Tendsto (fun ν : ℝ => ν⁻¹) atTop (nhdsWithin 0 (Ioi 0)))
  have hlim := ((hratio.log (by positivity)).sub_const (α * Real.log 2)).div_const (α - 1)
  have hval : (Real.log (2 * α) - α * Real.log 2) / (α - 1) = renyiConstant α := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ha0.ne']
    dsimp only [renyiConstant]
    field_simp (disch := first | positivity | assumption | simp only [sub_ne_zero.mpr ha1])
    ring
  rw [hval] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with ν hv
  have hv0 : 0 < ν := by linarith
  have hvh : 0 < ν / 2 := by positivity
  have hi : 0 < ν⁻¹ := inv_pos.mpr hv0
  have hi1 : ν⁻¹ < 1 := by
    simpa only [one_div] using (div_lt_one hv0).mpr hv
  have hp : 0 < 1 + ν⁻¹ := by positivity
  have hm : 0 < 1 - ν⁻¹ := by linarith
  have hg : 0 < (1 + ν⁻¹) ^ α - (1 - ν⁻¹) ^ α :=
    sub_pos.mpr (Real.rpow_lt_rpow hm.le (by linarith) ha0)
  have hA : (ν + 1) / 2 = (ν / 2) * (1 + ν⁻¹) := by
    field_simp (disch := first | positivity | assumption)
  have hB : (ν - 1) / 2 = (ν / 2) * (1 - ν⁻¹) := by
    field_simp (disch := first | positivity | assumption)
  have hD : ((ν + 1) / 2) ^ α - ((ν - 1) / 2) ^ α =
      (ν / 2) ^ α * ((1 + ν⁻¹) ^ α - (1 - ν⁻¹) ^ α) := by
    rw [hA, hB, Real.mul_rpow hvh.le hp.le, Real.mul_rpow hvh.le hm.le]
    ring
  dsimp only [renyiFunction]
  rw [hD, Real.log_mul (Real.rpow_pos_of_pos hvh α).ne' hg.ne', Real.log_rpow hvh,
    Real.log_div hv0.ne' (by norm_num : (2 : ℝ) ≠ 0), Real.log_mul hv0.ne' hg.ne']
  field_simp (disch := first | positivity | assumption | simp only [sub_ne_zero.mpr ha1])
  ring

private lemma logarithm_normalization {ν x : ℝ} (hv : 1 < ν) (hx : x ∈ Icc 0 1) :
    Real.log (ν ^ 2 - x ^ 2) - 2 * Real.log ν = Real.log (1 - (x / ν) ^ 2) := by
  have hv0 : 0 < ν := by linarith
  have hpos : 0 < ν ^ 2 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hq : 1 - (x / ν) ^ 2 = (ν ^ 2 - x ^ 2) / ν ^ 2 := by
    field_simp (disch := first | positivity | assumption)
  have hqp : 0 < 1 - (x / ν) ^ 2 := by rw [hq]; exact div_pos hpos (sq_pos_of_pos hv0)
  have heq : ν ^ 2 - x ^ 2 = ν ^ 2 * (1 - (x / ν) ^ 2) := by
    field_simp (disch := first | positivity | assumption)
  rw [heq, Real.log_mul (pow_ne_zero 2 hv0.ne') hqp.ne', Real.log_pow]
  ring

private lemma normalized_log_integrable {α ν : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hv : 1 < ν) :
    IntegrableOn (fun x => renyiWeight α x * Real.log (1 - (x / ν) ^ 2)) (Ioo 0 1) := by
  have hi := (logarithmic_integrable ha0 ha2 ha1 hv.le).sub
    ((weight_integrable ha0 ha2 ha1).mul_const (2 * Real.log ν))
  apply hi.congr_fun _ measurableSet_Ioo
  intro x hx
  change renyiWeight α x * Real.log (ν ^ 2 - x ^ 2) -
    renyiWeight α x * (2 * Real.log ν) =
    renyiWeight α x * Real.log (1 - (x / ν) ^ 2)
  rw [← logarithm_normalization hv ⟨hx.1.le, hx.2.le⟩]
  ring

private lemma normalized_integral_eq {α ν : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hv : 1 < ν) :
    (∫ x in Ioo (0 : ℝ) 1, renyiWeight α x * Real.log (1 - (x / ν) ^ 2)) =
      (∫ x in Ioo (0 : ℝ) 1, renyiWeight α x * Real.log (ν ^ 2 - x ^ 2)) - Real.log ν := by
  calc
    _ = ∫ x in Ioo (0 : ℝ) 1, renyiWeight α x * Real.log (ν ^ 2 - x ^ 2) -
        renyiWeight α x * (2 * Real.log ν) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      change renyiWeight α x * Real.log (1 - (x / ν) ^ 2) =
        renyiWeight α x * Real.log (ν ^ 2 - x ^ 2) - renyiWeight α x * (2 * Real.log ν)
      rw [← logarithm_normalization hv ⟨hx.1.le, hx.2.le⟩]
      ring
    _ = (∫ x in Ioo (0 : ℝ) 1, renyiWeight α x * Real.log (ν ^ 2 - x ^ 2)) -
        (∫ x in Ioo (0 : ℝ) 1, renyiWeight α x) * (2 * Real.log ν) := by
      rw [integral_sub (logarithmic_integrable ha0 ha2 ha1 hv.le)
        ((weight_integrable ha0 ha2 ha1).mul_const (2 * Real.log ν)), integral_mul_const]
    _ = _ := by rw [weight_mass ha0 ha2 ha1]; ring

private lemma logarithmic_normalized_limit {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) :
    Tendsto (fun ν => (∫ x in Ioo (0 : ℝ) 1,
      renyiWeight α x * Real.log (ν ^ 2 - x ^ 2)) - Real.log ν) atTop (nhds 0) := by
  have hmeas : ∀ᶠ ν in atTop, AEStronglyMeasurable
      (fun x => renyiWeight α x * Real.log (1 - (x / ν) ^ 2))
      (volume.restrict (Ioo 0 1)) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with ν hv
    exact (normalized_log_integrable ha0 ha2 ha1 hv).aestronglyMeasurable
  have hbound : ∀ᶠ ν in atTop, ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1),
      ‖renyiWeight α x * Real.log (1 - (x / ν) ^ 2)‖ ≤
        renyiWeight α x * (-Real.log (3 / 4)) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with ν hv
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hv0 : 0 < ν := by linarith
    have hw := (weight_pos ha0 ha2 ha1 hx.1.le hx.2).le
    have hr0 : 0 ≤ x / ν := div_nonneg hx.1.le hv0.le
    have hr1 : x / ν ≤ 1 / 2 := (div_le_iff₀ hv0).mpr (by linarith [hx.2])
    have harg : (3 / 4 : ℝ) ≤ 1 - (x / ν) ^ 2 := by
      nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr1)]
    have hloglo : Real.log (3 / 4) ≤ Real.log (1 - (x / ν) ^ 2) :=
      Real.log_le_log (by norm_num) harg
    have hloghi : Real.log (1 - (x / ν) ^ 2) ≤ 0 :=
      Real.log_nonpos (by linarith) (by nlinarith [sq_nonneg (x / ν)])
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw, abs_of_nonpos hloghi]
    exact mul_le_mul_of_nonneg_left (neg_le_neg hloglo) hw
  have hlim : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1),
      Tendsto (fun ν => renyiWeight α x * Real.log (1 - (x / ν) ^ 2)) atTop (nhds 0) := by
    apply ae_of_all
    intro x
    have ht : Tendsto (fun ν : ℝ => x / ν) atTop (nhds 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using
        (tendsto_inv_atTop_zero : Tendsto (fun ν : ℝ => ν⁻¹) atTop (nhds 0)).const_mul x
    have hl : Tendsto (fun ν : ℝ => 1 - (x / ν) ^ 2) atTop (nhds 1) := by
      simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero] using
        tendsto_const_nhds.sub (ht.pow 2)
    simpa only [Real.log_one, mul_zero] using (hl.log one_ne_zero).const_mul (renyiWeight α x)
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioo (0 : ℝ) 1)) (f := fun _ => (0 : ℝ))
    (fun x => renyiWeight α x * (-Real.log (3 / 4))) hmeas hbound
    ((weight_integrable ha0 ha2 ha1).mul_const (-Real.log (3 / 4))) hlim
  have ht' : Tendsto (fun ν => ∫ x in Ioo (0 : ℝ) 1,
      renyiWeight α x * Real.log (1 - (x / ν) ^ 2)) atTop (nhds 0) := by
    simpa only [integral_zero] using ht
  apply ht'.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with ν hv
  exact normalized_integral_eq ha0 ha2 ha1 hv

private lemma representation_atTop {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) :
    Tendsto (fun ν => renyiFunction α ν -
      ∫ x in Ioo (0 : ℝ) 1, renyiWeight α x * Real.log (ν ^ 2 - x ^ 2))
      atTop (nhds (renyiConstant α)) := by
  have hs := renyiFunction_normalized_limit ha0 ha1
  have hi := logarithmic_normalized_limit ha0 ha2 ha1
  have hlim := hs.sub hi
  simpa only [sub_sub_sub_cancel_right, sub_zero] using hlim

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

private lemma logarithmic_continuousWithinAt_one {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) : ContinuousWithinAt
      (fun ν => ∫ x in Ioo (0 : ℝ) 1, renyiWeight α x * Real.log (ν ^ 2 - x ^ 2))
      (Ici 1) 1 := by
  let B := fun x => renyiWeight α x * (Real.log 4 - Real.log (1 - x ^ 2))
  have hBi : Integrable B (volume.restrict (Ioo 0 1)) := by
    convert! ((weight_integrable ha0 ha2 ha1).mul_const (Real.log 4)).sub
      (logarithmic_integrable_at_one ha0 ha2 ha1) using 1
    ext x
    dsimp only [B, Pi.sub_apply]
    ring
  have hmeas : ∀ᶠ ν in nhdsWithin (1 : ℝ) (Ici 1), AEStronglyMeasurable
      (fun x => renyiWeight α x * Real.log (ν ^ 2 - x ^ 2))
      (volume.restrict (Ioo 0 1)) := by
    filter_upwards [self_mem_nhdsWithin] with ν hv
    exact (logarithmic_integrable ha0 ha2 ha1 hv).aestronglyMeasurable
  have hbound : ∀ᶠ ν in nhdsWithin (1 : ℝ) (Ici 1),
      ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1),
        ‖renyiWeight α x * Real.log (ν ^ 2 - x ^ 2)‖ ≤ B x := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (1 : ℝ) < 2))]
      with ν hv1 hv2
    change 1 ≤ ν at hv1
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hw := (weight_pos ha0 ha2 ha1 hx.1.le hx.2).le
    have hxpos : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    have hvpos : 0 < ν ^ 2 - x ^ 2 := by nlinarith [hx.1, hx.2, hv1]
    have hloglo : Real.log (1 - x ^ 2) ≤ Real.log (ν ^ 2 - x ^ 2) :=
      Real.log_le_log hxpos (by nlinarith [hv1])
    have hloghi : Real.log (ν ^ 2 - x ^ 2) ≤ Real.log 4 :=
      Real.log_le_log hvpos (by nlinarith [sq_nonneg x, hv1])
    have hl0 : Real.log (1 - x ^ 2) ≤ 0 := Real.log_nonpos hxpos.le (by nlinarith)
    have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
    exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, by linarith⟩) hw
  have hlim : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1),
      Tendsto (fun ν => renyiWeight α x * Real.log (ν ^ 2 - x ^ 2))
        (nhdsWithin (1 : ℝ) (Ici 1))
        (nhds (renyiWeight α x * Real.log (1 ^ 2 - x ^ 2))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hxpos : 0 < (1 : ℝ) ^ 2 - x ^ 2 := by nlinarith [hx.1, hx.2]
    exact (((continuousAt_id.pow 2).sub continuousAt_const).log hxpos.ne').const_mul
      (renyiWeight α x) |>.continuousWithinAt
  exact tendsto_integral_filter_of_dominated_convergence B hmeas hbound hBi hlim

private lemma renyiFunction_continuousAt_one {α : ℝ} (ha0 : 0 < α) :
    ContinuousAt (renyiFunction α) 1 := by
  have hA : ContinuousAt (fun v : ℝ => ((v + 1) / 2) ^ α) 1 :=
    ((continuousAt_id.add continuousAt_const).div_const 2).rpow_const (Or.inr ha0.le)
  have hB : ContinuousAt (fun v : ℝ => ((v - 1) / 2) ^ α) 1 :=
    ((continuousAt_id.sub continuousAt_const).div_const 2).rpow_const (Or.inr ha0.le)
  exact ((hA.sub hB).log (entropy_difference_pos ha0 le_rfl).ne').div_const (α - 1)

private lemma representation_at_one {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) :
    renyiFunction α 1 = renyiConstant α +
      ∫ x in Ioo (0 : ℝ) 1, renyiWeight α x * Real.log (1 ^ 2 - x ^ 2) := by
  have hr := fun v (hv : 1 < v) => representation_of_one_lt ha0 ha2 ha1 hv
  have hl := (renyiFunction_continuousAt_one ha0).continuousWithinAt (s := Ioi (1 : ℝ))
  have hi := (logarithmic_continuousWithinAt_one ha0 ha2 ha1).mono Ioi_subset_Ici_self
  have heq : (fun v => renyiFunction α v) =ᶠ[nhdsWithin (1 : ℝ) (Ioi 1)]
      (fun v => renyiConstant α +
        ∫ x in Ioo (0 : ℝ) 1, renyiWeight α x * Real.log (v ^ 2 - x ^ 2)) := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    exact hr v hv
  exact tendsto_nhds_unique hl ((tendsto_const_nhds.add hi).congr' heq.symm)

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

end

end D5.S3.Quantum.Analysis.BosonicRenyiStieltjes
