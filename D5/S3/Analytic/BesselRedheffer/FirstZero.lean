/- GID: D5/S3/Analytic/BesselRedheffer/FirstZero
   generality: G
   mirror-B: D5/B/S3/Analytic/BesselRedheffer/FirstZero
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Integrals.Basic, mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Deriv, mathlib/module/Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts, mathlib/module/Mathlib.Topology.Order.IntermediateValue, mathlib/module/Mathlib.Topology.Order.Monotone]
   utility: none
   digest: A weighted energy bound, existence, and positivity of the first normalized Bessel zero. -/

import D5.S3.Analytic.BesselRedheffer.Series
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Monotone

open Set MeasureTheory Filter Topology
open D5.S3.Analytic.BesselRedheffer.Defs
open D5.S3.Analytic.BesselRedheffer.Series

set_option maxHeartbeats 800000

namespace D5.S3.Analytic.BesselRedheffer.FirstZero

private lemma exists_zero_of_nonpos {ν x : ℝ} (hν : -1 < ν) (hx : 0 ≤ x)
    (hfx : nbessel ν x ≤ 0) : ∃ r, 0 < r ∧ r ≤ x ∧ nbessel ν r = 0 := by
  have hm : (0 : ℝ) ∈ Icc (nbessel ν x) (nbessel ν 0) := by
    rw [nbessel_zero]
    exact ⟨hfx, zero_le_one⟩
  obtain ⟨r, hr, hfr⟩ := intermediate_value_Icc' hx (continuous_nbessel hν).continuousOn hm
  refine ⟨r, ?_, hr.2, hfr⟩
  rcases hr.1.eq_or_lt with he | hp
  · subst r
    rw [nbessel_zero] at hfr
    norm_num at hfr
  · exact hp

/-- The normalized series stays positive before its first positive zero. -/
theorem nbessel_pos_of_lt {ν x : ℝ} (hν : -1 < ν) (hx : 0 ≤ x)
    (hxj : x < firstZero ν) : 0 < nbessel ν x := by
  by_contra hn
  obtain ⟨r, hr, hrx, hfr⟩ := exists_zero_of_nonpos hν hx (le_of_not_gt hn)
  have hbelow : BddBelow {r : ℝ | 0 < r ∧ nbessel ν r = 0} := ⟨0, fun r hr => hr.1.le⟩
  have hjr : firstZero ν ≤ r := csInf_le hbelow ⟨hr, hfr⟩
  linarith

private lemma integral_power {p : ℝ} (hp : 0 ≤ p) :
    (∫ r in (0 : ℝ)..1, r ^ p) = 1 / (p + 1) := by
  rw [integral_rpow (Or.inl (by linarith))]
  rw [Real.one_rpow, Real.zero_rpow (by linarith : p + 1 ≠ 0)]
  ring

private lemma integral_trial6 {p : ℝ} (hp : 0 ≤ p) :
    (∫ r in (0 : ℝ)..1, r ^ p * (1 - r ^ 2) ^ 6) =
      1 / (p + 1) - 6 / (p + 3) + 15 / (p + 5) - 20 / (p + 7) +
        15 / (p + 9) - 6 / (p + 11) + 1 / (p + 13) := by
  have he : (∫ r in (0 : ℝ)..1, r ^ p * (1 - r ^ 2) ^ 6) =
      ∫ r in (0 : ℝ)..1, r ^ p - 6 * r ^ (p + 2) + 15 * r ^ (p + 4) -
        20 * r ^ (p + 6) + 15 * r ^ (p + 8) - 6 * r ^ (p + 10) + r ^ (p + 12) := by
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro r hr
    dsimp only
    simp only [Real.rpow_add hr.1]
    simp only [Real.rpow_ofNat]
    ring
  rw [he]
  have hi (q : ℝ) (hq : 0 ≤ q) : IntervalIntegrable (fun r : ℝ => r ^ q) volume 0 1 :=
    (Real.continuous_rpow_const hq).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_add, intervalIntegral.integral_sub]
  · simp only [intervalIntegral.integral_const_mul]
    rw [integral_power hp, integral_power (by linarith : 0 ≤ p + 2),
      integral_power (by linarith : 0 ≤ p + 4), integral_power (by linarith : 0 ≤ p + 6),
      integral_power (by linarith : 0 ≤ p + 8), integral_power (by linarith : 0 ≤ p + 10),
      integral_power (by linarith : 0 ≤ p + 12)]
    ring
  all_goals apply Continuous.intervalIntegrable
  all_goals fun_prop (disch := positivity)

private lemma integral_trial4 {p : ℝ} (hp : 0 ≤ p) :
    (∫ r in (0 : ℝ)..1, r ^ p * (1 - r ^ 2) ^ 4) =
      1 / (p + 1) - 4 / (p + 3) + 6 / (p + 5) - 4 / (p + 7) + 1 / (p + 9) := by
  have he : (∫ r in (0 : ℝ)..1, r ^ p * (1 - r ^ 2) ^ 4) =
      ∫ r in (0 : ℝ)..1, r ^ p - 4 * r ^ (p + 2) + 6 * r ^ (p + 4) -
        4 * r ^ (p + 6) + r ^ (p + 8) := by
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro r hr
    dsimp only
    simp only [Real.rpow_add hr.1]
    simp only [Real.rpow_ofNat]
    ring
  rw [he, intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_add, intervalIntegral.integral_sub]
  · simp only [intervalIntegral.integral_const_mul]
    rw [integral_power hp, integral_power (by linarith : 0 ≤ p + 2),
      integral_power (by linarith : 0 ≤ p + 4), integral_power (by linarith : 0 ≤ p + 6),
      integral_power (by linarith : 0 ≤ p + 8)]
    ring
  all_goals apply Continuous.intervalIntegrable
  all_goals fun_prop (disch := positivity)

private lemma picone_integral {p L : ℝ} (hp : 1 ≤ p)
    (y v a : ℝ → ℝ)
    (hy : ∀ r ∈ Icc (0 : ℝ) 1, HasDerivAt y (v r) r)
    (hv : ∀ r ∈ Icc (0 : ℝ) 1, HasDerivAt v (a r) r)
    (hpos : ∀ r ∈ Icc (0 : ℝ) 1, 0 < y r)
    (hode : ∀ r ∈ Ioo (0 : ℝ) 1, r * a r + p * v r + L * r * y r = 0) :
    L * (∫ r in (0 : ℝ)..1, r ^ p * ((1 - r ^ 2) ^ 3) ^ 2) ≤
      ∫ r in (0 : ℝ)..1, r ^ p * (-6 * r * (1 - r ^ 2) ^ 2) ^ 2 := by
  let w : ℝ → ℝ := fun r => r ^ p
  let u : ℝ → ℝ := fun r => (1 - r ^ 2) ^ 3
  let d : ℝ → ℝ := fun r => -6 * r * (1 - r ^ 2) ^ 2
  let h : ℝ → ℝ := fun r => v r / y r
  let H : ℝ → ℝ := fun r => w r * h r * (u r) ^ 2
  let q : ℝ → ℝ := fun r => w r * (d r - h r * u r) ^ 2
  let f : ℝ → ℝ := fun r => w r * (d r) ^ 2 - L * (w r * (u r) ^ 2)
  have cy : ContinuousOn y (Icc (0 : ℝ) 1) := fun r hr => (hy r hr).continuousAt.continuousWithinAt
  have cv : ContinuousOn v (Icc (0 : ℝ) 1) := fun r hr => (hv r hr).continuousAt.continuousWithinAt
  have ch : ContinuousOn h (Icc (0 : ℝ) 1) := cv.div cy (fun r hr => (hpos r hr).ne')
  have cw : Continuous w := Real.continuous_rpow_const (by linarith)
  have cu : Continuous u := by dsimp [u]; fun_prop
  have cd : Continuous d := by dsimp [d]; fun_prop
  have cH : ContinuousOn H (Icc (0 : ℝ) 1) := (cw.continuousOn.mul ch).mul (cu.pow 2).continuousOn
  have cq : ContinuousOn q (Icc (0 : ℝ) 1) :=
    cw.continuousOn.mul ((cd.continuousOn.sub (ch.mul cu.continuousOn)).pow 2)
  have cf : Continuous f := (cw.mul (cd.pow 2)).sub ((cw.mul (cu.pow 2)).const_mul L)
  have hdH : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt H (f r - q r) r := by
    intro r hr
    have hrc : r ∈ Icc (0 : ℝ) 1 := ⟨hr.1.le, hr.2.le⟩
    have hwr : HasDerivAt w (p * r ^ (p - 1)) r := Real.hasDerivAt_rpow_const (Or.inl hr.1.ne')
    have hur : HasDerivAt u (d r) r := by
      convert (((hasDerivAt_const r (1 : ℝ)).sub ((hasDerivAt_id r).pow 2)).pow 3) using 1
      · rfl
      · dsimp [d]
        ring
    have hhr : HasDerivAt h ((a r * y r - v r * v r) / (y r) ^ 2) r :=
      (hv r hrc).div (hy r hrc) (hpos r hrc).ne'
    have hd := (hwr.mul hhr).mul (hur.pow 2)
    convert hd using 1
    dsimp only [f, q, w, u, d, h, Pi.mul_apply, Pi.pow_apply]
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    have hwp : r ^ p = r ^ (p - 1) * r := by
      calc
        r ^ p = r ^ ((p - 1) + 1) := by congr 1; ring
        _ = r ^ (p - 1) * r := by rw [Real.rpow_add hr.1, Real.rpow_one]
    have hO := hode r hr
    have hy0 := (hpos r hrc).ne'
    field_simp
    rw [hwp]
    linear_combination -(r ^ (p - 1)) * (1 - r ^ 2) ^ 6 * y r * hO
  have hint : (∫ r in (0 : ℝ)..1, f r - q r) = 0 := by
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one cH hdH
      ((cf.continuousOn.sub cq).intervalIntegrable_of_Icc zero_le_one)
    convert hi using 1
    dsimp [H, w, u]
    simp [Real.zero_rpow (by linarith : p ≠ 0)]
  have hq : 0 ≤ ∫ r in (0 : ℝ)..1, q r := by
    apply intervalIntegral.integral_nonneg zero_le_one
    intro r hr
    dsimp [q, w]
    exact mul_nonneg (Real.rpow_nonneg hr.1 _) (sq_nonneg _)
  rw [intervalIntegral.integral_sub (cf.intervalIntegrable 0 1)
    (cq.intervalIntegrable_of_Icc zero_le_one)] at hint
  have hf : 0 ≤ ∫ r in (0 : ℝ)..1, f r := by linarith
  dsimp only [f] at hf
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul] at hf
  · dsimp only [w, u, d] at hf
    linarith
  · exact (cw.mul (cd.pow 2)).intervalIntegrable 0 1
  · exact ((cw.mul (cu.pow 2)).const_mul L).intervalIntegrable 0 1

private lemma energy_moments {ν : ℝ} (hν : 30 ≤ ν) :
    (∫ r in (0 : ℝ)..1, r ^ (2 * ν + 1) * (-6 * r * (1 - r ^ 2) ^ 2) ^ 2) =
      ((6 : ℝ) / 5 * (ν + 1) * (ν + 7)) *
        ∫ r in (0 : ℝ)..1, r ^ (2 * ν + 1) * ((1 - r ^ 2) ^ 3) ^ 2 := by
  have he : (∫ r in (0 : ℝ)..1, r ^ (2 * ν + 1) * (-6 * r * (1 - r ^ 2) ^ 2) ^ 2) =
      36 * ∫ r in (0 : ℝ)..1, r ^ (2 * ν + 3) * (1 - r ^ 2) ^ 4 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro r hr
    dsimp only
    rw [show 2 * ν + 3 = (2 * ν + 1) + 2 by ring]
    simp only [Real.rpow_add hr.1, Real.rpow_ofNat, Real.rpow_one]
    ring
  have hd : (∫ r in (0 : ℝ)..1, r ^ (2 * ν + 1) * ((1 - r ^ 2) ^ 3) ^ 2) =
      ∫ r in (0 : ℝ)..1, r ^ (2 * ν + 1) * (1 - r ^ 2) ^ 6 := by
    congr 1
    ext r
    ring
  rw [he, hd, integral_trial4 (by linarith : 0 ≤ 2 * ν + 3),
    integral_trial6 (by linarith : 0 ≤ 2 * ν + 1)]
  have hn (k : ℕ) : 2 * ν + (k : ℝ) + 2 ≠ 0 := by positivity
  have h2 : 2 * ν + 2 ≠ 0 := by linarith
  have h4 : 2 * ν + 4 ≠ 0 := by linarith
  have h6 : 2 * ν + 6 ≠ 0 := by linarith
  have h8 : 2 * ν + 8 ≠ 0 := by linarith
  have h10 : 2 * ν + 10 ≠ 0 := by linarith
  have h12 : 2 * ν + 12 ≠ 0 := by linarith
  have h14 : 2 * ν + 14 ≠ 0 := by linarith
  ring_nf
  field_simp
  <;> ring

/-- Positivity on a closed interval forces the trial-function energy bound. -/
theorem nbessel_energy_bound {ν z : ℝ} (hν : 30 ≤ ν) (hz : 0 < z)
    (hpos : ∀ x ∈ Icc (0 : ℝ) z, 0 < nbessel ν x) :
    z ^ 2 ≤ (6 : ℝ) / 5 * (ν + 1) * (ν + 7) := by
  let y : ℝ → ℝ := fun r => nbessel ν (z * r)
  let v : ℝ → ℝ := fun r => z * (- (z * r) / (2 * (ν + 1)) * nbessel (ν + 1) (z * r))
  let a : ℝ → ℝ := fun r => z ^ 2 *
    (-1 / (2 * (ν + 1)) * nbessel (ν + 1) (z * r) +
      (z * r) ^ 2 / (4 * (ν + 1) * (ν + 2)) * nbessel (ν + 2) (z * r))
  have hv0 : -1 < ν := by linarith
  have hy : ∀ r ∈ Icc (0 : ℝ) 1, HasDerivAt y (v r) r := by
    intro r hr
    convert (hasDerivAt_nbessel hv0 (z * r)).comp r ((hasDerivAt_id r).const_mul z) using 1
    · rfl
    · dsimp [v]
      ring
  have hv : ∀ r ∈ Icc (0 : ℝ) 1, HasDerivAt v (a r) r := by
    intro r hr
    convert ((hasDerivAt_nbessel_deriv hv0 (z * r)).comp r
      ((hasDerivAt_id r).const_mul z)).const_mul z using 1 <;> dsimp [v, a] <;> ring
  have hp : ∀ r ∈ Icc (0 : ℝ) 1, 0 < y r := by
    intro r hr
    apply hpos
    exact ⟨mul_nonneg hz.le hr.1, by nlinarith [hr.2]⟩
  have ho : ∀ r ∈ Ioo (0 : ℝ) 1,
      r * a r + (2 * ν + 1) * v r + z ^ 2 * r * y r = 0 := by
    intro r hr
    have hO := nbessel_ode hv0 (z * r)
    dsimp [a, v, y]
    linear_combination z * hO
  have hE := picone_integral (by linarith : 1 ≤ 2 * ν + 1) y v a hy hv hp ho
  rw [energy_moments hν] at hE
  have hD : 0 < ∫ r in (0 : ℝ)..1, r ^ (2 * ν + 1) * ((1 - r ^ 2) ^ 3) ^ 2 := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
    · apply Continuous.intervalIntegrable
      fun_prop (disch := positivity)
    · intro r hr
      apply mul_pos (Real.rpow_pos_of_pos hr.1 _)
      apply sq_pos_of_pos
      apply pow_pos
      nlinarith [hr.1, hr.2]
    · norm_num
  nlinarith

private lemma zero_set_nonempty {ν : ℝ} (hν : 30 ≤ ν) :
    {x : ℝ | 0 < x ∧ nbessel ν x = 0}.Nonempty := by
  by_contra hn
  have hne : ∀ r : ℝ, 0 < r → nbessel ν r ≠ 0 := by
    intro r hr he
    exact hn ⟨r, hr, he⟩
  let U : ℝ := (6 : ℝ) / 5 * (ν + 1) * (ν + 7)
  have hU : 0 < U := by dsimp [U]; positivity
  have hp : ∀ x ∈ Icc (0 : ℝ) (U + 1), 0 < nbessel ν x := by
    intro x hx
    by_contra hf
    obtain ⟨r, hr, hrx, hfr⟩ := exists_zero_of_nonpos (by linarith : -1 < ν) hx.1
      (le_of_not_gt hf)
    exact hne r hr hfr
  have hE := nbessel_energy_bound hν (by linarith : 0 < U + 1) hp
  change (U + 1) ^ 2 ≤ U at hE
  nlinarith [sq_nonneg U]

private lemma zero_set_closed {ν : ℝ} (hν : -1 < ν) :
    IsClosed {x : ℝ | 0 < x ∧ nbessel ν x = 0} := by
  have he : {x : ℝ | 0 < x ∧ nbessel ν x = 0} =
      {x : ℝ | 0 ≤ x ∧ nbessel ν x = 0} := by
    ext x
    constructor
    · exact fun hx => ⟨hx.1.le, hx.2⟩
    · intro hx
      refine ⟨lt_of_le_of_ne hx.1 ?_, hx.2⟩
      intro hz
      subst x
      have hfx := hx.2
      rw [nbessel_zero] at hfx
      norm_num at hfx
  rw [he]
  exact (isClosed_le continuous_const continuous_id).inter
    (isClosed_eq (continuous_nbessel hν) continuous_const)

/-- The infimum defining the first positive zero is itself a zero. -/
theorem nbessel_firstZero {ν : ℝ} (hν : 30 ≤ ν) : nbessel ν (firstZero ν) = 0 := by
  have hbelow : BddBelow {x : ℝ | 0 < x ∧ nbessel ν x = 0} := ⟨0, fun x hx => hx.1.le⟩
  exact ((zero_set_closed (by linarith : -1 < ν)).csInf_mem (zero_set_nonempty hν) hbelow).2

/-- The first positive zero is positive for every order at least thirty. -/
theorem firstZero_pos {ν : ℝ} (hν : 30 ≤ ν) : 0 < firstZero ν := by
  have hz := nbessel_firstZero hν
  have hj0 : 0 ≤ firstZero ν := le_csInf (zero_set_nonempty hν) (fun x hx => hx.1.le)
  have hjne : firstZero ν ≠ 0 := by
    intro he
    have hp := (nbessel_pos_near_zero (by linarith : -1 < ν)).self_of_nhds
    rw [he] at hz
    rw [hz] at hp
    exact lt_irrefl _ hp
  exact lt_of_le_of_ne hj0 hjne.symm

/-- The cubic radial trial function bounds the square of the first zero. -/
theorem firstZero_sq_le {ν : ℝ} (hν : 30 ≤ ν) :
    firstZero ν ^ 2 ≤ (6 : ℝ) / 5 * (ν + 1) * (ν + 7) := by
  let U : ℝ := (6 : ℝ) / 5 * (ν + 1) * (ν + 7)
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hj := firstZero_pos hν
  by_contra hn
  have hjU : U < firstZero ν ^ 2 := lt_of_not_ge hn
  have hs : Real.sqrt U < firstZero ν := by
    nlinarith [Real.sqrt_nonneg U, Real.sq_sqrt hU]
  let z : ℝ := (Real.sqrt U + firstZero ν) / 2
  have hz : 0 < z := by dsimp [z]; positivity
  have hzj : z < firstZero ν := by dsimp [z]; linarith
  have hsz : Real.sqrt U < z := by dsimp [z]; linarith
  have hp : ∀ x ∈ Icc (0 : ℝ) z, 0 < nbessel ν x := by
    intro x hx
    exact nbessel_pos_of_lt (by linarith : -1 < ν) hx.1 (lt_of_le_of_lt hx.2 hzj)
  have hE := nbessel_energy_bound hν hz hp
  change z ^ 2 ≤ U at hE
  nlinarith [Real.sq_sqrt hU, Real.sqrt_nonneg U]

end D5.S3.Analytic.BesselRedheffer.FirstZero
