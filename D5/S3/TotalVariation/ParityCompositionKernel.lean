/- GID: D5/S3/TotalVariation/ParityCompositionKernel
   generality: G
   mirror-B: D5/B/S3/TotalVariation/ParityCompositionKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Parity masses of uniform weak compositions and biased Bernoulli vectors. -/

import D5.S3.TotalVariation.Metric
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.TotalVariation.ParityCompositionKernel

open Finset Real Set
open scoped BigOperators

/-- The parity-vector mass induced by the uniform weak compositions of `M` into `d` parts.
The binomial coefficient is evaluated only after the parity and support tests succeed. -/
noncomputable def R (d M : ℕ) (ξ : Fin d → Bool) : ℝ :=
  let h := ∑ i, (ξ i).toNat
  if h % 2 = M % 2 ∧ h ≤ M then
    (((M - h) / 2 + d - 1).choose (d - 1) : ℝ) /
      ((M + d - 1).choose (d - 1) : ℝ)
  else 0

/-- Independent Bernoulli masses with parameter `M / (2M + d)`, conditioned on the
parity of the total number of occupied coordinates. -/
noncomputable def Q (d M : ℕ) (ξ : Fin d → Bool) : ℝ :=
  let h := ∑ i, (ξ i).toNat
  let ν : ℝ := M / (2 * M + d)
  let η : ℝ := d / (2 * M + d)
  let p : ℝ := (1 + (-1 : ℝ) ^ M * η ^ d) / 2
  if h % 2 = M % 2 then ν ^ h * (1 - ν) ^ (d - h) / p else 0

/-- The continuous logarithmic profile of the parity density ratio. -/
private noncomputable def logProfile (d M : ℕ) (x : ℝ) : ℝ :=
  (∑ j ∈ range (d - 1), log ((M : ℝ) - x + 2 * (j + 1))) -
    x * log ((M : ℝ) / (M + d))

/-- At the unconditioned Bernoulli center, the continuum cancellation leaves only
the endpoint error of the complete reciprocal sum. -/
private theorem profile_endpoint (d M : ℕ) (hd : 2 ≤ d) (hM : 3 * d ≤ M) :
    let m : ℝ := d * M / (2 * M + d)
    let s : ℝ := -(∑ j ∈ range (d - 1),
      1 / ((M : ℝ) - m + 2 * (j + 1))) - log ((M : ℝ) / (M + d))
    HasDerivAt (logProfile d M) s m ∧ 0 ≤ s ∧ s ≤ 1 / ((M : ℝ) - d) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hMd : (d : ℝ) < M := by exact_mod_cast (by omega : d < M)
  have hM0 : (0 : ℝ) < M := hd0.trans hMd
  have hden : (0 : ℝ) < 2 * M + d := by positivity
  let m : ℝ := d * M / (2 * M + d)
  have hm0 : 0 < m := by dsimp [m]; positivity
  have hmd : m < d := by
    dsimp [m]
    rw [div_lt_iff₀ hden]
    nlinarith
  let a : ℝ := M - m
  have ha : 0 < a := by dsimp [a]; linarith
  have had : (M : ℝ) - d ≤ a := by dsimp [a]; linarith
  let f : ℝ → ℝ := fun y => 1 / (a + 2 * y)
  have hfpos (y : ℝ) (hy : 0 ≤ y) : 0 < a + 2 * y := by linarith
  have hfcont : ContinuousOn f (Icc 0 d) := by
    apply ContinuousOn.div continuousOn_const
      (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
    intro y hy
    exact (hfpos y hy.1).ne'
  have hfanti : AntitoneOn f (Icc 0 d) := by
    intro x hx y hy hxy
    exact one_div_le_one_div_of_le (hfpos x hx.1) (by linarith)
  have hint : (∫ y in (0 : ℝ)..d, f y) = -log ((M : ℝ) / (M + d)) := by
    have hcalc : (∫ y in (0 : ℝ)..d, f y) =
        log (a + 2 * d) / 2 - log a / 2 := by
      have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := (0 : ℝ)) (b := (d : ℝ))
        (f := fun y => log (a + 2 * y) / 2) (f' := f)
      simp only [mul_zero, add_zero] at ht
      apply ht
      · intro y hy
        rw [uIcc_of_le (le_of_lt hd0)] at hy
        convert (((hasDerivAt_const y a).add
          ((hasDerivAt_id y).const_mul 2)).log (hfpos y hy.1).ne').div_const 2 using 1 <;>
          dsimp [f] <;> ring
      · exact hfcont.intervalIntegrable
    have hr : (a + 2 * d) / a = (((M : ℝ) + d) / M) ^ 2 := by
      dsimp [a, m]
      field_simp [hden.ne', hM0.ne']
      ring
    rw [hcalc, ← sub_div, ← log_div (hfpos d hd0.le).ne' ha.ne', hr, log_pow]
    have hi : ((M : ℝ) + d) / M = ((M : ℝ) / (M + d))⁻¹ := by
      rw [inv_div]
    rw [hi, log_inv]
    ring
  have hdc : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hint0 : IntervalIntegrable f MeasureTheory.volume (0 : ℝ) d :=
    hfcont.intervalIntegrable
  have hsumlo : (∫ y in (1 : ℝ)..d, f y) ≤
      ∑ j ∈ range (d - 1), f (j + 1) := by
    have ht := AntitoneOn.integral_le_sum
      (x₀ := (1 : ℝ)) (a := d - 1)
      (hfanti.mono (by
        rw [hdc]
        simp only [add_sub_cancel]
        exact Icc_subset_Icc (by norm_num) le_rfl))
    simpa only [hdc, add_sub_cancel, add_comm] using ht
  have hsumhi : (∑ j ∈ range (d - 1), f (j + 1)) ≤
      ∫ y in (0 : ℝ)..d, f y := by
    have ht := AntitoneOn.sum_le_integral
      (x₀ := (0 : ℝ)) (a := d - 1)
      (hfanti.mono (by
        rw [hdc]
        simp only [zero_add]
        exact Icc_subset_Icc le_rfl (by linarith)))
    simp only [zero_add, Nat.cast_add, Nat.cast_one] at ht
    refine ht.trans ?_
    apply intervalIntegral.integral_mono_interval le_rfl
      (by linarith [hdc]) (by linarith [hdc]) _ hint0
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    exact (one_div_pos.mpr (hfpos x hx.1.le)).le
  have htail : (∫ y in (0 : ℝ)..1, f y) ≤ 1 / ((M : ℝ) - d) := by
    calc
      (∫ y in (0 : ℝ)..1, f y) ≤ ∫ _ in (0 : ℝ)..1, 1 / ((M : ℝ) - d) := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          (hfcont.mono (Icc_subset_Icc le_rfl (by linarith))).intervalIntegrable
          (intervalIntegral.intervalIntegrable_const)
        intro y hy
        exact one_div_le_one_div_of_le (sub_pos.mpr hMd) (by linarith [had, hy.1])
      _ = 1 / ((M : ℝ) - d) := by simp
  have hadd : (∫ y in (0 : ℝ)..1, f y) + (∫ y in (1 : ℝ)..d, f y) =
      ∫ y in (0 : ℝ)..d, f y := by
    apply intervalIntegral.integral_add_adjacent_intervals
    · exact (hfcont.mono (Icc_subset_Icc le_rfl (by linarith))).intervalIntegrable
    · exact (hfcont.mono (Icc_subset_Icc (by norm_num) le_rfl)).intervalIntegrable
  refine ⟨?_, ?_, ?_⟩
  · apply HasDerivAt.sub
    · convert HasDerivAt.fun_sum (u := range (d - 1)) (fun j hj =>
        (((hasDerivAt_const m (M : ℝ)).sub (hasDerivAt_id m)).add_const
          (2 * (j + 1))).log (by
            have ht : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
            dsimp [a] at ha
            linarith : (M : ℝ) - m + 2 * (j + 1) ≠ 0)) using 1
      simp only [zero_sub, neg_div, sum_neg_distrib]
    · exact (hasDerivAt_id m).mul_const _
  · dsimp [f, a] at hsumhi
    rw [hint] at hsumhi
    dsimp [m] at hsumhi ⊢
    linarith
  · dsimp [f, a] at hsumlo
    rw [hint] at hadd
    dsimp [m] at hsumlo ⊢
    linarith

end D5.S3.TotalVariation.ParityCompositionKernel
