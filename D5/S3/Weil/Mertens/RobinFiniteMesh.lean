/- GID: D5/S3/Weil/Mertens/RobinFiniteMesh
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/RobinFiniteMesh
   mirror-E: none(waiver:analytic-integral-estimate)
   anchors: []
   utility: none
   digest: Unconditional finite mesh error for the actual Robin weighted mass. -/

import D5.S3.Weil.Mertens.RobinCenteredChord

/-! The local Chebyshev oscillation widths sum to a single endpoint increment
plus the interval length. This controls the total error for an arbitrary finite
mesh on a doubling block. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Mertens.RobinFiniteMesh

open Real Set MeasureTheory
open Finset (range)
open D5.S3.Arith.Robin.CompleteMertensPeak (psiErrorKernel complete_mertens_ledger)
open D5.S3.Weil.Mertens.RobinCenteredChord (abs_mass_sub_chord_le)
open D5.S3.Weil.Mertens.RobinWeightedRamp (R u)
open D5.S3.Weil.Mertens.WeightedTailTransport (weightedTail)
open D5.S3.Weil.Mertens.WeightedTailWindowMass (weightedNegativeMass)

noncomputable section

/-- The positive part of the signed coordinate chord through the two actual
Robin samples, integrated against the weight in `abs_mass_sub_chord_le`.
The endpoint values of `R` admit the finite Mangoldt formula `RobinWeightedRamp.ramp_eq_sum`. -/
def chordMass (a b : ℝ) : ℝ :=
  let q (t : ℝ) := (u t - u a) / (u b - u a)
  let H (t : ℝ) := (1 - q t) * R a + q t * R b
  ∫ t in a..b, (log t / (1 + log t)) / (t * sqrt t) * max (H t) 0

/-- On a finite mesh in a doubling block, the actual Robin weighted mass is
approximated by the corresponding signed chord masses. The error depends on a
single Chebyshev increment across the whole block. The indexing includes the
empty mesh when both endpoints agree. -/
theorem abs_mass_sub_mesh_le {A B h : ℝ} {N : ℕ} {x : ℕ → ℝ}
    (hA : exp 1 ≤ A) (hB : B ≤ 2 * A) (hx0 : x 0 = A) (hxN : x N = B)
    (hmono : StrictMonoOn x (Iic N)) (hstep : ∀ i < N, x (i + 1) - x i ≤ h) :
    |weightedNegativeMass psiErrorKernel A B -
        (∑ i ∈ range N, chordMass (x i) (x (i + 1)))| ≤
      (3 * h ^ 2 / (4 * A ^ 2 * sqrt A)) * (Chebyshev.psi B - Chebyshev.psi A + B - A) := by
  have hA0 : 0 < A := (exp_pos 1).trans_le hA
  have hA2 : 2 ≤ A := Real.exp_one_gt_two.le.trans hA
  have hleft (i : ℕ) (hi : i ≤ N) : A ≤ x i := by
    rw [← hx0]
    exact hmono.monotoneOn (mem_Iic.mpr (Nat.zero_le N)) (mem_Iic.mpr hi) (Nat.zero_le i)
  have hright (i : ℕ) (hi : i ≤ N) : x i ≤ B := by
    rw [← hxN]
    exact hmono.monotoneOn (mem_Iic.mpr hi) (mem_Iic.mpr le_rfl) hi
  have hcell (i : ℕ) (hi : i < N) : x i < x (i + 1) :=
    hmono (mem_Iic.mpr hi.le) (mem_Iic.mpr (Nat.succ_le_iff.mpr hi)) (Nat.lt_succ_self i)
  let f (t : ℝ) := (WeightedTailInverse.a t / sqrt t) * max (-weightedTail psiErrorKernel t) 0
  have hf : ContinuousOn f (Icc A B) := by
    have hlog : ContinuousOn log (Icc A B) := fun t ht =>
      (continuousAt_log (hA0.trans_le ht.1).ne').continuousWithinAt
    have hweight : ContinuousOn WeightedTailInverse.a (Icc A B) := by
      unfold WeightedTailInverse.a
      exact (hlog.pow 2).div (hlog.const_add 1) (fun t ht => by
        have ht1 : 1 < t := (by linarith only [hA2] : 1 < A).trans_le ht.1
        have htlog := log_pos ht1
        exact ne_of_gt (by positivity))
    have htail : ContinuousOn (weightedTail psiErrorKernel) (Icc A B) :=
      (complete_mertens_ledger hA2).2.1.continuousOn_Ici_primitive_Ioi.mono (fun _ ht => ht.1)
    exact (hweight.div continuous_sqrt.continuousOn
      (fun _ ht => (sqrt_pos.2 (hA0.trans_le ht.1)).ne')).mul
      (htail.neg.sup continuousOn_const)
  have hmass : (∑ i ∈ range N, weightedNegativeMass psiErrorKernel (x i) (x (i + 1))) =
      weightedNegativeMass psiErrorKernel A B := by
    have hint (i : ℕ) (hi : i < N) : IntervalIntegrable f volume (x i) (x (i + 1)) :=
      (hf.mono (Icc_subset_Icc (hleft i hi.le)
        (hright (i + 1) (Nat.succ_le_iff.mpr hi)))).intervalIntegrable_of_Icc (hcell i hi).le
    simpa only [weightedNegativeMass, f, hx0, hxN] using
      (intervalIntegral.sum_integral_adjacent_intervals hint)
  let increment (i : ℕ) := Chebyshev.psi (x (i + 1)) - Chebyshev.psi (x i) + (x (i + 1) - x i)
  have herror (i : ℕ) (hi : i < N) :
      |weightedNegativeMass psiErrorKernel (x i) (x (i + 1)) - chordMass (x i) (x (i + 1))| ≤
        (3 * h ^ 2 / (4 * A ^ 2 * sqrt A)) * increment i := by
    let a := x i
    let b := x (i + 1)
    have hAa : A ≤ a := hleft i hi.le
    have hbB : b ≤ B := hright (i + 1) (Nat.succ_le_iff.mpr hi)
    have hab : a < b := hcell i hi
    have ha0 : 0 < a := hA0.trans_le hAa
    have hb : b ≤ 2 * a := (hbB.trans hB).trans (by linarith only [hAa])
    have hrange (t : ℝ) (ht : t ∈ Icc a b) :
        Chebyshev.psi a - b ≤ Chebyshev.psi t - t ∧
          Chebyshev.psi t - t ≤ Chebyshev.psi b - a :=
      ⟨sub_le_sub (Chebyshev.psi_mono ht.1) ht.2, sub_le_sub (Chebyshev.psi_mono ht.2) ht.1⟩
    have hlocal := abs_mass_sub_chord_le (hA.trans hAa) hab hb hrange
    change |weightedNegativeMass psiErrorKernel a b - chordMass a b| ≤ _ at hlocal
    have hden : 4 * A ^ 2 * sqrt A ≤ 4 * a ^ 2 * sqrt a :=
      mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA0.le hAa 2) (by norm_num))
        (sqrt_le_sqrt hAa) (sqrt_nonneg A) (by positivity)
    have hcoef : 3 * (b - a) ^ 2 / (4 * a ^ 2 * sqrt a) ≤ 3 * h ^ 2 / (4 * A ^ 2 * sqrt A) := by
      have hsq : (b - a) ^ 2 ≤ h ^ 2 :=
        pow_le_pow_left₀ (sub_nonneg.mpr hab.le) (hstep i hi) 2
      calc
        _ ≤ 3 * h ^ 2 / (4 * a ^ 2 * sqrt a) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num)) (by positivity)
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    have hincrement : 0 ≤ increment i :=
      add_nonneg (sub_nonneg.mpr (Chebyshev.psi_mono hab.le)) (sub_nonneg.mpr hab.le)
    calc
      _ ≤ 3 * (Chebyshev.psi b - a - (Chebyshev.psi a - b)) * (b - a) ^ 2 /
          (4 * a ^ 2 * sqrt a) := hlocal
      _ = (3 * (b - a) ^ 2 / (4 * a ^ 2 * sqrt a)) * increment i := by
        change _ = _ * (Chebyshev.psi b - Chebyshev.psi a + (b - a))
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hincrement
  calc
    _ = |∑ i ∈ range N, (weightedNegativeMass psiErrorKernel (x i) (x (i + 1)) -
        chordMass (x i) (x (i + 1)))| := by rw [← hmass, ← Finset.sum_sub_distrib]
    _ ≤ ∑ i ∈ range N, |weightedNegativeMass psiErrorKernel (x i) (x (i + 1)) -
        chordMass (x i) (x (i + 1))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range N, (3 * h ^ 2 / (4 * A ^ 2 * sqrt A)) * increment i :=
      Finset.sum_le_sum fun i hi => herror i (Finset.mem_range.mp hi)
    _ = _ := by
      rw [← Finset.mul_sum]
      simp only [increment, Finset.sum_add_distrib]
      rw [Finset.sum_range_sub (fun i => Chebyshev.psi (x i)) N, Finset.sum_range_sub x N, hx0, hxN]
      ring

/-- Mesh widths at most `η * A^(3/4)` give a uniform error on any block
ending at or before `2 * A`. -/
theorem abs_mass_sub_mesh_le_nine_mul_sq {A B h η : ℝ} {N : ℕ} {x : ℕ → ℝ}
    (hA : exp 1 ≤ A) (hB : B ≤ 2 * A) (hx0 : x 0 = A) (hxN : x N = B)
    (hmono : StrictMonoOn x (Iic N)) (hstep : ∀ i < N, x (i + 1) - x i ≤ h)
    (hscale : h ≤ η * A ^ (3 / 4 : ℝ)) :
    |weightedNegativeMass psiErrorKernel A B -
        (∑ i ∈ range N, chordMass (x i) (x (i + 1)))| ≤ 9 * η ^ 2 := by
  by_cases hN : N = 0
  · subst N
    have hBA : B = A := hxN.symm.trans hx0
    rw [hBA]
    simp only [Finset.range_zero, Finset.sum_empty, weightedNegativeMass,
      intervalIntegral.integral_same, sub_zero, abs_zero]
    positivity
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  have h01 : x 0 < x 1 :=
    hmono (mem_Iic.mpr (Nat.zero_le N)) (mem_Iic.mpr hNpos) Nat.zero_lt_one
  have hh : 0 ≤ h := (sub_nonneg.mpr h01.le).trans (hstep 0 hNpos)
  have hA0 : 0 < A := (exp_pos 1).trans_le hA
  have hAB : A ≤ B := by
    rw [← hx0, ← hxN]
    exact hmono.monotoneOn (mem_Iic.mpr (Nat.zero_le N)) (mem_Iic.mpr le_rfl) (Nat.zero_le N)
  have hbudget0 : 0 ≤ Chebyshev.psi B - Chebyshev.psi A + B - A := by
    linarith only [Chebyshev.psi_mono hAB, hAB]
  have hlog : log 4 ≤ (3 / 2 : ℝ) := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    linarith only [Real.log_two_lt_d9]
  have hpsi : Chebyshev.psi B ≤ (11 / 2 : ℝ) * B :=
    (Chebyshev.psi_le_const_mul_self (hA0.le.trans hAB)).trans
      (mul_le_mul_of_nonneg_right (by linarith only [hlog]) (hA0.le.trans hAB))
  have hbudget : Chebyshev.psi B - Chebyshev.psi A + B - A ≤ 12 * A := by
    linarith only [hpsi, Chebyshev.psi_nonneg A, hB]
  have hpower : (A ^ (3 / 4 : ℝ)) ^ 2 = A * sqrt A := by
    rw [← Real.rpow_two, ← Real.rpow_mul hA0.le, Real.sqrt_eq_rpow]
    rw [show (3 / 4 : ℝ) * 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hA0, Real.rpow_one]
  have hsq : h ^ 2 ≤ η ^ 2 * (A * sqrt A) := calc
    _ ≤ (η * A ^ (3 / 4 : ℝ)) ^ 2 := pow_le_pow_left₀ hh hscale 2
    _ = _ := by rw [mul_pow, hpower]
  have hcoef : 3 * h ^ 2 / (4 * A ^ 2 * sqrt A) ≤ 3 * η ^ 2 / (4 * A) := calc
    _ ≤ 3 * (η ^ 2 * (A * sqrt A)) / (4 * A ^ 2 * sqrt A) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num)) (by positivity)
    _ = _ := by field_simp [hA0.ne', (sqrt_pos.2 hA0).ne'] <;> ring
  calc
    _ ≤ (3 * h ^ 2 / (4 * A ^ 2 * sqrt A)) * (Chebyshev.psi B - Chebyshev.psi A + B - A) :=
      abs_mass_sub_mesh_le hA hB hx0 hxN hmono hstep
    _ ≤ (3 * η ^ 2 / (4 * A)) * (12 * A) := mul_le_mul hcoef hbudget hbudget0 (by positivity)
    _ = _ := by field_simp [hA0.ne'] <;> ring

end
end D5.S3.Weil.Mertens.RobinFiniteMesh
