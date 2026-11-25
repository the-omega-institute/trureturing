/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/FourGapPowerSeries
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Power-series partial fractions for the four-slot word kernel. -/

import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap
import Mathlib.RingTheory.PowerSeries.WellKnown

/-! Cleared partial fractions for four geometric factors. -/

open scoped BigOperators

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum

noncomputable section

abbrev Series := PowerSeries ℝ

/-- The inverse of the positive power of a linear pole denominator. -/
def pole (a : ℝ) (multiplicity : ℕ) : Series :=
  PowerSeries.rescale a (PowerSeries.invOneSubPow ℝ multiplicity).val

theorem coeff_pole_succ (a : ℝ) (p m : ℕ) :
    PowerSeries.coeff p (pole a (m+1)) = a^p * ((m+p).choose m : ℝ) := by
  simp [pole, PowerSeries.coeff_rescale, PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]

private theorem coeff_pole_one (a : ℝ) (p : ℕ) :
    PowerSeries.coeff p (pole a 1) = a^p := by
  simpa using coeff_pole_succ a p 0

theorem pole_add (a : ℝ) (m n : ℕ) : pole a (m+n) = pole a m * pole a n := by
  simp [pole, PowerSeries.invOneSubPow_add, Units.val_mul]

theorem pole_mul_denominator (a : ℝ) (m : ℕ) :
    pole a m * (1 - PowerSeries.C a * PowerSeries.X)^m = 1 := by
  have hinv := (PowerSeries.invOneSubPow ℝ m).val_inv
  rw [PowerSeries.invOneSubPow_inv_eq_one_sub_pow] at hinv
  simpa [pole, PowerSeries.rescale_X] using congrArg (PowerSeries.rescale a) hinv

private def linearDenominator (a : ℝ) : Series :=
  1 - PowerSeries.C a * PowerSeries.X

private theorem pole_cancel_power (a : ℝ) (m n : ℕ) :
    pole a (m+n) * linearDenominator a ^ n = pole a m := by
  rw [pole_add, mul_assoc]
  rw [show pole a n * linearDenominator a ^ n = 1 from pole_mul_denominator a n, mul_one]

/-- The cleared partial fractions for a triple pole and a simple pole. -/
theorem pole_three_one (a b : ℝ) :
    PowerSeries.C ((a-b)^3) * (pole a 3 * pole b 1) =
      PowerSeries.C (a*(a-b)^2) * pole a 3 -
      PowerSeries.C (a*b*(a-b)) * pole a 2 +
      PowerSeries.C (a*b^2) * pole a 1 -
      PowerSeries.C (b^3) * pole b 1 := by
  let A := linearDenominator a
  let B := linearDenominator b
  let F := pole a 3 * pole b 1
  have hb : pole b 1 * B = 1 := by simpa [B, linearDenominator] using pole_mul_denominator b 1
  have ha3 : pole a 3 * A^3 = 1 := pole_mul_denominator a 3
  have ha2 : pole a 3 * A^2 = pole a 1 := pole_cancel_power a 1 2
  have ha1 : pole a 3 * A = pole a 2 := by simpa using pole_cancel_power a 2 1
  have hB : F * B = pole a 3 := by dsimp [F]; rw [mul_assoc, hb, mul_one]
  have hAB : F * A * B = pole a 2 := by
    calc
      F * A * B = (F * B) * A := by ring
      _ = _ := by rw [hB, ha1]
  have hA2B : F * A^2 * B = pole a 1 := by
    calc
      F * A^2 * B = (F * B) * A^2 := by ring
      _ = _ := by rw [hB, ha2]
  have hA3 : F * A^3 = pole b 1 := by
    calc
      F * A^3 = (pole a 3 * A^3) * pole b 1 := by dsimp [F]; ring
      _ = _ := by rw [ha3, one_mul]
  have hidentity : (PowerSeries.C ((a-b)^3) : Series) =
      PowerSeries.C (a*(a-b)^2) * B -
      PowerSeries.C (a*b*(a-b)) * A * B +
      PowerSeries.C (a*b^2) * A^2 * B -
      PowerSeries.C (b^3) * A^3 := by
    dsimp [A, B, linearDenominator]
    simp only [map_pow, map_mul, map_sub]
    ring
  change PowerSeries.C ((a-b)^3) * F = _
  rw [hidentity]
  calc
    _ = PowerSeries.C (a*(a-b)^2) * (F * B) -
        PowerSeries.C (a*b*(a-b)) * (F * A * B) +
        PowerSeries.C (a*b^2) * (F * A^2 * B) -
        PowerSeries.C (b^3) * (F * A^3) := by ring
    _ = _ := by rw [hB, hAB, hA2B, hA3]

/-- The cleared partial fractions for two double poles. -/
theorem pole_two_two (a b : ℝ) :
    PowerSeries.C ((a-b)^3) * (pole a 2 * pole b 2) =
      PowerSeries.C (a^2*(a-b)) * pole a 2 -
      PowerSeries.C (2*a^2*b) * pole a 1 +
      PowerSeries.C (b^2*(a-b)) * pole b 2 +
      PowerSeries.C (2*b^2*a) * pole b 1 := by
  let A := linearDenominator a
  let B := linearDenominator b
  let F := pole a 2 * pole b 2
  have ha : pole a 2 * A^2 = 1 := pole_mul_denominator a 2
  have hb : pole b 2 * B^2 = 1 := pole_mul_denominator b 2
  have ha1 : pole a 2 * A = pole a 1 := by simpa using pole_cancel_power a 1 1
  have hb1 : pole b 2 * B = pole b 1 := by simpa using pole_cancel_power b 1 1
  have hA : F * A^2 = pole b 2 := by
    calc
      F * A^2 = (pole a 2 * A^2) * pole b 2 := by dsimp [F]; ring
      _ = _ := by rw [ha, one_mul]
  have hB : F * B^2 = pole a 2 := by dsimp [F]; rw [mul_assoc, hb, mul_one]
  have hAB : F * A * B^2 = pole a 1 := by
    calc
      F * A * B^2 = (F * B^2) * A := by ring
      _ = _ := by rw [hB, ha1]
  have hidentity : (PowerSeries.C ((a-b)^3) : Series) =
      PowerSeries.C (a^2*(a-b)) * B^2 -
      PowerSeries.C (2*a^2*b) * A * B^2 +
      PowerSeries.C (b^2*(a-b)) * A^2 +
      PowerSeries.C (2*b^2*a) * A^2 * B := by
    dsimp [A, B, linearDenominator]
    simp only [map_pow, map_sub, map_mul, map_ofNat]
    ring
  change PowerSeries.C ((a-b)^3) * F = _
  rw [hidentity]
  calc
    _ = PowerSeries.C (a^2*(a-b)) * (F * B^2) -
        PowerSeries.C (2*a^2*b) * (F * A * B^2) +
        PowerSeries.C (b^2*(a-b)) * (F * A^2) +
        PowerSeries.C (2*b^2*a) * (F * A^2 * B) := by ring
    _ = _ := by rw [hB, hAB, hA, hb1]

/-- The cleared partial fractions for a double pole and two simple poles. -/
theorem pole_two_one_one (a b c : ℝ) :
    PowerSeries.C ((a-b)^2*(a-c)^2*(b-c)) * (pole a 2 * (pole b 1 * pole c 1)) =
      PowerSeries.C (a^2*(a-b)*(a-c)*(b-c)) * pole a 2 -
      PowerSeries.C (a^2*(b*(a-c)+c*(a-b))*(b-c)) * pole a 1 +
      PowerSeries.C (b^3*(a-c)^2) * pole b 1 -
      PowerSeries.C (c^3*(a-b)^2) * pole c 1 := by
  let A := linearDenominator a
  let B := linearDenominator b
  let C := linearDenominator c
  let F := pole a 2 * (pole b 1 * pole c 1)
  have ha : pole a 2 * A^2 = 1 := pole_mul_denominator a 2
  have hb : pole b 1 * B = 1 := by simpa [B, linearDenominator] using pole_mul_denominator b 1
  have hc : pole c 1 * C = 1 := by simpa [C, linearDenominator] using pole_mul_denominator c 1
  have ha1 : pole a 2 * A = pole a 1 := by simpa using pole_cancel_power a 1 1
  have hBC : F * B * C = pole a 2 := by
    calc
      F * B * C = pole a 2 * ((pole b 1 * B) * (pole c 1 * C)) := by
        dsimp [F]
        ring
      _ = _ := by rw [hb, hc, mul_one, mul_one]
  have hABC : F * A * B * C = pole a 1 := by
    calc
      F * A * B * C = (F * B * C) * A := by ring
      _ = _ := by rw [hBC, ha1]
  have hAC : F * A^2 * C = pole b 1 := by
    calc
      F * A^2 * C = pole b 1 * ((pole a 2 * A^2) * (pole c 1 * C)) := by
        dsimp [F]
        ring
      _ = _ := by rw [ha, hc, mul_one, mul_one]
  have hAB : F * A^2 * B = pole c 1 := by
    calc
      F * A^2 * B = pole c 1 * ((pole a 2 * A^2) * (pole b 1 * B)) := by
        dsimp [F]
        ring
      _ = _ := by rw [ha, hb, mul_one, mul_one]
  have hidentity : (PowerSeries.C ((a-b)^2*(a-c)^2*(b-c)) : Series) =
      PowerSeries.C (a^2*(a-b)*(a-c)*(b-c)) * B * C -
      PowerSeries.C (a^2*(b*(a-c)+c*(a-b))*(b-c)) * A * B * C +
      PowerSeries.C (b^3*(a-c)^2) * A^2 * C -
      PowerSeries.C (c^3*(a-b)^2) * A^2 * B := by
    dsimp [A, B, C, linearDenominator]
    simp only [map_pow, map_sub, map_mul, map_add]
    ring
  change PowerSeries.C ((a-b)^2*(a-c)^2*(b-c)) * F = _
  rw [hidentity]
  calc
    _ = PowerSeries.C (a^2*(a-b)*(a-c)*(b-c)) * (F * B * C) -
        PowerSeries.C (a^2*(b*(a-c)+c*(a-b))*(b-c)) * (F * A * B * C) +
        PowerSeries.C (b^3*(a-c)^2) * (F * A^2 * C) -
        PowerSeries.C (c^3*(a-b)^2) * (F * A^2 * B) := by ring
    _ = _ := by rw [hBC, hABC, hAC, hAB]

/-- The cleared partial fractions of a product of four simple poles. -/
theorem pole_one_one_one_one (a b c d : ℝ) :
    PowerSeries.C ((a-b)*(a-c)*(a-d)*(b-c)*(b-d)*(c-d)) *
        (pole a 1 * (pole b 1 * (pole c 1 * pole d 1))) =
      PowerSeries.C (a^3*(b-c)*(b-d)*(c-d)) * pole a 1 -
      PowerSeries.C (b^3*(a-c)*(a-d)*(c-d)) * pole b 1 +
      PowerSeries.C (c^3*(a-b)*(a-d)*(b-d)) * pole c 1 -
      PowerSeries.C (d^3*(a-b)*(a-c)*(b-c)) * pole d 1 := by
  let A := linearDenominator a
  let B := linearDenominator b
  let C := linearDenominator c
  let D := linearDenominator d
  let F := pole a 1 * (pole b 1 * (pole c 1 * pole d 1))
  have ha : pole a 1 * A = 1 := by
    simpa only [A, linearDenominator, pow_one] using pole_mul_denominator a 1
  have hb : pole b 1 * B = 1 := by
    simpa only [B, linearDenominator, pow_one] using pole_mul_denominator b 1
  have hc : pole c 1 * C = 1 := by
    simpa only [C, linearDenominator, pow_one] using pole_mul_denominator c 1
  have hd : pole d 1 * D = 1 := by
    simpa only [D, linearDenominator, pow_one] using pole_mul_denominator d 1
  have hBCD : F * (B*C*D) = pole a 1 := by
    calc
      _ = pole a 1 * ((pole b 1 * B) * (pole c 1 * C) * (pole d 1 * D)) := by
        dsimp [F]
        ring
      _ = _ := by rw [hb, hc, hd]; simp
  have hACD : F * (A*C*D) = pole b 1 := by
    calc
      _ = pole b 1 * ((pole a 1 * A) * (pole c 1 * C) * (pole d 1 * D)) := by
        dsimp [F]
        ring
      _ = _ := by rw [ha, hc, hd]; simp
  have hABD : F * (A*B*D) = pole c 1 := by
    calc
      _ = pole c 1 * ((pole a 1 * A) * (pole b 1 * B) * (pole d 1 * D)) := by
        dsimp [F]
        ring
      _ = _ := by rw [ha, hb, hd]; simp
  have hABC : F * (A*B*C) = pole d 1 := by
    calc
      _ = pole d 1 * ((pole a 1 * A) * (pole b 1 * B) * (pole c 1 * C)) := by
        dsimp [F]
        ring
      _ = _ := by rw [ha, hb, hc]; simp
  have hpoly : (PowerSeries.C ((a-b)*(a-c)*(a-d)*(b-c)*(b-d)*(c-d)) : Series) =
      PowerSeries.C (a^3*(b-c)*(b-d)*(c-d)) * (B*C*D) -
      PowerSeries.C (b^3*(a-c)*(a-d)*(c-d)) * (A*C*D) +
      PowerSeries.C (c^3*(a-b)*(a-d)*(b-d)) * (A*B*D) -
      PowerSeries.C (d^3*(a-b)*(a-c)*(b-c)) * (A*B*C) := by
    dsimp [A, B, C, D, linearDenominator]
    simp only [map_pow, map_mul, map_sub]
    ring
  change PowerSeries.C ((a-b)*(a-c)*(a-d)*(b-c)*(b-d)*(c-d)) * F = _
  rw [hpoly]
  calc
    _ = PowerSeries.C (a^3*(b-c)*(b-d)*(c-d)) * (F * (B*C*D)) -
        PowerSeries.C (b^3*(a-c)*(a-d)*(c-d)) * (F * (A*C*D)) +
        PowerSeries.C (c^3*(a-b)*(a-d)*(b-d)) * (F * (A*B*D)) -
        PowerSeries.C (d^3*(a-b)*(a-c)*(b-c)) * (F * (A*B*C)) := by ring
    _ = _ := by rw [hBCD, hACD, hABD, hABC]

open private FourCopyGap.sum_gaps_nested FourCopyGap.monomial FourCopyGap.balanced
  from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap in
/-- The coefficient of the product of four geometric series is the positive
part of the cyclic word's scalar comparison kernel. -/
theorem gapDefect_eq_coeff_poles (p : ℕ) (a b c d : ℝ) :
    FourCopyGap.gapDefect p a b c d =
      PowerSeries.coeff p (pole a 1 * (pole b 1 * (pole c 1 * pole d 1))) -
        (FourCopyGap.gaps p).card * FourCopyGap.balanced p a b c d := by
  unfold FourCopyGap.gapDefect
  congr 1
  rw [FourCopyGap.sum_gaps_nested]
  simp only [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    coeff_pole_one, Finset.mul_sum, FourCopyGap.monomial]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

private theorem coeff_pole_two (a : ℝ) (p : ℕ) :
    PowerSeries.coeff p (pole a 2) = a^p * (p+1 : ℝ) := by
  simpa [add_comm] using coeff_pole_succ a p 1

private theorem coeff_pole_three (a : ℝ) (p : ℕ) :
    PowerSeries.coeff p (pole a 3) = a^p * ((p+2).choose 2 : ℝ) := by
  simpa [add_comm] using coeff_pole_succ a p 2

open private FourCopyGap.balanced
  from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap

theorem cleared_gap_three_one (p : ℕ) (a b : ℝ) :
    (a-b)^3 * FourCopyGap.gapDefect p a a a b =
      a*(a-b)^2 * (a^p * ((p+2).choose 2 : ℝ)) -
      a*b*(a-b) * (a^p * (p+1 : ℝ)) + a*b^2*a^p - b^3*b^p -
      (a-b)^3 * ((FourCopyGap.gaps p).card * FourCopyGap.balanced p a a a b) := by
  have hcoeff := congrArg (PowerSeries.coeff p) (pole_three_one a b)
  simp only [PowerSeries.coeff_C_mul, map_add, map_sub, coeff_pole_one,
    coeff_pole_two, coeff_pole_three] at hcoeff
  have htwo : pole a 2 = pole a 1 * pole a 1 := pole_add a 1 1
  have hthree : pole a 3 = pole a 1 * (pole a 1 * pole a 1) := by
    calc
      pole a 3 = pole a 1 * pole a 2 := pole_add a 1 2
      _ = _ := by rw [htwo]
  rw [gapDefect_eq_coeff_poles, mul_sub]
  rw [show pole a 1 * (pole a 1 * (pole a 1 * pole b 1)) = pole a 3 * pole b 1 by
    rw [hthree]
    ring, hcoeff]

theorem cleared_gap_two_two (p : ℕ) (a b : ℝ) :
    (a-b)^3 * FourCopyGap.gapDefect p a a b b =
      a^2*(a-b) * (a^p * (p+1 : ℝ)) - 2*a^2*b*a^p +
      b^2*(a-b) * (b^p * (p+1 : ℝ)) + 2*b^2*a*b^p -
      (a-b)^3 * ((FourCopyGap.gaps p).card * FourCopyGap.balanced p a a b b) := by
  have hcoeff := congrArg (PowerSeries.coeff p) (pole_two_two a b)
  simp only [PowerSeries.coeff_C_mul, map_add, map_sub, coeff_pole_one,
    coeff_pole_two] at hcoeff
  rw [gapDefect_eq_coeff_poles, mul_sub]
  rw [show pole a 1 * (pole a 1 * (pole b 1 * pole b 1)) = pole a 2 * pole b 2 by
    rw [pole_add a 1 1, pole_add b 1 1]
    ring, hcoeff]

theorem cleared_gap_two_one_one (p : ℕ) (a b c : ℝ) :
    ((a-b)^2*(a-c)^2*(b-c)) * FourCopyGap.gapDefect p a a b c =
      a^2*(a-b)*(a-c)*(b-c) * (a^p * (p+1 : ℝ)) -
      a^2*(b*(a-c)+c*(a-b))*(b-c)*a^p +
      b^3*(a-c)^2*b^p - c^3*(a-b)^2*c^p -
      ((a-b)^2*(a-c)^2*(b-c)) *
        ((FourCopyGap.gaps p).card * FourCopyGap.balanced p a a b c) := by
  have hcoeff := congrArg (PowerSeries.coeff p) (pole_two_one_one a b c)
  simp only [PowerSeries.coeff_C_mul, map_add, map_sub, coeff_pole_one,
    coeff_pole_two] at hcoeff
  rw [gapDefect_eq_coeff_poles, mul_sub]
  rw [show pole a 1 * (pole a 1 * (pole b 1 * pole c 1)) = pole a 2 * (pole b 1 * pole c 1) by
    rw [pole_add a 1 1, mul_assoc], hcoeff]

/-- The contribution of each node to the scalar word deficit with four
distinct spectral slots, after clearing the common denominator. -/
theorem cleared_gap_one_one_one_one (p : ℕ) (a b c d : ℝ) :
    ((a-b)*(a-c)*(a-d)*(b-c)*(b-d)*(c-d)) * FourCopyGap.gapDefect p a b c d =
      a^3*(b-c)*(b-d)*(c-d)*a^p - b^3*(a-c)*(a-d)*(c-d)*b^p +
      c^3*(a-b)*(a-d)*(b-d)*c^p - d^3*(a-b)*(a-c)*(b-c)*d^p -
      ((a-b)*(a-c)*(a-d)*(b-c)*(b-d)*(c-d)) *
        ((FourCopyGap.gaps p).card * FourCopyGap.balanced p a b c d) := by
  have hcoeff := congrArg (PowerSeries.coeff p) (pole_one_one_one_one a b c d)
  simp only [PowerSeries.coeff_C_mul, map_add, map_sub, coeff_pole_one] at hcoeff
  rw [gapDefect_eq_coeff_poles, mul_sub, hcoeff]

/-- The scalar gap deficit at four distinct nodes is the sum of their
simple-pole contributions minus the balanced monomial. -/
theorem gapDefect_eq_simple_poles (p : ℕ) (a b c d : ℝ)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    FourCopyGap.gapDefect p a b c d =
      a^3 / ((a-b)*(a-c)*(a-d)) * a^p +
      b^3 / ((b-a)*(b-c)*(b-d)) * b^p +
      c^3 / ((c-a)*(c-b)*(c-d)) * c^p +
      d^3 / ((d-a)*(d-b)*(d-c)) * d^p -
      ((FourCopyGap.gaps p).card : ℝ) * FourCopyGap.balanced p a b c d := by
  let Δ := (a-b)*(a-c)*(a-d)*(b-c)*(b-d)*(c-d)
  have hΔ : Δ ≠ 0 := by
    simp [Δ, mul_ne_zero_iff, sub_ne_zero, hab, hac, had, hbc, hbd, hcd]
  have scale (f t k g : ℝ) (ht : t ≠ 0) (he : Δ = t*k) :
      Δ * (f / t * g) = k*f*g := by
    rw [he]
    calc
      _ = k * (t * (f / t)) * g := by ring
      _ = _ := by rw [mul_div_cancel₀ _ ht]
  have ha := scale (a^3) ((a-b)*(a-c)*(a-d)) ((b-c)*(b-d)*(c-d)) (a^p)
    (by simp [mul_ne_zero_iff, sub_ne_zero, hab, hac, had]) (by dsimp [Δ]; ring)
  have hb := scale (b^3) ((b-a)*(b-c)*(b-d)) (-(a-c)*(a-d)*(c-d)) (b^p)
    (by simp [mul_ne_zero_iff, sub_ne_zero, hab.symm, hbc, hbd]) (by dsimp [Δ]; ring)
  have hc := scale (c^3) ((c-a)*(c-b)*(c-d)) ((a-b)*(a-d)*(b-d)) (c^p)
    (by simp [mul_ne_zero_iff, sub_ne_zero, hac.symm, hbc.symm, hcd]) (by dsimp [Δ]; ring)
  have hd := scale (d^3) ((d-a)*(d-b)*(d-c)) (-(a-b)*(a-c)*(b-c)) (d^p)
    (by simp [mul_ne_zero_iff, sub_ne_zero, had.symm, hbd.symm, hcd.symm]) (by dsimp [Δ]; ring)
  have hcoeff := cleared_gap_one_one_one_one p a b c d
  change Δ * _ = _ at hcoeff
  apply mul_left_cancel₀ hΔ
  rw [hcoeff, mul_sub Δ, mul_add Δ, mul_add Δ, mul_add Δ, ha, hb, hc, hd]
  dsimp [Δ]
  ring

end

end RefinedBMV.ThreeBlockGram.PositiveSpectrum
