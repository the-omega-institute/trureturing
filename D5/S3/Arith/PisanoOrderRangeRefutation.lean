/- GID: D5/S3/Arith/PisanoOrderRangeRefutation
   generality: I
   mirror-B: D5/B/S3/Arith/PisanoOrderRangeRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/PisanoOrderRangeRefutation.claim; result=D5/S3/Arith/PisanoOrderRangeRefutation.result; claim=D5/S3/Arith/PisanoOrderRangeRefutation.claim
   digest: A Lucas sequence mod thirteen has three zeros per period, outside the conjectured range. -/

import D5.S1.Recurrence.LucasEvenDescent
import D5.S1.Recurrence.LucasCompanion
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.PisanoOrderRangeRefutation

open D5.S1.Recurrence.LucasEvenDescent
open D5.S1.Recurrence.LucasCompanion

/-- The number of zeros in one Pisano period. The frozen zero-index theorem says
that zeros occur exactly at multiples of `entryPoint`; since a period returns to
zero, the entry point divides the period, so this quotient counts those multiples
in the half-open interval from zero to the period. -/
noncomputable def pisanoOrder {m : ℕ} (p : ZMod m) (q : (ZMod m)ˣ) : ℕ :=
  matrixPeriod p q / entryPoint p q

/-- Benfield--Lippard, arXiv:2407.20048v2, Conjecture 5.3(v), restricted to the
purely periodic case where `b` is invertible modulo `m`. The paper's parameters
are `(p, q) = (a, -b)`, and the absolute-value hypothesis is written without
natural subtraction. Refuting this restriction refutes the published clause. -/
def claim : Prop :=
  ∀ (a b : ℤ) (m : ℕ) (q : (ZMod m)ˣ),
    1 < m → b ≠ 1 → b ≠ -1 → a.natAbs = b.natAbs + 1 →
    (q : ZMod m) = -(b : ZMod m) →
    pisanoOrder ((a : ℤ) : ZMod m) q ∈ ({0, 1, 2} : Set ℕ)

/-- At `(a, b, m) = (3, 2, 13)`, the entry point is four and the period is twelve,
so the order is three, outside the conjectured range. -/
theorem result : ¬ claim := by
  let q : (ZMod 13)ˣ :=
    { val := -2
      inv := 6
      val_inv := by decide
      inv_val := by decide }
  have hzero : lucasU (3 : ZMod 13) q 0 = 0 :=
    (lucas_recurrence (3 : ZMod 13) q).1
  have hone : lucasU (3 : ZMod 13) q 1 = 1 :=
    (lucas_recurrence (3 : ZMod 13) q).2.1
  have hrec := (lucas_recurrence (3 : ZMod 13) q).2.2
  have htwo : lucasU (3 : ZMod 13) q 2 = 3 := by
    have h := hrec 0
    norm_num [hzero, hone] at h
    exact h
  have hthree : lucasU (3 : ZMod 13) q 3 = 11 := by
    have h := hrec 1
    norm_num [q, hone, htwo] at h
    exact h
  have hfour : lucasU (3 : ZMod 13) q 4 = 0 := by
    have h := hrec 2
    norm_num [q, htwo, hthree] at h
    exact h
  have hdivInt : (entryPoint (3 : ZMod 13) q : ℤ) ∣ 4 :=
    (lucas_eq_zero_iff_entry_dvd (3 : ZMod 13) q 4).mp hfour
  have hdiv : entryPoint (3 : ZMod 13) q ∣ 4 := by
    exact_mod_cast hdivInt
  have hpos : 0 < entryPoint (3 : ZMod 13) q :=
    (entry_point_spec (3 : ZMod 13) q).1
  have hle : entryPoint (3 : ZMod 13) q ≤ 4 :=
    Nat.le_of_dvd (by decide : 0 < 4) hdiv
  have hneOne : entryPoint (3 : ZMod 13) q ≠ 1 := by
    intro he
    have hz : lucasU (3 : ZMod 13) q 1 = 0 :=
      (lucas_eq_zero_iff_entry_dvd (3 : ZMod 13) q 1).mpr (by
        rw [he]
        norm_num)
    rw [hone] at hz
    exact absurd hz (by decide)
  have hneTwo : entryPoint (3 : ZMod 13) q ≠ 2 := by
    intro he
    have hz : lucasU (3 : ZMod 13) q 2 = 0 :=
      (lucas_eq_zero_iff_entry_dvd (3 : ZMod 13) q 2).mpr (by
        rw [he]
        norm_num)
    rw [htwo] at hz
    exact absurd hz (by decide)
  have hneThree : entryPoint (3 : ZMod 13) q ≠ 3 := by
    intro he
    rw [he] at hdiv
    norm_num at hdiv
  have hentry : entryPoint (3 : ZMod 13) q = 4 := by
    omega
  have hperiod : matrixPeriod (3 : ZMod 13) q = 12 := by
    change orderOf (companion (3 : ZMod 13) q) = 12
    apply (orderOf_eq_iff (by decide : 0 < 12)).mpr
    constructor
    · rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one]
      simp only [companion, q, neg_neg]
      decide +kernel
    · intro n hn hnpos
      rw [Ne, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one]
      simp only [companion, q, neg_neg]
      interval_cases n <;> decide +kernel
  have horder : pisanoOrder (3 : ZMod 13) q = 3 := by
    rw [pisanoOrder, hperiod, hentry]
  intro hclaim
  have hmem := hclaim 3 2 13 q (by decide) (by decide) (by decide)
    (by decide) (by norm_num [q])
  norm_num [horder] at hmem

end D5.S3.Arith.PisanoOrderRangeRefutation
