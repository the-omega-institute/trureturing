/- GID: D5/S3/Arith/Congruence/PadicPrecisionBlindSpot
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/PadicPrecisionBlindSpot
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime-power readings agree through the valuation, whose successor first distinguishes. -/

import Mathlib.Data.Int.ModEq
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/- Library-search audit trail (2026-08-24):
   * `rg -n -F 'precision_reading_eq_iff_le_padicValInt' D5 Golden/Frozen/accepted`
     returned no matches. Broader repository searches for `padicValInt`, p-adic
     precision, equal prime-power residues, and least distinguishing precision
     found no public or private theorem covering either result.
   * Pinned Mathlib provides `Int.modEq_iff_dvd` and
     `padicValInt_dvd_iff`, which together give the equivalence after using
     `x ≠ y` to remove the zero-difference disjunct.
   * No Mathlib declaration found in the same searches states the least
     distinguishing precision. Its membership and minimality are proved from
     the imported divisibility equivalence and elementary natural arithmetic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Congruence.PadicPrecisionBlindSpot

/-- The precision-`k` integer reading is reduction modulo `p ^ k`. -/
def precisionReading (p k : Nat) (x : Int) : Int :=
  x % (p : Int) ^ k

/-- Two distinct integers have the same precision-`k` reading exactly when
`k` does not exceed the `p`-adic valuation of their difference. -/
theorem precision_reading_eq_iff_le_padicValInt (p k : Nat) (x y : Int)
    (hp : p.Prime) (hxy : x ≠ y) :
    precisionReading p k x = precisionReading p k y <->
      k <= padicValInt p (x - y) := by
  letI : Fact p.Prime := ⟨hp⟩
  change x ≡ y [ZMOD (p : Int) ^ k] <-> k <= padicValInt p (x - y)
  rw [Int.modEq_iff_dvd, show y - x = -(x - y) by omega, Int.dvd_neg,
    padicValInt_dvd_iff]
  exact or_iff_right_of_imp fun hzero => (hxy (sub_eq_zero.mp hzero)).elim

/-- The successor of the valuation of a nonzero difference is the least
precision at which the two integer readings differ. -/
theorem first_distinguishing_precision (p : Nat) (x y : Int)
    (hp : p.Prime) (hxy : x ≠ y) :
    IsLeast {k : Nat | precisionReading p k x ≠ precisionReading p k y}
      (padicValInt p (x - y) + 1) := by
  constructor
  · intro hequal
    have hle : padicValInt p (x - y) + 1 <= padicValInt p (x - y) :=
      (precision_reading_eq_iff_le_padicValInt p _ x y hp hxy).mp hequal
    omega
  · intro k hdistinguishes
    by_contra hnot_least
    have hk : k <= padicValInt p (x - y) := by omega
    exact hdistinguishes
      ((precision_reading_eq_iff_le_padicValInt p k x y hp hxy).mpr hk)

example :
    IsLeast {k : Nat | precisionReading 2 k 0 ≠ precisionReading 2 k 1}
      1 := by
  simpa [padicValInt] using
    (first_distinguishing_precision 2 0 1 (by decide) (by norm_num))

#print axioms precision_reading_eq_iff_le_padicValInt
#print axioms first_distinguishing_precision

end D5.S3.Arith.Congruence.PadicPrecisionBlindSpot
