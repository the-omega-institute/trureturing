/- GID: D5/S3/Arith/Precision/PrimePowerPrecisionBlindSpot
   generality: G
   mirror-B: D5/B/S3/Arith/Precision/PrimePowerPrecisionBlindSpot
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime-power agreement and its first separating precision follow the integer valuation. -/

import D5.S3.Arith.Congruence.PadicPrecisionBlindSpot

/- Library-search audit trail (2026-09-03):
   * Repository search found the frozen exact primitives `precisionReading`,
     `precision_reading_eq_iff_le_padicValInt`, and
     `first_distinguishing_precision` in `PadicPrecisionBlindSpot`; this module
     imports and applies them rather than proving the divisibility facts again.
   * Pinned Mathlib supplies the underlying `Int.modEq_iff_dvd`,
     `padicValInt_dvd_iff`, `Nat.find_spec`, and `Nat.find_min'` APIs.
   * Loogle and GitHub code search found Mathlib and downstream uses of those
     APIs, but no exact combined observer theorem outside this repository. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Precision.PrimePowerPrecisionBlindSpot

open D5.S3.Arith.Congruence.PadicPrecisionBlindSpot

private theorem positive_distinguishing_precision_exists (p : Nat) (x y : Int)
    (hp : p.Prime) (hxy : x ≠ y) :
    ∃ k : Nat, 1 <= k ∧ precisionReading p k x ≠ precisionReading p k y := by
  have hleast := first_distinguishing_precision p x y hp hxy
  exact ⟨padicValInt p (x - y) + 1, by omega, hleast.1⟩

/-- The source's `kappa_p(x,y)`: the least positive precision at which the
prime-power residue readings differ (source lines 1963-1970). -/
noncomputable def firstDistinguishingPrecision (p : Nat) (x y : Int)
    (hp : p.Prime) (hxy : x ≠ y) : Nat :=
  Nat.find (positive_distinguishing_precision_exists p x y hp hxy)

/-- For a fixed prime, positive precision, and distinct integers, agreement
lasts exactly through the valuation of the difference, and the first
distinguishing precision is its successor (source lines 9073-9096). -/
theorem prime_power_precision_blind_spot (p k : Nat) (x y : Int)
    (hp : p.Prime) (_hk : 1 <= k) (hxy : x ≠ y) :
    (precisionReading p k x = precisionReading p k y <->
      k <= padicValInt p (x - y)) ∧
    firstDistinguishingPrecision p x y hp hxy =
      padicValInt p (x - y) + 1 := by
  refine ⟨precision_reading_eq_iff_le_padicValInt p k x y hp hxy, ?_⟩
  have hleast := first_distinguishing_precision p x y hp hxy
  let existence := positive_distinguishing_precision_exists p x y hp hxy
  change Nat.find existence = padicValInt p (x - y) + 1
  apply Nat.le_antisymm
  · exact Nat.find_min' existence ⟨by omega, hleast.1⟩
  · exact hleast.2 (Nat.find_spec existence).2

/- Satisfiability probe: 4 and 0 agree modulo 2^2 and first differ modulo 2^3. -/
example :
    precisionReading 2 2 4 = precisionReading 2 2 0 ∧
      firstDistinguishingPrecision 2 4 0 (by decide) (by norm_num) = 3 := by
  have hp : Nat.Prime 2 := by decide
  have hxy : (4 : Int) ≠ 0 := by norm_num
  have h := prime_power_precision_blind_spot 2 2 4 0 hp (by norm_num) hxy
  have hsame : precisionReading 2 2 4 = precisionReading 2 2 0 := by
    norm_num [precisionReading]
  have hdiff : precisionReading 2 3 4 ≠ precisionReading 2 3 0 := by
    norm_num [precisionReading]
  have hval : padicValInt 2 ((4 : Int) - 0) = 2 := by
    have hlower := h.1.mp hsame
    have hupper : ¬3 <= padicValInt 2 ((4 : Int) - 0) := by
      intro hthree
      exact hdiff
        ((precision_reading_eq_iff_le_padicValInt 2 3 4 0 hp hxy).mpr hthree)
    omega
  constructor
  · exact hsame
  · calc
      firstDistinguishingPrecision 2 4 0 (by decide) (by norm_num) =
          padicValInt 2 (4 - 0) + 1 :=
        prime_power_precision_blind_spot 2 2 4 0 (by decide) (by norm_num)
          (by norm_num) |>.2
      _ = 3 := by omega

/- Reverse probe: both CAS assertions are independently projected from the
public conjunction. -/
example (p k : Nat) (x y : Int) (hp : p.Prime) (_hk : 1 <= k) (hxy : x ≠ y)
    (h : (precisionReading p k x = precisionReading p k y <->
        k <= padicValInt p (x - y)) ∧
      firstDistinguishingPrecision p x y hp hxy =
        padicValInt p (x - y) + 1) :
    (k <= padicValInt p (x - y) ->
      precisionReading p k x = precisionReading p k y) ∧
    firstDistinguishingPrecision p x y hp hxy =
      padicValInt p (x - y) + 1 :=
  ⟨h.1.mpr, h.2⟩

#print axioms prime_power_precision_blind_spot

end D5.S3.Arith.Precision.PrimePowerPrecisionBlindSpot
