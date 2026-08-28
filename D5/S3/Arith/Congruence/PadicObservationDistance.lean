/- GID: D5/S3/Arith/Congruence/PadicObservationDistance
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/PadicObservationDistance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The first unequal prime-power reading induces the p-adic distance formula. -/

import D5.S3.Arith.Congruence.PadicPrecisionBlindSpot
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic

/- Library-search audit trail (2026-08-26):
   * Searches for p-adic observation distances and for `Nat.find` applied to
     `precisionReading` found no existing D5 definition or theorem.
   * The frozen `PadicPrecisionBlindSpot` family supplies the canonical
     prime-power reading and its least distinguishing-precision theorem.
   * Pinned Mathlib supplies `Nat.find_spec` and `Nat.find_min'`, but no exact
     theorem identifying a first-readout distance with a p-adic valuation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Congruence.PadicObservationDistance

open D5.S3.Arith.Congruence.PadicPrecisionBlindSpot

private theorem distinguishing_precision_exists (p : Nat) (x y : Int)
    (hp : p.Prime) (hxy : x ≠ y) :
    ∃ k : Nat, precisionReading p k x ≠ precisionReading p k y := by
  exact ⟨padicValInt p (x - y) + 1,
    (first_distinguishing_precision p x y hp hxy).1⟩

/-- The observation distance is zero on equal integers. Otherwise it is the
prime base raised to one minus the first precision whose readings differ. -/
noncomputable def observationDistance (p : Nat) (hp : p.Prime) (x y : Int) : ℝ :=
  if hxy : x = y then 0
  else
    (p : ℝ) ^
      (1 - (Nat.find (distinguishing_precision_exists p x y hp hxy) : Int))

/-- For distinct integers, distance from the first unequal prime-power reading
is exactly the usual p-adic valuation scale. -/
theorem observation_distance_eq_padic_valuation (p : Nat) (x y : Int)
    (hp : p.Prime) (hxy : x ≠ y) :
    observationDistance p hp x y =
      (p : ℝ) ^ (-(padicValInt p (x - y) : Int)) := by
  let existence := distinguishing_precision_exists p x y hp hxy
  have hleast := first_distinguishing_precision p x y hp hxy
  have hfindLower :
      padicValInt p (x - y) + 1 ≤ Nat.find existence :=
    hleast.2 (Nat.find_spec existence)
  have hfindUpper :
      Nat.find existence ≤ padicValInt p (x - y) + 1 :=
    Nat.find_min' existence hleast.1
  have hfind : Nat.find existence = padicValInt p (x - y) + 1 :=
    Nat.le_antisymm hfindUpper hfindLower
  have hexponent :
      (1 : Int) - (padicValInt p (x - y) + 1 : Nat) =
        -(padicValInt p (x - y) : Int) := by
    omega
  simp only [observationDistance, dif_neg hxy]
  change (p : ℝ) ^ (1 - (Nat.find existence : Int)) = _
  rw [hfind, hexponent]

#print axioms observation_distance_eq_padic_valuation

end D5.S3.Arith.Congruence.PadicObservationDistance
