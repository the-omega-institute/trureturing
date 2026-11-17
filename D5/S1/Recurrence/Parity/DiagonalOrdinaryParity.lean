/- GID: D5/S1/Recurrence/Parity/DiagonalOrdinaryParity
   generality: I
   mirror-B: D5/B/S1/Recurrence/Parity/DiagonalOrdinaryParity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The normalized diagonal-constraint series has odd ordinary coefficients exactly at powers of two. -/

import D5.S1.Recurrence.Parity.DiagonalIterateEven
import D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity

open PowerSeries
open D5.S1.Recurrence.Parity.DiagonalIterateEven

namespace D5.S1.Recurrence.Parity.DiagonalOrdinaryParity

theorem result (n : ℕ) (_hn : 1 ≤ n) :
    Odd (coeff n generatingSeries) ↔ ∃ k : ℕ, n = 2 ^ k := by
  classical
  let P := D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.powerTwoSeries
  have hp : P + P ^ 2 = (X : PowerSeries (ZMod 2)) := by
    have h := D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.thue_series_equation.1
    have hz : (2 : PowerSeries (ZMod 2)) = 0 := by
      simpa only [map_ofNat, map_zero] using
        congrArg (C (R := ZMod 2)) (show (2 : ZMod 2) = 0 by decide)
    change P = X + P ^ 2 at h
    linear_combination h + P ^ 2 * hz
  have hh : H = P :=
    D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.quadratic_unique
      H_zero D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.power_two_zero
      (H_quadratic.trans hp.symm)
  have hc := congrArg (coeff n) (mod_two_identity.trans hh)
  rw [coeff_map] at hc
  change ((coeff n generatingSeries : ℤ) : ZMod 2) = coeff n P at hc
  rw [← ZMod.intCast_eq_one_iff_odd, hc]
  simp only [P, D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.powerTwoSeries,
    coeff_mk, ite_eq_left_iff, zero_ne_one, imp_false, not_not]

#print axioms result

end D5.S1.Recurrence.Parity.DiagonalOrdinaryParity
