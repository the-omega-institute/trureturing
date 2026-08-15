/- GID: D5/S0/Asymptotics/EscapeProbability/FixedPointCountOrder
   generality: G
   mirror-B: D5/B/S0/Asymptotics/EscapeProbability/FixedPointCountOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Order.GroupWithZero.Basic]
   digest: Positive-address escape probability strictly reverses fixed-point-count order. -/

/- Library-search audit trail (2026-08-15):
   * Repository and all-local-ref searches found no theorem comparing two
     frozen escape probabilities through their fixed-point counts.
   * Pinned Mathlib provides `pow_lt_pow_iff_left₀`, the exact strict-order
     equivalence for positive natural powers on nonnegative bases.
   * Pinned Mathlib provides `div_lt_div_iff_of_pos_right`, the exact bridge
     comparing the two fixed-point ratios over their common positive denominator.
-/

import D5.S0.Asymptotics.EscapeProbability.PoissonDomainLimit
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic

namespace D5.S0.Asymptotics.EscapeProbability.FixedPointCountOrder

open D5.S0.Asymptotics.FixedPointFreeEscapeProbability
open D5.S0.Asymptotics.EscapeProbability.PoissonDomainLimit

/-- On every positive finite address set, frozen escape probability strictly
reverses the fixed-point-count order of twists on the same output alphabet. -/
theorem escape_probability_lt_iff_fixed_point_card_gt
    {Y : Type*} [Fintype Y] [Nonempty Y]
    (f g : Y -> Y) (A : Nat) (hA : 0 < A) :
    escapeProbability (A := Fin A) f < escapeProbability (A := Fin A) g <->
      Nat.card {y : Y // g y = y} < Nat.card {y : Y // f y = y} := by
  classical
  rw [escape_probability_closed_form f A, escape_probability_closed_form g A]
  let kf := Nat.card {y : Y // f y = y}
  let kg := Nat.card {y : Y // g y = y}
  let n := Fintype.card Y
  change (1 - (kf : Real) / (n : Real) ^ A) ^ A <
      (1 - (kg : Real) / (n : Real) ^ A) ^ A <-> kg < kf
  have hn : 0 < n := by
    exact Fintype.card_pos
  have hkf_le : kf <= n := by
    dsimp [kf, n]
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_le _
  have hkg_le : kg <= n := by
    dsimp [kg, n]
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_le _
  have hn_le_pow : n <= n ^ A :=
    Nat.le_pow (a := n) (b := A) (by omega)
  have hkf_pow : kf <= n ^ A := hkf_le.trans hn_le_pow
  have hkg_pow : kg <= n ^ A := hkg_le.trans hn_le_pow
  have hden : 0 < (n : Real) ^ A := by positivity
  have hbasef : 0 <= 1 - (kf : Real) / (n : Real) ^ A := by
    rw [sub_nonneg, div_le_one hden]
    exact_mod_cast hkf_pow
  have hbaseg : 0 <= 1 - (kg : Real) / (n : Real) ^ A := by
    rw [sub_nonneg, div_le_one hden]
    exact_mod_cast hkg_pow
  rw [pow_lt_pow_iff_left₀ hbasef hbaseg hA.ne']
  constructor
  · intro h
    have hdiv : (kg : Real) / (n : Real) ^ A <
        (kf : Real) / (n : Real) ^ A := by
      linarith
    have hcast : (kg : Real) < (kf : Real) :=
      (div_lt_div_iff_of_pos_right hden).mp hdiv
    exact_mod_cast hcast
  · intro h
    have hcast : (kg : Real) < (kf : Real) := by
      exact_mod_cast h
    have hdiv : (kg : Real) / (n : Real) ^ A <
        (kf : Real) / (n : Real) ^ A :=
      (div_lt_div_iff_of_pos_right hden).mpr hcast
    linarith

example : Bool := false

example :
    escapeProbability (A := Fin 2) (id : Bool -> Bool) <
      escapeProbability (A := Fin 2) Bool.not := by
  rw [escape_probability_lt_iff_fixed_point_card_gt
    (id : Bool -> Bool) Bool.not 2 (by norm_num)]
  simp [Nat.card_eq_fintype_card]

#print axioms escape_probability_lt_iff_fixed_point_card_gt

end D5.S0.Asymptotics.EscapeProbability.FixedPointCountOrder
