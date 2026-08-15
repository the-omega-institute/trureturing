/- GID: D5/S0/Asymptotics/EscapeProbability/UnitProbabilityCharacterization
   generality: G
   mirror-B: D5/B/S0/Asymptotics/EscapeProbability/UnitProbabilityCharacterization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Unit escape probability characterizes fixed-point-free twists. -/

/- Library-search audit trail (2026-08-15):
   * Repository searches for an escape-probability-one characterization found
     only the sufficient direction `fixed_point_free_escape_probability_eq_one`.
   * The full capture-count distribution was also absent, but proving it would
     require a new weighted-profile decomposition rather than this public-API bridge.
   * Pinned Mathlib provides `pow_eq_one_iff_of_nonneg`, `sub_eq_self`, and
     `div_eq_zero_iff`; all three are applied below to the frozen closed form.
-/

import D5.S0.Asymptotics.EscapeProbability.PoissonDomainLimit

namespace D5.S0.Asymptotics.EscapeProbability.UnitProbabilityCharacterization

open D5.S0.Asymptotics.FixedPointFreeEscapeProbability
open D5.S0.Asymptotics.EscapeProbability.PoissonDomainLimit

/-- On a nonempty finite address set, uniform escape probability is one exactly
when the twist has no fixed points. -/
theorem escape_probability_eq_one_iff_fixed_point_free
    {Y : Type*} [Fintype Y] [Nonempty Y]
    (f : Y -> Y) (A : Nat) (hA : 0 < A) :
    escapeProbability (A := Fin A) f = 1 <->
      Nat.card {y : Y // f y = y} = 0 := by
  classical
  constructor
  · intro hprob
    rw [escape_probability_closed_form] at hprob
    have hk : Nat.card {y : Y // f y = y} <= Fintype.card Y := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_subtype_le _
    have hkpow :
        Nat.card {y : Y // f y = y} <= Fintype.card Y ^ A :=
      hk.trans (Nat.le_pow (a := Fintype.card Y) (b := A) (by omega))
    have hdenpos : 0 < (Fintype.card Y : Real) ^ A := by positivity
    have hnonneg :
        0 <= 1 - (Nat.card {y : Y // f y = y} : Real) /
          (Fintype.card Y : Real) ^ A := by
      rw [sub_nonneg, div_le_one hdenpos]
      exact_mod_cast hkpow
    have hbase :
        1 - (Nat.card {y : Y // f y = y} : Real) /
          (Fintype.card Y : Real) ^ A = 1 :=
      (pow_eq_one_iff_of_nonneg hnonneg hA.ne').mp hprob
    have hratio :
        (Nat.card {y : Y // f y = y} : Real) /
          (Fintype.card Y : Real) ^ A = 0 :=
      sub_eq_self.mp hbase
    have hkcast : (Nat.card {y : Y // f y = y} : Real) = 0 :=
      (div_eq_zero_iff.mp hratio).resolve_right hdenpos.ne'
    exact Nat.cast_eq_zero.mp hkcast
  · intro hfix
    letI : Nonempty (Fin A) := Fin.pos_iff_nonempty.mp hA
    exact fixed_point_free_escape_probability_eq_one (A := Fin A) f hfix

/- The hypotheses are jointly inhabited by Boolean negation on one address. -/
example :
    escapeProbability (A := Fin 1) Bool.not = 1 <->
      Nat.card {y : Bool // Bool.not y = y} = 0 := by
  exact escape_probability_eq_one_iff_fixed_point_free Bool.not 1 (by norm_num)

#print axioms escape_probability_eq_one_iff_fixed_point_free

end D5.S0.Asymptotics.EscapeProbability.UnitProbabilityCharacterization
