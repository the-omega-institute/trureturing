/- GID: D5/S0/Asymptotics/EscapeProbability/ZeroCharacterization
   generality: G
   mirror-B: D5/B/S0/Asymptotics/EscapeProbability/ZeroCharacterization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Card]
   digest: Zero escape occurs exactly for identity twists in the two finite degeneracies. -/

/- Library-search audit trail (2026-08-15):
   * Pinned Mathlib's `pow_eq_zero_iff` reduces a positive real power
     equaling zero to its base equaling zero.
   * `set_fintype_card_eq_univ_iff` identifies a full-cardinality fixed-point
     subtype with the whole output type.
   * `Function.forall_isFixedPt_iff` turns pointwise fixedness into `f = id`.
   * `Nat.pow_right_injective` identifies the exponent when the alphabet has
     at least two elements.
   * Repository and pinned-Mathlib searches found no zero-escape
     characterization for this frozen model.
-/

import D5.S0.Asymptotics.EscapeProbability.PoissonDomainLimit
import Mathlib.Tactic

namespace D5.S0.Asymptotics.EscapeProbability.ZeroCharacterization

open D5.S0.Asymptotics.FixedPointFreeEscapeProbability
open D5.S0.Asymptotics.EscapeProbability.PoissonDomainLimit

/-- The frozen escape probability vanishes exactly when the address type is
nonempty, the twist is the identity, and either there is one address or the
output alphabet is a singleton. -/
theorem escape_probability_eq_zero_iff
    {Y : Type*} [Fintype Y] [Nonempty Y] (f : Y -> Y) (A : Nat) :
    escapeProbability (A := Fin A) f = 0 <->
      0 < A ∧ f = id ∧ (A = 1 ∨ Fintype.card Y = 1) := by
  classical
  rw [escape_probability_closed_form]
  constructor
  · intro hzero
    have hA : A ≠ 0 := by
      intro h
      subst A
      simp at hzero
    have hbase :
        1 - (Nat.card {y : Y // f y = y} : Real) /
          (Fintype.card Y : Real) ^ A = 0 :=
      (pow_eq_zero_iff hA).mp hzero
    have hden : (Fintype.card Y : Real) ^ A ≠ 0 := by
      positivity
    have hratio :
        (Nat.card {y : Y // f y = y} : Real) /
          (Fintype.card Y : Real) ^ A = 1 := by
      linarith
    have hreal :
        (Nat.card {y : Y // f y = y} : Real) =
          (Fintype.card Y : Real) ^ A :=
      (div_eq_one_iff_eq hden).mp hratio
    have hkpow :
        Nat.card {y : Y // f y = y} = Fintype.card Y ^ A := by
      exact_mod_cast hreal
    have hk : Nat.card {y : Y // f y = y} <= Fintype.card Y := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_subtype_le _
    have hnle : Fintype.card Y <= Fintype.card Y ^ A :=
      Nat.le_pow (a := Fintype.card Y) (b := A) (by omega)
    have hfixedCard :
        Nat.card {y : Y // f y = y} = Fintype.card Y := by
      omega
    have hfixedCard' :
        Fintype.card {y : Y // f y = y} = Fintype.card Y := by
      simpa [Nat.card_eq_fintype_card] using hfixedCard
    have hfixedSet : ({y : Y | f y = y} : Set Y) = Set.univ :=
      (set_fintype_card_eq_univ_iff _).mp hfixedCard'
    have hfixed : ∀ y : Y, f y = y := by
      intro y
      have hy : y ∈ ({y : Y | f y = y} : Set Y) := by
        rw [hfixedSet]
        exact Set.mem_univ y
      exact hy
    have hf : f = id := Function.forall_isFixedPt_iff.mp hfixed
    have hpowSelf : Fintype.card Y ^ A = Fintype.card Y := by
      omega
    have hdegenerate : A = 1 ∨ Fintype.card Y = 1 := by
      by_cases hn : Fintype.card Y = 1
      · exact Or.inr hn
      · left
        have hnTwo : 2 <= Fintype.card Y := by
          have hnPos : 0 < Fintype.card Y := Fintype.card_pos
          omega
        exact Nat.pow_right_injective hnTwo (by simpa using hpowSelf)
    exact ⟨Nat.pos_of_ne_zero hA, hf, hdegenerate⟩
  · rintro ⟨hA, rfl, hdegenerate⟩
    have hfixedCard :
        Nat.card {y : Y // id y = y} = Fintype.card Y := by
      simp [Nat.card_eq_fintype_card]
    rw [hfixedCard]
    rcases hdegenerate with rfl | hn
    · simp [Nat.cast_ne_zero.mpr (Fintype.card_pos.ne')]
    · rw [hn]
      simp [hA.ne']

/-- The one-address branch allows a nonsingleton output alphabet. -/
example :
    escapeProbability (A := Fin 1) (id : Fin 2 -> Fin 2) = 0 := by
  rw [escape_probability_eq_zero_iff]
  simp

/-- The singleton-alphabet branch allows more than one address. -/
example :
    escapeProbability (A := Fin 3) (id : Fin 1 -> Fin 1) = 0 := by
  rw [escape_probability_eq_zero_iff]
  simp

#print axioms escape_probability_eq_zero_iff

end D5.S0.Asymptotics.EscapeProbability.ZeroCharacterization
