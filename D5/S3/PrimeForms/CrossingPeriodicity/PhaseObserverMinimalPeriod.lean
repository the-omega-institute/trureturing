/- GID: D5/S3/PrimeForms/CrossingPeriodicity/PhaseObserverMinimalPeriod
   generality: G
   mirror-B: D5/B/S3/PrimeForms/CrossingPeriodicity/PhaseObserverMinimalPeriod
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Names the observer and proves positive, zero, odd, and even period cases. -/

/- Library-search audit trail (2026-08-25):
   * Repository search confirmed that the source phase `Psi` is the public `windingPhase`
     from `ExactPropagation`; the imported sandwich module proves its displacement by two.
   * Pinned-Mathlib source search hit `ZMod.addOrderOf_coe`, which gives the required
     quotient by a gcd directly, and `addOrderOf_eq_iff`, which exposes minimality.
   * For the existing rational-circle observer, source search hit
     `AddCircle.gcd_mul_addOrderOf_div_eq`; it proves the same order without a new quotient
     equivalence. The local `smart_search.sh` name searches returned no textual matches.
   * `addOrderOf_nsmul` and `Nat.div_gcd` were inspected but are not needed after the exact
     `ZMod` and `AddCircle` hits. No general CRT order theorem was needed for the fixed case.
   * The corollary evaluates both closed forms and the lcm. This checks, rather than derives,
     the source's CRT decomposition because the source only asks for the fixed moduli 4 and 3.
-/

import D5.S3.PrimeForms.CrossingPeriodicity.SandwichPhasePeriod
import D5.S3.PrimeForms.CrossingPeriodicity.PhaseObserverTranslation
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.PrimeForms.CrossingPeriodicity.PhaseObserverMinimalPeriod

open D5.S3.PrimeForms.Crossing.ExactPropagation

/-- The winding-phase observer modulo the natural modulus `m`, in the rational additive-circle
model already used by `phase_observer_descends_to_translation`. -/
def phaseObserver (m : Nat) (A : PositiveMatrix) : AddCircle (m : Rat) :=
  ((windingPhase A : Rat) : AddCircle (m : Rat))

/-- The closed form for the least positive period of translation by minus two modulo `m`. -/
def phasePeriod (m : Nat) : Nat := m / Nat.gcd m 2

/-- For a positive modulus, `phasePeriod m` is exactly the additive order of minus two: it
returns to zero, while no smaller positive step count does. -/
theorem phase_period_eq (m : Nat) (hm : 0 < m) :
    addOrderOf (-((2 : Nat) : ZMod m)) = phasePeriod m ∧
      0 < phasePeriod m ∧
      phasePeriod m • (-((2 : Nat) : ZMod m)) = 0 ∧
      ∀ k : Nat, k < phasePeriod m → 0 < k → k • (-((2 : Nat) : ZMod m)) ≠ 0 := by
  have horder : addOrderOf (-((2 : Nat) : ZMod m)) = phasePeriod m := by
    rw [addOrderOf_neg, phasePeriod]
    exact ZMod.addOrderOf_coe 2 hm.ne'
  have hpositive : 0 < phasePeriod m := by
    simpa only [phasePeriod] using
      Nat.div_pos (Nat.gcd_le_left 2 hm) (Nat.gcd_pos_of_pos_left 2 hm)
  exact ⟨horder, hpositive, (addOrderOf_eq_iff hpositive).mp horder⟩

#print axioms phase_period_eq

/-- The same period is the additive order of the translation step in the rational
`AddCircle (m : Rat)` used by the existing phase-observer semiconjugacy. -/
theorem phase_period_addCircle_eq (m : Nat) (hm : 0 < m) :
    addOrderOf (-((2 : Rat) : AddCircle (m : Rat))) = phasePeriod m ∧
      0 < phasePeriod m := by
  letI : Fact (0 < (m : Rat)) := ⟨by exact_mod_cast hm⟩
  have hm0 : (m : Rat) ≠ 0 := by exact_mod_cast hm.ne'
  constructor
  · rw [addOrderOf_neg, phasePeriod]
    have hmul :
        m.gcd 2 * addOrderOf ((2 : Rat) : AddCircle (m : Rat)) = m := by
      simpa [Nat.gcd_comm, div_mul_cancel₀ (2 : Rat) hm0] using
        AddCircle.gcd_mul_addOrderOf_div_eq (m : Rat) 2 hm
    apply (Nat.eq_div_iff_mul_eq_left
      (Nat.gcd_pos_of_pos_left 2 hm).ne' (Nat.gcd_dvd_left m 2)).2
    simpa [mul_comm] using hmul.symm
  · simpa only [phasePeriod] using
      Nat.div_pos (Nat.gcd_le_left 2 hm) (Nat.gcd_pos_of_pos_left 2 hm)

#print axioms phase_period_addCircle_eq

/-- The positive-modulus hypothesis is necessary for a least positive period: at modulus zero
the closed form is zero, so it cannot satisfy the positivity clause. -/
theorem positive_modulus_is_necessary :
    ¬(0 < phasePeriod 0 ∧
      addOrderOf (-((2 : Nat) : ZMod 0)) = phasePeriod 0) := by
  norm_num [phasePeriod]

#print axioms positive_modulus_is_necessary

-- These examples audit the zero modulus, the singleton quotient, and odd and even moduli.
example : phasePeriod 0 = 0 := by norm_num [phasePeriod]

example : phasePeriod 1 = 1 ∧ (-((2 : Nat) : ZMod 1)) = 0 := by
  exact ⟨by norm_num [phasePeriod], Subsingleton.elim _ _⟩

example : Odd 5 ∧ phasePeriod 5 = 5 := by norm_num [phasePeriod]

example : Even 8 ∧ phasePeriod 8 = 4 := by norm_num [phasePeriod]

-- Step count zero always returns, which is why minimality quantifies over positive counts.
example (m : Nat) : (0 : Nat) • (-((2 : Nat) : ZMod m)) = 0 := by simp

/-- The fixed CRT factorization is checked through its two component periods and their lcm. -/
theorem phase_period_twelve :
    phasePeriod 4 = 2 ∧ phasePeriod 3 = 3 ∧
      phasePeriod 12 = Nat.lcm 2 3 ∧ phasePeriod 12 = 6 := by
  norm_num [phasePeriod, Nat.lcm]

#print axioms phase_period_twelve

end D5.S3.PrimeForms.CrossingPeriodicity.PhaseObserverMinimalPeriod
