/- GID: D5/S3/Arith/Robin/ShortCofactorCharacterEnergy
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ShortCofactorCharacterEnergy
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Short positive intervals have a logarithmic multiplicative energy bound. -/

import Mathlib.Combinatorics.Additive.Energy
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Sigma
import Mathlib.Tactic

namespace D5.S3.Arith.Robin.ShortCofactorCharacterEnergy

open Finset

/-- The positive natural numbers strictly below a real cutoff. -/
noncomputable def shortInterval (H : ℝ) : Finset ℕ := Ico 1 ⌈H⌉₊

/-- The classical gcd parametrization gives a logarithmic energy bound. -/
theorem short_interval_energy (H : ℝ) (hH : 1 ≤ H) :
    ((shortInterval H).mulEnergy (shortInterval H) : ℝ) ≤
      2 * H ^ 2 * (1 + Real.log H) := by
  sorry

#check Nat.coprime_div_gcd_div_gcd
#check Nat.Coprime.dvd_of_dvd_mul_right
#check Nat.mul_div_cancel_left'
#check Nat.le_div_iff_mul_le
#check Finset.card_sigma
#check Finset.card_le_card_of_surjOn
#check Nat.card_Icc
#check Nat.ceil_le
#check Nat.lt_ceil
#check Nat.ceil_lt_add_one
#check Nat.ceil_pos
#check Nat.cast_div_le
#check Real.inner_le_Lp_mul_Lq
#check Finset.inner_le_Lp_mul_Lq
#check DirichletCharacter.unit_norm_eq_one
#check MulChar.inv_apply'
#check Complex.normSq_eq_norm_sq

end D5.S3.Arith.Robin.ShortCofactorCharacterEnergy
