/- GID: D5/S3/ConceptDynamics/Coding/PrimitiveLifts/NilpotentRootAmalgamation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PrimitiveLifts/NilpotentRootAmalgamation
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: [mathlib/module/Mathlib.GroupTheory.Nilpotent, mathlib/module/Mathlib.Data.Int.GCD]
   utility: none
   digest: Coprime equal powers in any nilpotent group have a unique common root. -/

import Mathlib.GroupTheory.Nilpotent
import Mathlib.Data.Int.GCD

/-! Coprime root amalgamation by central-quotient induction and integer Bezout. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.PrimitiveLifts.NilpotentRootAmalgamation

open Subgroup QuotientGroup
open scoped commutatorElement

universe u

private theorem commute_of_coprime_power_commute {G : Type u} [Group G]
    [Group.IsNilpotent G] {m n : ℕ} (hmn : m.Coprime n) {x y : G}
    (hm : Commute (x ^ m) y) (hn : Commute x (y ^ n)) : Commute x y := by
  revert x y
  apply @Group.nilpotent_center_quotient_ind _ G _ _ (by simp +contextual)
  intro G _ _ ih x y hm hn
  have hcomm : ∀ g : G, Commute g ⁅x, y⁆ := by
    simp_rw [commute_iff_eq, ← mem_center_iff, ← eq_one_iff, ← mk'_apply,
      map_commutatorElement, commutatorElement_eq_one_iff_commute]
    apply ih
    · simpa using hm.map (mk' (center G))
    · simpa using hn.map (mk' (center G))
  apply commutatorElement_eq_one_iff_commute.mp
  apply (pow_eq_one_iff_of_coprime hmn).mp
  constructor
  · rw [(hcomm x).commutatorElement_pow_left]
    exact hm.commutator_eq
  · rw [(hcomm y).commutatorElement_pow_right]
    exact hn.commutator_eq

private theorem bezout_word {G : Type u} [Group G] (z : G) {m n : ℕ}
    (hmn : m.Coprime n) :
    (z ^ n) ^ Nat.gcdB m n * (z ^ m) ^ Nat.gcdA m n = z := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add,
    add_comm, ← Nat.gcd_eq_gcd_ab, hmn, Int.natCast_one, zpow_one]

/-- Equal coprime natural powers amalgamate uniquely in an arbitrary nilpotent group,
including zero exponents and groups with torsion. -/
theorem pow_eq_pow_iff_existsUnique {G : Type u} [Group G] [Group.IsNilpotent G]
    (x y : G) (m n : ℕ) (hmn : m.Coprime n) :
    x ^ m = y ^ n ↔ ∃! z : G, x = z ^ n ∧ y = z ^ m := by
  constructor
  · intro h
    have hxy : Commute x y := commute_of_coprime_power_commute hmn
      (by rw [h]; exact (Commute.refl y).pow_left n)
      (by rw [← h]; exact (Commute.refl x).pow_right m)
    let z := x ^ Nat.gcdB m n * y ^ Nat.gcdA m n
    have hx : x = z ^ n := by
      dsimp [z]
      rw [(hxy.zpow_zpow _ _).mul_pow]
      have hb := (bezout_word x hmn).symm
      rw [h] at hb
      simpa only [← zpow_natCast, ← zpow_mul, Int.mul_comm] using hb
    have hy : y = z ^ m := by
      dsimp [z]
      rw [(hxy.zpow_zpow _ _).mul_pow]
      have hb := (bezout_word y hmn).symm
      rw [← h] at hb
      simpa only [← zpow_natCast, ← zpow_mul, Int.mul_comm] using hb
    refine ⟨z, ⟨hx, hy⟩, ?_⟩
    intro w hw
    calc
      w = (w ^ n) ^ Nat.gcdB m n * (w ^ m) ^ Nat.gcdA m n := (bezout_word w hmn).symm
      _ = z := by rw [← hw.1, ← hw.2]
  · rintro ⟨z, ⟨rfl, rfl⟩, _⟩
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]

end D5.S3.ConceptDynamics.Coding.PrimitiveLifts.NilpotentRootAmalgamation
