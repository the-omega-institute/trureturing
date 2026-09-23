/- GID: D5/S3/Arith/Covering/CoveringSystem
   generality: G
   mirror-B: D5/B/S3/Arith/Covering/CoveringSystem
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Int.CardIntervalMod, mathlib/module/Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset, mathlib/module/Mathlib.Algebra.BigOperators.Ring.Finset, mathlib/module/Mathlib.Data.Nat.Cast.Field]
   utility: none
   digest: Finite systems of positive-modulus congruence classes covering the integers have reciprocal-modulus sum at least one. -/

import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Cast.Field

set_option autoImplicit false

namespace D5.S3.Arith.Covering.CoveringSystem

open scoped BigOperators

/-- Each pair `(a, m)` denotes the whole congruence class of `a` modulo the positive
modulus `m`. Coverage is over `ℤ`, so negative integers are explicitly included;
the natural residue `a` need not be reduced modulo `m`. -/
def IsCoveringSystem (C : Finset (ℕ × ℕ)) : Prop :=
  (∀ p ∈ C, 1 ≤ p.2) ∧ ∀ z : ℤ, ∃ p ∈ C, Int.ModEq (p.2 : ℤ) z (p.1 : ℤ)

/-- The moduli are at least two and distinct for distinct members of the system. -/
def IsDistinct (C : Finset (ℕ × ℕ)) : Prop :=
  (∀ p ∈ C, 2 ≤ p.2) ∧ (C : Set (ℕ × ℕ)).Pairwise (fun p q => p.2 ≠ q.2)

/-- Every modulus in the system is odd. -/
def AllOdd (C : Finset (ℕ × ℕ)) : Prop :=
  ∀ p ∈ C, Odd p.2

/-- Counting the covered residues over a common period gives the density bound.
Overlaps are allowed, so the reciprocal-modulus sum is bounded below by one. -/
theorem sum_reciprocal_moduli_ge_one {C : Finset (ℕ × ℕ)} (hC : IsCoveringSystem C) :
    1 ≤ ∑ p ∈ C, (1 : ℚ) / p.2 := by
  classical
  let M := ∏ p ∈ C, p.2
  have hM : 0 < M := Finset.prod_pos (fun p hp => hC.1 p hp)
  have hdvd : ∀ p ∈ C, p.2 ∣ M := fun p hp => Finset.dvd_prod_of_mem Prod.snd hp
  let R := fun p : ℕ × ℕ => (Finset.range M).filter (fun n => Nat.ModEq p.2 n p.1)
  have hcard : ∀ p ∈ C, (R p).card = M / p.2 := by
    intro p hp
    have hc := Nat.count_modEq_card M (hC.1 p hp) p.1
    simpa [Nat.count_eq_card_filter_range, Nat.mod_eq_zero_of_dvd (hdvd p hp), R]
      using hc
  have hcover : C.biUnion R = Finset.range M := by
    ext n
    constructor
    · intro hn
      obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.mp hn
      exact (Finset.mem_filter.mp hp).1
    · intro hn
      obtain ⟨p, hp, hz⟩ := hC.2 (n : ℤ)
      exact Finset.mem_biUnion.mpr ⟨p, hp,
        Finset.mem_filter.mpr ⟨hn, Int.natCast_modEq_iff.mp hz⟩⟩
  have hcount : M ≤ ∑ p ∈ C, M / p.2 := by
    calc
      M = (C.biUnion R).card := by rw [hcover, Finset.card_range]
      _ ≤ ∑ p ∈ C, (R p).card := Finset.card_biUnion_le
      _ = ∑ p ∈ C, M / p.2 := Finset.sum_congr rfl hcard
  have hcountQ : (M : ℚ) ≤ ∑ p ∈ C, (M : ℚ) / p.2 := by
    have hc : (M : ℚ) ≤ ∑ p ∈ C, ((M / p.2 : ℕ) : ℚ) := by
      exact_mod_cast hcount
    convert hc using 1
    apply Finset.sum_congr rfl
    intro p hp
    exact (Nat.cast_div (hdvd p hp) (by exact_mod_cast (Nat.ne_of_gt (hC.1 p hp)))).symm
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  apply (mul_le_mul_iff_right₀ hMq).mp
  simpa only [mul_one, Finset.mul_sum, mul_one_div] using hcountQ

end D5.S3.Arith.Covering.CoveringSystem
