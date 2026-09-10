/- GID: D5/S3/ArithSums/A375178Supercongruence
   generality: G
   mirror-B: D5/B/S3/ArithSums/A375178Supercongruence
   mirror-E: none(waiver:universal-congruence-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.FieldTheory.Finite.Basic]
   utility: none
   digest: First-order binomial expansions and harmonic sums for A375178. -/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open Finset
namespace D5.S3.ArithSums.A375178Supercongruence

def a (n : ℕ) : ℕ := ∑ k ∈ range n, (Nat.choose (n + k - 1) k) ^ 3

private lemma prod_first_order {R : Type*} [CommRing R] {ι : Type*}
    (s : Finset ι) (t : R) (f : ι → R) :
    ∃ r : R, (∏ i ∈ s, (1 + t * f i)) = 1 + t * ∑ i ∈ s, f i + t ^ 2 * r := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨r, hr⟩ := ih
    refine ⟨r + f i * (∑ j ∈ s, f j) + t * f i * r, ?_⟩
    rw [prod_insert hi, sum_insert hi, hr]
    ring

private lemma sum_inverse_pow (p : ℕ) [Fact p.Prime] (r : ℕ) (hr : r < p - 1) :
    ∑ x : ZMod p, x⁻¹ ^ r = 0 := by
  rw [← Fintype.sum_equiv (Equiv.inv (ZMod p)) (fun x => x ^ r) (fun x => x⁻¹ ^ r)]
  · exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) r (by simpa using hr)
  · intro x
    simp

private lemma sum_cast_range {M : Type*} [AddCommMonoid M] (p : ℕ) [NeZero p]
    (f : ZMod p → M) : ∑ k ∈ range p, f k = ∑ x : ZMod p, f x := by
  apply Finset.sum_bij (fun (k : ℕ) _ => (k : ZMod p))
  · simp
  · intro a ha b hb hab
    have := congrArg ZMod.val hab
    simpa [ZMod.val_natCast_of_lt (mem_range.mp ha),
      ZMod.val_natCast_of_lt (mem_range.mp hb)] using this
  · intro b _
    exact ⟨b.val, mem_range.mpr b.val_lt, ZMod.natCast_zmod_val b⟩
  · simp


private def doubleH (p a b : ℕ) [NeZero p] : ZMod p :=
  ∑ x : ZMod p, ∑ y : ZMod p, if x.val < y.val then x⁻¹ ^ a * y⁻¹ ^ b else 0

private lemma doubleH_reverse (p : ℕ) [Fact p.Prime] :
    doubleH p 1 3 = doubleH p 3 1 := by
  unfold doubleH
  rw [sum_comm]
  apply Fintype.sum_equiv (Equiv.neg (ZMod p))
  intro x
  apply Fintype.sum_equiv (Equiv.neg (ZMod p))
  intro y
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  have hvx := x.val_lt
  have hvy := y.val_lt
  have hc : y.val < x.val ↔ p - x.val < p - y.val := by omega
  simp only [Equiv.neg_apply, ZMod.neg_val, hx, hy, if_false, ← hc,
    inv_neg, pow_one]
  split_ifs <;> ring

private lemma doubleH_shuffle (p : ℕ) [Fact p.Prime] :
    (∑ x : ZMod p, x⁻¹) * (∑ x : ZMod p, x⁻¹ ^ 3) =
      doubleH p 1 3 + doubleH p 3 1 + ∑ x : ZMod p, x⁻¹ ^ 4 := by
  unfold doubleH
  rw [Fintype.sum_mul_sum]
  have hr :
      (∑ x : ZMod p, ∑ y : ZMod p, if x.val < y.val then x⁻¹ ^ 3 * y⁻¹ else 0) =
      ∑ x : ZMod p, ∑ y : ZMod p, if y.val < x.val then x⁻¹ * y⁻¹ ^ 3 else 0 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro x _
    apply sum_congr rfl
    intro y _
    split_ifs <;> ring
  simp only [pow_one]
  rw [hr, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro x _
  have hd : x⁻¹ ^ 4 =
      ∑ y : ZMod p, if x = y then x⁻¹ * y⁻¹ ^ 3 else 0 := by simp [pow_succ, mul_assoc]
  rw [hd, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro y _
  have he : x.val = y.val ↔ x = y := ⟨fun h => by simpa only [ZMod.natCast_zmod_val] using congrArg (fun n : ℕ => (n : ZMod p)) h, congrArg ZMod.val⟩
  split_ifs <;> simp_all <;> omega

private lemma doubleH_zero (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    doubleH p 1 3 = 0 := by
  have h1 := sum_inverse_pow p 1 (by omega)
  have h4 := sum_inverse_pow p 4 (by omega)
  have hs := doubleH_shuffle p
  simp only [pow_one] at h1
  rw [h1, zero_mul, h4, add_zero, ← doubleH_reverse p] at hs
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  have : (2 : ZMod p) * doubleH p 1 3 = 0 := by linear_combination -hs
  exact (mul_eq_zero.mp this).resolve_left htwo


end D5.S3.ArithSums.A375178Supercongruence
