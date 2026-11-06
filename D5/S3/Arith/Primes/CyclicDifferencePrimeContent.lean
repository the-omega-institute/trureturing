/- GID: D5/S3/Arith/Primes/CyclicDifferencePrimeContent
   generality: G
   mirror-B: D5/B/S3/Arith/Primes/CyclicDifferencePrimeContent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The content of every positive cyclic difference is a prime power. -/
/-
admission_basis: escape-witness
escape_witness: content_prime_power
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/20302.
proof_shape: coeff: bind-only; consumers: D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.powerBlocks_initial, D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.commIter_powerBlocks, D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.result, D5.S3.Arith.Primes.CyclicDifferencePrimeContent.sum_coeff_succ, D5.S3.Arith.Primes.CyclicDifferencePrimeContent.coeff_cast_nonzero, D5.S3.Arith.Primes.CyclicDifferencePrimeContent.content, D5.S3.Arith.Primes.CyclicDifferencePrimeContent.order_prime_power_of_coeff
proof_shape: diff_eq_zero_const: bind-only; consumers: D5.S3.Arith.Primes.CyclicDifferencePrimeContent.diff_injective_sum_zero
proof_shape: sum_diff: bind-only; consumers: D5.S3.Arith.Primes.CyclicDifferencePrimeContent.sum_coeff_succ
proof_shape: diff_injective_sum_zero: bind-only; consumers: D5.S3.Arith.Primes.CyclicDifferencePrimeContent.coeff_cast_nonzero
proof_shape: sum_coeff_succ: bind-only; consumers: D5.S3.Arith.Primes.CyclicDifferencePrimeContent.coeff_cast_nonzero
proof_shape: coeff_cast_nonzero: content; consumers: D5.S3.Arith.Primes.CyclicDifferencePrimeContent.content_ne_zero, D5.S3.Arith.Primes.CyclicDifferencePrimeContent.prime_dvd_content
proof_shape: content: bind-only; consumers: D5.S3.Arith.Primes.CyclicDifferencePrimeContent.content_ne_zero, D5.S3.Arith.Primes.CyclicDifferencePrimeContent.prime_dvd_content, D5.S3.Arith.Primes.CyclicDifferencePrimeContent.content_prime_power, D5.S3.Arith.Primes.CyclicDifferencePrimeContent.order_prime_power_of_coeff
proof_shape: content_ne_zero: content; consumers: D5.S3.Arith.Primes.CyclicDifferencePrimeContent.content_prime_power
proof_shape: prime_dvd_content: content; consumers: D5.S3.Arith.Primes.CyclicDifferencePrimeContent.content_prime_power
proof_shape: content_prime_power: content; consumers: D5.S3.Arith.Primes.CyclicDifferencePrimeContent.order_prime_power_of_coeff
proof_shape: order_prime_power_of_coeff: content; consumers: D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.result
-/

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace D5.S3.Arith.Primes.CyclicDifferencePrimeContent

open Finset

variable {p : ℕ} [NeZero p]

def coeff (p : ℕ) [NeZero p] : ℕ → ZMod p → ℤ
  | 0, j => if j = 1 then 1 else 0
  | r + 1, j => coeff p r j - coeff p r (j - 1)

private theorem diff_eq_zero_const {A : Type*} [AddGroup A] (v : ZMod p → A)
    (h : ∀ j, (v j - v (j - 1)) = 0) : ∀ j, v j = v 0 := by
  have hv : Function.Periodic v (1 : ZMod p) := by
    intro j
    simpa only [add_sub_cancel_right] using sub_eq_zero.mp (h (j + 1))
  intro j
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective j
  simpa only [mul_one] using hv.nat_mul_eq n

private theorem sum_diff {A : Type*} [AddCommGroup A] (v : ZMod p → A) :
    ∑ j, (v j - v (j - 1)) = 0 := by
  simp only [sum_sub_distrib]
  exact sub_eq_zero.mpr ((Equiv.subRight (1 : ZMod p)).sum_comp v).symm

private theorem diff_injective_sum_zero {K : Type*} [Ring K] [NoZeroDivisors K] (hp : (p : K) ≠ 0)
    (v : ZMod p → K) (hsum : ∑ j, v j = 0)
    (h : ∀ j, (v j - v (j - 1)) = 0) : ∀ j, v j = 0 := by
  have hc := diff_eq_zero_const v h
  have hz : (p : K) * v 0 = 0 := by
    simpa only [hc, sum_const, card_univ, ZMod.card, nsmul_eq_mul] using hsum
  have hzero : v 0 = 0 := (mul_eq_zero.mp hz).resolve_left hp
  intro j
  exact (hc j).trans hzero

private theorem sum_coeff_succ (r : ℕ) : ∑ j, coeff p (r + 1) j = 0 := by
  exact sum_diff _

private theorem coeff_cast_nonzero {K : Type*} [Ring K] [Nontrivial K] [NoZeroDivisors K]
    (hp : 1 < p) (hpk : (p : K) ≠ 0) (r : ℕ) :
    ¬ ∀ j, (coeff p (r + 1) j : K) = 0 := by
  letI : Fact (1 < p) := ⟨hp⟩
  induction r with
  | zero =>
    intro h
    have he := h 1
    simp [coeff, one_ne_zero, zero_ne_one] at he
  | succ r ih =>
    intro h
    apply ih
    apply diff_injective_sum_zero hpk
    · simpa only [← Int.cast_sum, sum_coeff_succ, Int.cast_zero]
    · intro j
      simpa only [coeff, Int.cast_sub] using h j

private def content (p : ℕ) [NeZero p] (r : ℕ) : ℕ :=
  Finset.univ.gcd (fun j => (coeff p (r + 1) j).natAbs)

private theorem content_ne_zero (hp : 1 < p) (r : ℕ) : content p r ≠ 0 := by
  intro h
  apply coeff_cast_nonzero (K := ℤ) hp (Int.natCast_ne_zero.mpr (Nat.ne_zero_of_lt hp)) r
  intro j
  have hz := Finset.gcd_eq_zero_iff.mp h j (mem_univ j)
  simpa only [Int.cast_id, Int.natAbs_eq_zero] using hz

private theorem prime_dvd_content (hp : p.Prime) (r : ℕ) {q : ℕ} (hq : q.Prime)
    (hd : q ∣ content p r) : q = p := by
  by_contra hqp
  letI : Fact q.Prime := ⟨hq⟩
  have hpk : (p : ZMod q) ≠ 0 := by
    exact CharP.cast_ne_zero_of_ne_of_prime (ZMod q) hp hqp
  apply coeff_cast_nonzero (K := ZMod q) hp.one_lt hpk r
  intro j
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
  rw [Int.natCast_dvd]
  exact hd.trans (Finset.gcd_dvd (mem_univ j))

private theorem content_prime_power (hp : p.Prime) (r : ℕ) :
    ∃ m : ℕ, content p r = p ^ m := by
  exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (content_ne_zero hp.one_lt r)
    (fun hq hd => prime_dvd_content hp r hq hd)⟩

theorem order_prime_power_of_coeff {G : Type*} [Group G]
    (hp : p.Prime) (g : G) (r : ℕ)
    (h : ∀ j, g ^ coeff p (r + 1) j = 1) : ∃ m : ℕ, orderOf g = p ^ m := by
  obtain ⟨m, hm⟩ := content_prime_power hp r
  have hd : orderOf g ∣ content p r := Finset.dvd_gcd fun j _ =>
    Int.natCast_dvd.mp (orderOf_dvd_iff_zpow_eq_one.mpr (h j))
  rw [hm] at hd
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).mp hd
  exact ⟨k, hk⟩


end D5.S3.Arith.Primes.CyclicDifferencePrimeContent
