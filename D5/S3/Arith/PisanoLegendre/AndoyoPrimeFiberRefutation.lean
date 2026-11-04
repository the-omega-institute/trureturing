/- GID: D5/S3/Arith/PisanoLegendre/AndoyoPrimeFiberRefutation
   generality: I
   mirror-B: D5/B/S3/Arith/PisanoLegendre/AndoyoPrimeFiberRefutation
   mirror-E: none(waiver:symbolic-external-open-problem-refutation)
   anchors: []
   utility: none
   digest: Andoyo Question 5.2 fails: seeds (0,3) have exact odd-prime fiber {3} at -1. -/

/-
admission_basis: open-problem-resolution (#22882; Refuted)
Applicability: arbitrary signed integer seeds, not both zero; every odd prime,
including primes dividing both seeds. The fixed seeds (0,3) refute the original
universal assertion; no coprime-seed infinitude statement is asserted.
Utility: none. The declarations describe exact recurrence periods and unbounded
prime fibers. No bounded enumeration, checker, numerical reduction or certified
finite-instance delivery occurs: the zero orbit at three is a consumed base case
inside the symbolic norm/parity obstruction for every other odd prime.
The instance designation records the specific permitted seed counterexample;
the obstruction itself quantifies over all odd primes.
Per declaration: name | proof_shape | live consumers.
  fiber | bind-only definition | claim, fiber_subset, result
  claim | bind-only definition | result
  recurrence_state | content | period_exists
  period_exists | content | period_even, value_at_three
  recurrence_norm | content | period_even
  period_even | content | fiber_subset
  count_partition | bind-only | fiber_subset
  zero_mod_three | content | value_at_three
  value_at_three | content | result
  fiber_subset | content | result
  result | content | external Question 5.2 settlement
The consumed content comprises recurrence-state periodicity, the alternating
norm, period parity and the exact Legendre-count partition. All eight helpers
remain private. Imported F, ScalarPeriod, pi, signCount, K and chi retain their
original definitions; no private Q5.3 supplier is used or re-proved.
-/

import D5.S3.Arith.AndoyoPisanoSetCollision
import Mathlib.Tactic

/-! The value -1 at the zero orbit is isolated by parity at every other odd prime. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.PisanoLegendre.AndoyoPrimeFiberRefutation

open D5.S3.Arith.AndoyoPisanoSetCollision
open D5.S3.Arith.FibonacciAtomic.GraftAffineClosure (step)
open scoped BigOperators

/-- The exact fiber over all odd primes; the primality proof supplies the Legendre instance. -/
def fiber (a b k : ℤ) : Set ℕ :=
  {p | ∃ hp : p.Prime, p ≠ 2 ∧ K p hp a b = k}

/-- Andoyo Question 5.2, including arbitrary signed, nonprimitive seed pairs. -/
def claim : Prop := ∀ a b : ℤ, (a, b) ≠ (0, 0) →
  ∀ k : ℤ, k ∈ chi a b → (fiber a b k).Infinite

private theorem recurrence_state (p : ℕ) (a b : ℤ) (n : ℕ) :
    (step (A := ZMod p))^[n] (a, b) =
      ((F a b n : ZMod p), (F a b (n + 1) : ZMod p)) := by
  induction n with
  | zero => simp [F]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [step, F, Int.cast_add]
    congr 1
    ring

private theorem period_exists (p : ℕ) (hp : p.Prime) (a b : ℤ) :
    ScalarPeriod p a b (pi p a b) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hinj : Function.Injective (step (A := ZMod p)) := by
    intro x y h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [step] at h1 h2
    apply Prod.ext
    · rw [h1] at h2
      exact add_right_cancel h2
    · exact h1
  obtain ⟨t, ht, hr⟩ := hinj.mem_periodicPts ((a, b) : ZMod p × ZMod p)
  have hs : ScalarPeriod p a b t := by
    refine ⟨ht, fun n => ?_⟩
    have he : (step (A := ZMod p))^[n + t] (a, b) =
        (step (A := ZMod p))^[n] (a, b) := by
      rw [Function.iterate_add_apply, hr.eq]
    simpa only [recurrence_state] using congrArg Prod.fst he
  have hne : {t | ScalarPeriod p a b t}.Nonempty := ⟨t, hs⟩
  exact csInf_mem hne

private theorem recurrence_norm (a b : ℤ) (n : ℕ) :
    F a b (n + 1) ^ 2 - F a b n * F a b (n + 1) - F a b n ^ 2 =
      (-1 : ℤ) ^ n * (b ^ 2 - a * b - a ^ 2) := by
  induction n with
  | zero => simp [F]
  | succ n ih =>
    calc
      _ = -(F a b (n + 1) ^ 2 - F a b n * F a b (n + 1) - F a b n ^ 2) := by
        rw [show n + 1 + 1 = n + 2 by omega, F]
        ring
      _ = _ := by rw [ih, pow_succ]; ring

private theorem period_even (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (a b : ℤ) (hd : ((b ^ 2 - a * b - a ^ 2 : ℤ) : ZMod p) ≠ 0) :
    Even (pi p a b) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hs := period_exists p hp a b
  have h0 := hs.2 0
  have h1 := hs.2 1
  simp only [Nat.zero_add, F] at h0
  simp only [F] at h1
  have hn := congrArg (fun z : ℤ => (z : ZMod p)) (recurrence_norm a b (pi p a b))
  push_cast at hn
  rw [h0, show pi p a b + 1 = 1 + pi p a b by omega, h1] at hn
  by_contra he
  have ho := Nat.not_even_iff_odd.mp he
  rw [ho.neg_one_pow] at hn
  have hz : (2 : ZMod p) * ((b : ZMod p)^2 - a*b - a^2) = 0 := by
    linear_combination hn
  have htwo : (2 : ZMod p) = 0 := (mul_eq_zero.mp hz).resolve_right (by simpa using hd)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    ((ZMod.natCast_eq_zero_iff 2 p).mp htwo))

private theorem count_partition (p : ℕ) (hp : p.Prime) (a b : ℤ) :
    signCount p hp a b 1 + signCount p hp a b (-1) + signCount p hp a b 0 =
      pi p a b := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hsum : (∑ n ∈ Finset.range (pi p a b),
      ((if legendreSym p (F a b n) = 1 then 1 else 0) +
       (if legendreSym p (F a b n) = -1 then 1 else 0) +
       (if legendreSym p (F a b n) = 0 then 1 else 0) : ℕ)) = pi p a b := by
    calc
      _ = ∑ _n ∈ Finset.range (pi p a b), (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro n _
        by_cases hz : (F a b n : ZMod p) = 0
        · have h := (legendreSym.eq_zero_iff p _).mpr hz
          simp [h]
        · rcases legendreSym.eq_one_or_neg_one p hz with h | h <;> simp [h]
      _ = _ := by simp
  simpa only [Finset.sum_add_distrib, Finset.sum_boole, signCount, Nat.cast_id] using hsum

private theorem zero_mod_three (n : ℕ) : (F 0 3 n : ZMod 3) = 0 := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [F]
  | one => change (3 : ZMod 3) = 0; decide
  | more n h0 h1 => simp only [F, Int.cast_add, h0, h1, add_zero]

private theorem value_at_three : K 3 Nat.prime_three 0 3 = -1 := by
  have hp : pi 3 0 3 = 1 := by
    apply le_antisymm
    · exact csInf_le' (show ScalarPeriod 3 0 3 1 from
        ⟨by decide, fun n => by rw [zero_mod_three, zero_mod_three]⟩)
    · exact (period_exists 3 Nat.prime_three 0 3).1
  simp [K, signCount, hp, Finset.filter_singleton, F]

private theorem fiber_subset : fiber 0 3 (-1) ⊆ {3} := by
  rintro p ⟨hp, hp2, hk⟩
  by_contra hp3
  have hne : p ≠ 3 := by simpa using hp3
  letI : Fact p.Prime := ⟨hp⟩
  have hthree : (3 : ZMod p) ≠ 0 := by
    intro h
    exact hne ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
      ((ZMod.natCast_eq_zero_iff 3 p).mp h))
  have he := period_even p hp hp2 0 3 (by
    simpa only [zero_mul, zero_pow (by decide : 2 ≠ 0), sub_zero,
      Int.cast_pow, Int.cast_ofNat] using pow_ne_zero 2 hthree)
  obtain ⟨t, ht⟩ := he
  have hc := count_partition p hp 0 3
  have hci : (signCount p hp 0 3 1 : ℤ) + signCount p hp 0 3 (-1) +
      signCount p hp 0 3 0 = (pi p 0 3 : ℤ) := by exact_mod_cast hc
  unfold K at hk
  have hti : (pi p 0 3 : ℤ) = (t : ℤ) + t := by exact_mod_cast ht
  omega

/-- The attained value -1 for seeds (0,3) has no odd-prime realizations outside {3}. -/
theorem result : ¬ claim := by
  intro h
  have hi := h 0 3 (by decide) (-1) ⟨3, Nat.prime_three, by decide, value_at_three⟩
  exact hi (Set.finite_singleton 3 |>.subset fiber_subset)

#print axioms result

end D5.S3.Arith.PisanoLegendre.AndoyoPrimeFiberRefutation
