/- GID: D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Primitive Fibonacci states have one zero phase at each prime-power precision. -/

import D5.S3.Arith.FibonacciAtomic.GraftAffineClosure
import D5.S3.Arith.FibonacciAtomic.SamplingQuotient
import D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon
import Mathlib.RingTheory.Coprime.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.GraftLocalBehaviorLabels

open GraftAffineClosure (step)
open TimeSampling (readout zeroRank)

/-- Every primitive state that hits zero has exactly one zero phase. -/
theorem primitive_hit_phase (p m : ℕ) (hp : p.Prime)
    (x : ZMod (p ^ m) × ZMod (p ^ m)) (hx : IsUnit x.1 ∨ IsUnit x.2)
    (t k : ℕ) (ht : (step^[t] x).1 = 0) :
    (step^[k] x).1 = 0 ↔ k % zeroRank (p ^ m) = t % zeroRank (p ^ m) := by
  classical
  let n := p ^ m
  let : NeZero n := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcop : IsCoprime x.1 x.2 := by
    rcases hx with h | h
    · obtain ⟨a, ha⟩ := isUnit_iff_exists_inv'.mp h
      exact ⟨a, 0, by simpa using ha⟩
    · obtain ⟨b, hb⟩ := isUnit_iff_exists_inv'.mp h
      exact ⟨0, b, by simpa using hb⟩
  have iter_coprime (i : ℕ) : IsCoprime (step^[i] x).1 (step^[i] x).2 := by
    induction i with
    | zero => exact hcop
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      simpa only [step, mul_one] using ih.symm.add_mul_left_right (1 : ZMod n)
  have hit_unit : IsUnit (step^[t] x).2 := by
    have h := iter_coprime t
    rw [ht] at h
    exact isCoprime_zero_left.mp h
  have ranks := (PrimePowerGcdHorizon.sharp_prime_power_gcd_horizon p 2 hp le_rfl).1 m
  have entry (i : ℕ) : (Nat.fib i : ZMod n) = 0 ↔ zeroRank n ∣ i := by
    rw [ZMod.natCast_eq_zero_iff]
    exact D5.S3.Arith.FibonacciRank.fibonacci_entry_point ranks.1 ranks.2.1 ranks.2.2
  have first_zero (i : ℕ) (b : ZMod n) :
      (step^[i] (0, b)).1 = (Nat.fib i : ZMod n) * b := by
    have h := SamplingQuotient.readout_iterate n i (b, 0)
    change readout n i (b, 0) = (step^[i] (b, 0)).2 at h
    calc
      (step^[i] (0, b)).1 = (step^[i] (step (b, 0))).1 := by simp [step]
      _ = (step (step^[i] (b, 0))).1 := by
        rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
      _ = readout n i (b, 0) := h.symm
      _ = _ := by simp [readout]
  have forward (d : ℕ) : (step^[t + d] x).1 = 0 ↔ zeroRank n ∣ d := by
    rw [Nat.add_comm t d, Function.iterate_add_apply]
    have pair : step^[t] x = (0, (step^[t] x).2) := Prod.ext ht rfl
    rw [pair, first_zero, hit_unit.mul_left_eq_zero, entry]
  let L := (n ^ 2).factorial
  have period (z : ZMod n × ZMod n) : Function.IsPeriodicPt step L z :=
    ((GraftAffineClosure.result.2 n (pow_pos hp.pos m) (0, 0)).2.1 z)
  have Lpos : 0 < L := Nat.factorial_pos _
  have rankL : zeroRank n ∣ L := by
    apply (entry L).mp
    have h := congrArg Prod.fst (period (0, 1)).eq
    rw [first_zero] at h
    simpa using h
  let q := (t + 1) * L
  have tq : t ≤ k + q := by
    have : t + 1 ≤ q := Nat.le_mul_of_pos_right _ Lpos
    omega
  have same_state : step^[k + q] x = step^[k] x := by
    rw [Function.iterate_add_apply]
    rw [((period x).const_mul (t + 1)).eq]
  have same_phase : (k + q) % zeroRank n = k % zeroRank n := by
    have hq : zeroRank n ∣ q := dvd_mul_of_dvd_right rankL _
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hq, add_zero, Nat.mod_mod]
  rw [← same_state, ← same_phase]
  change (step^[k + q] x).1 = 0 ↔ Nat.ModEq (zeroRank n) (k + q) t
  rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' tq]
  rw [← forward (k + q - t), Nat.add_sub_cancel' tq]

#print axioms primitive_hit_phase

end D5.S3.Arith.FibonacciAtomic.GraftLocalBehaviorLabels
