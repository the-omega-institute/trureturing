/- GID: D5/S3/Arith/AndoyoPisanoSetCollision
   generality: I
   mirror-B: D5/B/S3/Arith/AndoyoPisanoSetCollision
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Distinct integer Fibonacci seeds have equal complete Pisano sets. -/

import D5.S3.Arith.PisanoMatrixBridge
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! ## A collision of complete Pisano sets

The source scalar periods are compared before any Legendre counts are taken.
The count comparison includes the zeroth index and the wraparound endpoint.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.AndoyoPisanoSetCollision

open D5.S3.Arith.FibonacciAtomic.GraftAffineClosure (step)
open scoped BigOperators

/-- The integer recurrence, including its zeroth term. -/
def F (a b : ℤ) : ℕ → ℤ
  | 0 => a
  | 1 => b
  | n + 2 => F a b (n + 1) + F a b n

/-- A positive scalar period at every nonnegative index, modulo p. -/
def ScalarPeriod (p : ℕ) (a b : ℤ) (t : ℕ) : Prop :=
  0 < t ∧ ∀ n : ℕ, (F a b (n + t) : ZMod p) = (F a b n : ZMod p)

/-- The least positive scalar period. -/
noncomputable def pi (p : ℕ) (a b : ℤ) : ℕ := sInf {t | ScalarPeriod p a b t}

/-- The number of indices with the specified Legendre value in one least period.
Repeated residue values contribute once for each index. -/
noncomputable def signCount (p : ℕ) (hp : p.Prime) (a b s : ℤ) : ℕ := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  exact ((Finset.range (pi p a b)).filter fun n => legendreSym p (F a b n) = s).card

/-- All three counts are cast to integers before either subtraction. -/
noncomputable def K (p : ℕ) (hp : p.Prime) (a b : ℤ) : ℤ :=
  (signCount p hp a b 1 : ℤ) - (signCount p hp a b (-1) : ℤ) -
    (signCount p hp a b 0 : ℤ)

/-- The complete Pisano set, indexed by all odd primes. -/
def chi (a b : ℤ) : Set ℤ := {k | ∃ (p : ℕ) (hp : p.Prime), p ≠ 2 ∧ K p hp a b = k}

private theorem standard (n : ℕ) : F 0 1 n = (Nat.fib n : ℤ) := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n h0 h1 => simp [F, Nat.fib_add_two, h0, h1, add_comm]

private theorem shifted (n : ℕ) : F 1 1 n = F 0 1 (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n h0 h1 => simpa only [F, h0, h1]

private theorem periods_equal (p t : ℕ) :
    ScalarPeriod p 1 1 t ↔ ScalarPeriod p 0 1 t := by
  constructor
  · rintro ⟨ht, h⟩
    refine ⟨ht, ?_⟩
    have h1 : (F 0 1 (t + 1) : ZMod p) = 1 := by
      simpa only [shifted, Nat.zero_add, F, Int.cast_one] using h 0
    have h2 : (F 0 1 (t + 2) : ZMod p) = 1 := by
      simpa only [shifted, F, Nat.add_assoc, Nat.add_comm 1 t, Int.cast_one] using h 1
    have h0 : (F 0 1 t : ZMod p) = 0 := by
      have hr : (F 0 1 (t + 2) : ZMod p) =
          (F 0 1 (t + 1) : ZMod p) + (F 0 1 t : ZMod p) := by
        simp only [F, Int.cast_add]
      rw [h2, h1] at hr
      exact add_left_cancel (hr.symm.trans (add_zero 1).symm)
    intro n
    cases n with
    | zero => simpa only [Nat.zero_add, F, Int.cast_zero] using h0
    | succ n =>
      simpa only [shifted, Nat.succ_eq_add_one, Nat.add_right_comm] using h n
  · rintro ⟨ht, h⟩
    refine ⟨ht, fun n => ?_⟩
    simpa only [shifted, Nat.add_right_comm] using h (n + 1)

private theorem least_period (p : ℕ) (hp : p.Prime) :
    ScalarPeriod p 0 1 (pi p 0 1) ∧
      ∀ t, ScalarPeriod p 0 1 t → pi p 0 1 ≤ t := by
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
  obtain ⟨t, ht, hreturn⟩ := hinj.mem_periodicPts ((0, 1) : ZMod p × ZMod p)
  have hscalar : ScalarPeriod p 0 1 t := by
    refine ⟨ht, fun n => ?_⟩
    have hm := (PisanoMatrixBridge.period_iff_return p t).mpr hreturn n
    simpa only [standard, Int.cast_natCast] using
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hm
  have hne : {t | ScalarPeriod p 0 1 t}.Nonempty := ⟨t, hscalar⟩
  exact ⟨csInf_mem hne, fun t h => csInf_le' h⟩

private theorem pi_equal (p : ℕ) (hp : p.Prime) : pi p 1 1 = pi p 0 1 := by
  have hleast := least_period p hp
  have hshift : ScalarPeriod p 1 1 (pi p 0 1) :=
    (periods_equal p _).mpr hleast.1
  have hnonempty : {t | ScalarPeriod p 1 1 t}.Nonempty := ⟨_, hshift⟩
  have hshiftleast : ScalarPeriod p 1 1 (pi p 1 1) := csInf_mem hnonempty
  exact le_antisymm (csInf_le' hshift)
    (hleast.2 _ ((periods_equal p _).mp hshiftleast))

private theorem counts_equal (p : ℕ) (hp : p.Prime) (s : ℤ) :
    signCount p hp 1 1 s = signCount p hp 0 1 s := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hend : legendreSym p (F 0 1 (pi p 0 1)) = legendreSym p (F 0 1 0) := by
    have h := (least_period p hp).1.2 0
    have hc : (F 0 1 (pi p 0 1) : ZMod p) = (F 0 1 0 : ZMod p) := by
      simpa only [Nat.zero_add] using h
    exact congrArg (quadraticChar (ZMod p)) hc
  let u : ℕ → ℕ := fun n => if legendreSym p (F 0 1 n) = s then 1 else 0
  have hu : u (pi p 0 1) = u 0 := by simp only [u, hend]
  have hsum := Finset.sum_range_succ' u (pi p 0 1)
  rw [Finset.sum_range_succ, hu] at hsum
  have heq : (∑ n ∈ Finset.range (pi p 0 1), u (n + 1)) =
      ∑ n ∈ Finset.range (pi p 0 1), u n := (Nat.add_right_cancel hsum).symm
  simpa only [u, signCount, pi_equal p hp, shifted, Finset.sum_boole, Nat.cast_id] using heq

/-- Andoyo's Question 5.3: distinct nonzero integer seed pairs can have the
same complete Pisano set. The exhibited pairs are (0,1) and (1,1). -/
theorem result : ∃ a₁ b₁ a₂ b₂ : ℤ,
    (a₁, b₁) ≠ (a₂, b₂) ∧ (a₁, b₁) ≠ (0, 0) ∧ (a₂, b₂) ≠ (0, 0) ∧
      chi a₁ b₁ = chi a₂ b₂ := by
  refine ⟨0, 1, 1, 1, by decide, by decide, by decide, ?_⟩
  have hk (p : ℕ) (hp : p.Prime) : K p hp 1 1 = K p hp 0 1 := by
    simp only [K, counts_equal]
  ext k
  simp only [chi, Set.mem_ofPred_eq, hk]

#print axioms result

end D5.S3.Arith.AndoyoPisanoSetCollision
