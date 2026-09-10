/- GID: D5/S3/Zeros/Convolution/PerfectMatchingCount
   generality: G
   mirror-B: D5/B/S3/Zeros/Convolution/PerfectMatchingCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.Perm.Centralizer]
   utility: none
   digest: Fixed-point-free involution counts from Mathlib cycle-type counting. -/

import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
The counting theorem directly specializes Mathlib's cycle-type formula.
All parameters are arbitrary; no bounded enumeration, checker, numerical
reduction, or certified instance is introduced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Zeros.Convolution.PerfectMatchingCount

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Permutations that partition the underlying type into pairs. -/
abbrev FixedPointFreeInvolution (α : Type*) :=
  {p : Equiv.Perm α // Function.Involutive p ∧ ∀ x, p x ≠ x}

noncomputable instance : Fintype (FixedPointFreeInvolution α) := by
  classical
  exact Fintype.ofFinite _

private theorem involution_iff_cycleType (h : ℕ) (hc : Fintype.card α = 2 * h)
    (p : Equiv.Perm α) :
    (Function.Involutive p ∧ ∀ x, p x ≠ x) ↔
      p.cycleType = Multiset.replicate h 2 := by
  constructor
  · rintro ⟨hi, hn⟩
    have hp : p ^ 2 = 1 := by ext x; exact hi x
    have hs : p.support = Finset.univ := by ext x; simp [hn x]
    have ht := Equiv.Perm.cycleType_of_pow_prime_eq_one hp
    have he := p.sum_cycleType
    rw [ht, Multiset.sum_replicate, hs, Finset.card_univ, hc] at he
    have hh : p.cycleType.card = h := by
      simp only [nsmul_eq_mul, Nat.cast_id] at he
      omega
    simpa [hh] using ht
  · intro ht
    have hp : p ^ 2 = 1 := Equiv.Perm.pow_prime_eq_one_iff.mpr (by
      intro c hc
      simpa using (Multiset.mem_replicate.mp (ht ▸ hc)).2)
    have hs : p.support = Finset.univ := Finset.eq_univ_of_card _ (by
      rw [← p.sum_cycleType, ht, Multiset.sum_replicate, hc]
      simp [nsmul_eq_mul, Nat.mul_comm])
    refine ⟨fun x => ?_, fun x => ?_⟩
    · exact congrArg (fun q : Equiv.Perm α => q x) hp
    · exact Equiv.Perm.mem_support.mp (hs ▸ Finset.mem_univ x)

/-- Division-free specialization of Mathlib's permutation cycle-type count. -/
theorem card_fixedPointFreeInvolution_mul (h : ℕ) (hc : Fintype.card α = 2 * h) :
    Fintype.card (FixedPointFreeInvolution α) * (h.factorial * 2 ^ h) =
      (2 * h).factorial := by
  classical
  have he : Fintype.card (FixedPointFreeInvolution α) =
      (Finset.univ.filter fun p : Equiv.Perm α =>
        p.cycleType = Multiset.replicate h 2).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact involution_iff_cycleType h hc p
  rw [he]
  have hm := Equiv.Perm.card_of_cycleType_mul_eq α (Multiset.replicate h 2)
  have hh : (Multiset.replicate h 2).sum ≤ Fintype.card α ∧
      ∀ c ∈ Multiset.replicate h 2, 2 ≤ c := by
    simp [hc, Multiset.mem_replicate, nsmul_eq_mul, Nat.mul_comm]
  have hsum : (Multiset.replicate h 2).sum = 2 * h := by simp [Nat.mul_comm]
  have hcount : (∏ n ∈ (Multiset.replicate h 2).toFinset,
      ((Multiset.replicate h 2).count n).factorial) = h.factorial := by
    by_cases hz : h = 0
    · subst h; simp
    · rw [Multiset.toFinset_replicate, if_neg hz]
      simp
  rw [if_pos hh, hc, hsum, Multiset.prod_replicate, hcount,
    Nat.sub_self, Nat.factorial_zero, one_mul] at hm
  simpa only [Nat.mul_comm (2 ^ h) h.factorial] using hm

/-- The factorial quotient is exact, including the empty type. -/
theorem card_fixedPointFreeInvolution (h : ℕ) (hc : Fintype.card α = 2 * h) :
    Fintype.card (FixedPointFreeInvolution α) =
      (2 * h).factorial / (h.factorial * 2 ^ h) := by
  apply Nat.eq_div_of_mul_eq_right (by positivity)
  simpa only [Nat.mul_comm] using card_fixedPointFreeInvolution_mul h hc

#print axioms card_fixedPointFreeInvolution_mul
#print axioms card_fixedPointFreeInvolution
#print axioms involution_iff_cycleType

end D5.S3.Zeros.Convolution.PerfectMatchingCount
