/- GID: D5/S3/Arith/PrimesNotSemilinear
   generality: G
   mirror-B: D5/B/S3/Arith/PrimesNotSemilinear
   mirror-E: none(waiver:symbolic-number-theoretic-obstruction)
   anchors: [mathlib/module/Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Defs]
   utility: none
   digest: The natural primes together with one form a set that is not semilinear. -/

import Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Defs
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Prime.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.PrimesNotSemilinear

/-- No positive translation preserves membership in one together with the primes on a tail. -/
private theorem primes_union_one_not_ultimately_periodic :
    ¬ ∃ k : ℕ, ∃ d > 0, ∀ x ≥ k,
      x ∈ ({1} ∪ {p : ℕ | p.Prime}) ↔ x + d ∈ ({1} ∪ {p : ℕ | p.Prime}) := by
  rintro ⟨k, d, hd, hperiod⟩
  obtain ⟨p, hpbound, hp⟩ := Nat.exists_infinite_primes (max k d + 1)
  have hkp : k ≤ p := by omega
  have hmem : ∀ m : ℕ, p + m * d ∈ ({1} ∪ {q : ℕ | q.Prime}) := by
    intro m
    induction m with
    | zero => simpa using (Or.inr hp : p ∈ ({1} ∪ {q : ℕ | q.Prime}))
    | succ m ih =>
      have hstep := (hperiod (p + m * d) (by omega)).mp ih
      simpa only [Nat.succ_mul, Nat.add_assoc] using hstep
  have hcomposite : p * (1 + d) ∈ ({1} ∪ {q : ℕ | q.Prime}) := by
    simpa only [Nat.mul_add, Nat.mul_one] using hmem p
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq] at hcomposite
  rcases hcomposite with hone | hprime
  · have hle : p ≤ p * (1 + d) := Nat.le_mul_of_pos_right p (by omega)
    have hp2 := hp.two_le
    omega
  · exact Nat.not_prime_mul hp.ne_one (by omega) hprime

/-- Adjoining one to the natural primes does not produce a semilinear set. -/
theorem primes_union_one_not_isSemilinearSet :
    ¬ IsSemilinearSet ({1} ∪ {p : ℕ | p.Prime}) := by
  intro hs
  exact primes_union_one_not_ultimately_periodic
    (Nat.isSemilinearSet_iff_ultimately_periodic.mp hs)

#print axioms primes_union_one_not_isSemilinearSet

end D5.S3.Arith.PrimesNotSemilinear
