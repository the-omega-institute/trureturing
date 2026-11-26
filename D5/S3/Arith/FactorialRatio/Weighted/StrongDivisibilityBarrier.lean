/- GID: D5/S3/Arith/FactorialRatio/Weighted/StrongDivisibilityBarrier
   generality: I
   mirror-B: D5/B/S3/Arith/FactorialRatio/Weighted/StrongDivisibilityBarrier
   mirror-E: none(waiver:symbolic-counterexample-family)
   anchors: [mathlib/module/Mathlib.Data.Fin.Tuple.NatAntidiagonal]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/FactorialRatio/Weighted/StrongDivisibilityBarrier.claim; result=D5/S3/Arith/FactorialRatio/Weighted/StrongDivisibilityBarrier.result; claim=D5/S3/Arith/FactorialRatio/Weighted/StrongDivisibilityBarrier.claim
   digest: Positive strong divisibility sequences have unbounded compact excess already at rank and window two. -/

import D5.S3.Arith.FactorialRatio.CompactFactorialGcd
import Mathlib.Tactic

/-! An unbounded family of compact excesses for positive strong divisibility sequences. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FactorialRatio.Weighted.StrongDivisibilityBarrier

open Finset

private def generalizedFactorial (u : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ i ∈ Ioc 0 n, u i

private def compactProduct (B : ℕ → ℕ) (r s b : ℕ) : ℕ :=
  ∏ i ∈ range r, B ((i + 1) * b) / B b * B (s - (r - (i + 1)) * b)

private def compactGcd (u : ℕ → ℕ) (r s : ℕ) : ℕ :=
  (range (s / r + 1)).gcd (compactProduct (generalizedFactorial u) r s)

private def fullGcd (u : ℕ → ℕ) (H M : ℕ) : ℕ :=
  (Finset.Nat.antidiagonalTuple (M + 1) (H - M)).gcd
    (fun a => ∏ i, generalizedFactorial u (a i))

/-- A uniform finite bound at the single admissible pair r=s=2 would be
necessary for a compression bound over all positive strong divisibility sequences. -/
def claim : Prop := ∃ bound : ℕ, ∀ u : ℕ → ℕ,
  (∀ n, 0 < n → 0 < u n) →
  (∀ a b, 0 < a → 0 < b → Nat.gcd (u a) (u b) = u (Nat.gcd a b)) →
  compactGcd u 2 2 / fullGcd u 5 1 ≤ bound

private def periodicSequence (P n : ℕ) : ℕ := if 2 ∣ n then P else 1

private theorem periodic_positive {P : ℕ} (hP : 0 < P) :
    ∀ n, 0 < n → 0 < periodicSequence P n := by
  intro n _
  unfold periodicSequence
  split_ifs <;> omega

private theorem periodic_strong (P : ℕ) :
    ∀ a b, 0 < a → 0 < b →
      Nat.gcd (periodicSequence P a) (periodicSequence P b) =
        periodicSequence P (Nat.gcd a b) := by
  intro a b _ _
  have hg : 2 ∣ Nat.gcd a b ↔ 2 ∣ a ∧ 2 ∣ b := Nat.dvd_gcd_iff
  by_cases ha : 2 ∣ a <;> by_cases hb : 2 ∣ b <;>
    simp [periodicSequence, ha, hb, hg]

private theorem factorial_values (P : ℕ) :
    generalizedFactorial (periodicSequence P) 0 = 1 ∧
    generalizedFactorial (periodicSequence P) 1 = 1 ∧
    generalizedFactorial (periodicSequence P) 2 = P ∧
    generalizedFactorial (periodicSequence P) 3 = P ∧
    generalizedFactorial (periodicSequence P) 4 = P * P := by
  norm_num [generalizedFactorial, periodicSequence, Finset.prod_Ioc_succ_top]

private theorem compact_value (P : ℕ) : compactGcd (periodicSequence P) 2 2 = P * P := by
  obtain ⟨h0, h1, h2, _, _⟩ := factorial_values P
  norm_num [compactGcd, compactProduct, Finset.range_add_one, Finset.gcd_insert,
    Finset.prod_range_succ, h0, h1, h2]
  change Nat.gcd (P * P) (P ^ 2) = P * P
  rw [pow_two, Nat.gcd_self]

private theorem full_value (P : ℕ) : fullGcd (periodicSequence P) 5 1 = P := by
  change (Finset.Nat.antidiagonalTuple 2 4).gcd
    (fun a : Fin 2 → ℕ => ∏ i, generalizedFactorial (periodicSequence P) (a i)) = P
  have hvalues := factorial_values P
  rcases hvalues with ⟨h0, h1, h2, h3, h4⟩
  apply Nat.dvd_antisymm
  · let a : Fin 2 → ℕ := ![1, 3]
    have ha : a ∈ Finset.Nat.antidiagonalTuple 2 4 := by
      apply Finset.Nat.mem_antidiagonalTuple.mpr
      simp [a, Fin.sum_univ_two]
    have hdiv := Finset.gcd_dvd (f := fun a : Fin 2 → ℕ =>
      ∏ i, generalizedFactorial (periodicSequence P) (a i)) ha
    simpa [fullGcd, a, Fin.prod_univ_two, h1, h3] using hdiv
  · apply Finset.dvd_gcd
    intro a ha
    have hsum := Finset.Nat.mem_antidiagonalTuple.mp ha
    simp only [Fin.sum_univ_two] at hsum
    have ha0 : a 0 ≤ 4 := by omega
    have hpair : a 1 = 4 - a 0 := by omega
    rw [Fin.prod_univ_two, hpair]
    interval_cases h : a 0 <;> simp [h, h0, h1, h2, h3, h4]

private theorem excess_value {P : ℕ} (hP : 0 < P) :
    compactGcd (periodicSequence P) 2 2 / fullGcd (periodicSequence P) 5 1 = P := by
  rw [compact_value, full_value, Nat.mul_div_cancel_left _ hP]

/-- At r=s=2 the excess equals an arbitrary positive parameter P. -/
theorem result : ¬ claim := by
  rintro ⟨bound, h⟩
  have hP : 0 < bound + 1 := Nat.zero_lt_succ bound
  have hbad := h (periodicSequence (bound + 1))
    (periodic_positive hP) (periodic_strong (bound + 1))
  rw [excess_value hP] at hbad
  omega

end D5.S3.Arith.FactorialRatio.Weighted.StrongDivisibilityBarrier
