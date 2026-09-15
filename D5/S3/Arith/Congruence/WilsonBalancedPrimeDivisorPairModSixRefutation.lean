/- GID: D5/S3/Arith/Congruence/WilsonBalancedPrimeDivisorPairModSixRefutation
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/WilsonBalancedPrimeDivisorPairModSixRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/Congruence/WilsonBalancedPrimeDivisorPairModSixRefutation.claim; result=D5/S3/Arith/Congruence/WilsonBalancedPrimeDivisorPairModSixRefutation.result; claim=D5/S3/Arith/Congruence/WilsonBalancedPrimeDivisorPairModSixRefutation.claim
   digest: The pair (140140, 141601) refutes the mod-six clause of Wilson's A260310 conjecture (v3). -/

import D5.S3.PrimeForms.PrimaryPseudoperfectPorts

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open D5.S3.PrimeForms.PrimaryPseudoperfectPorts (squarefreeDeriv)

namespace D5.S3.Arith.Congruence.WilsonBalancedPrimeDivisorPairModSixRefutation

/-- The sum of the distinct prime divisors of `n` (OEIS A008472). -/
def S (n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, p

/-- A balanced pair satisfying both the textual and programmatic source filters. -/
def IsPair (x y : ℕ) : Prop :=
  x < y ∧ S x + S y = squarefreeDeriv x + squarefreeDeriv y ∧ S x ≠ S y ∧ S y ≠ squarefreeDeriv y

/-- Wilson's conjecture that a composite smaller member is divisible by six. -/
def claim : Prop :=
  ∀ x y : ℕ, IsPair x y → 1 < x → ¬ Nat.Prime x → 6 ∣ x

/-- The balanced pair `(140140, 141601)` refutes the mod-six conjecture. -/
theorem result : ¬ claim := by
  intro h
  have hp2 : Nat.Prime 2 := by norm_num
  have hp5 : Nat.Prime 5 := by norm_num
  have hp7 : Nat.Prime 7 := by norm_num
  have hp11 : Nat.Prime 11 := by norm_num
  have hp13 : Nat.Prime 13 := by norm_num
  have hfactor : (140140 : ℕ) = 2 ^ 2 * 5 * 7 ^ 2 * 11 * 13 := by norm_num
  have hpf : (140140 : ℕ).primeFactors = {2, 5, 7, 11, 13} := by
    calc
      (140140 : ℕ).primeFactors = (2 ^ 2 * 5 * 7 ^ 2 * 11 * 13).primeFactors := by
        rw [hfactor]
      _ = (2 ^ 2 * 5 * 7 ^ 2 * 11).primeFactors ∪ (13 : ℕ).primeFactors := by
        rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
      _ = (2 ^ 2 * 5 * 7 ^ 2).primeFactors ∪ (11 : ℕ).primeFactors ∪
          (13 : ℕ).primeFactors := by
        rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
      _ = (2 ^ 2 * 5).primeFactors ∪ (7 ^ 2 : ℕ).primeFactors ∪
          (11 : ℕ).primeFactors ∪ (13 : ℕ).primeFactors := by
        rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
      _ = (2 ^ 2 : ℕ).primeFactors ∪ (5 : ℕ).primeFactors ∪
          (7 ^ 2 : ℕ).primeFactors ∪ (11 : ℕ).primeFactors ∪
          (13 : ℕ).primeFactors := by
        rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
      _ = {2, 5, 7, 11, 13} := by
        rw [Nat.primeFactors_prime_pow (by norm_num) hp2,
          Nat.primeFactors_prime_pow (by norm_num) hp7]
        simp [hp5.primeFactors, hp11.primeFactors, hp13.primeFactors]
  have hp141601 : Nat.Prime 141601 := by norm_num
  have hpair : IsPair 140140 141601 := by
    simp [IsPair, S, squarefreeDeriv, hpf, hp141601.primeFactors]
  have hdiv := h 140140 141601 hpair (by norm_num) (by norm_num)
  norm_num at hdiv

#print axioms result

end D5.S3.Arith.Congruence.WilsonBalancedPrimeDivisorPairModSixRefutation
