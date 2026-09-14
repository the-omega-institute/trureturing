/- GID: D5/S0/Certificates/CloitrePrimeGapDivisorCharacterizationRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/CloitrePrimeGapDivisorCharacterizationRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.NumberTheory.Divisors, mathlib/module/Mathlib.Tactic.IntervalCases]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/CloitrePrimeGapDivisorCharacterizationRefutation.claim; result=D5/S0/Certificates/CloitrePrimeGapDivisorCharacterizationRefutation.result; claim=D5/S0/Certificates/CloitrePrimeGapDivisorCharacterizationRefutation.claim
   digest: The value 529 refutes Cloitre's divisor-count prime-gap characterization of OEIS A049591. -/

import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S0.Certificates.CloitrePrimeGapDivisorCharacterizationRefutation

/-!
OEIS A049591 consists of odd primes `p` for which `p + 2` is composite.
Benoit Cloitre's comment of 2002-04-13 proposes that this sequence also
consists exactly of the integers `n > 1` having no prime strictly between
`n` and `n + tau(n)^2`, where `tau(n)` is the number of divisors of `n`.

The integer `529 = 23^2` refutes only that proposed characterization.  It
has three divisors, and every integer strictly between `529` and `538` is
composite, but `529` itself is not prime and hence is not a sequence term.
-/

/-- Membership in A049591: an odd prime whose value plus two is not prime. -/
def Term (n : ℕ) : Prop :=
  Odd n ∧ Nat.Prime n ∧ ¬ Nat.Prime (n + 2)

/-- There is no prime in the open interval from `n` to `n + tau(n)^2`. -/
def NoPrimeInGap (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p →
    ¬ (n < p ∧ p < n + (Nat.divisors n).card ^ 2)

/-- Cloitre's proposed exact characterization of A049591. -/
def claim : Prop :=
  ∀ n : ℕ, 1 < n → (Term n ↔ NoPrimeInGap n)

/-- The value `529` satisfies the prime-gap condition but is not prime. -/
theorem result : ¬ claim := by
  intro hclaim
  have hgap : NoPrimeInGap 529 := by
    intro p hp hbetween
    have hcard : (Nat.divisors 529).card ^ 2 = 9 := by decide
    rw [hcard] at hbetween
    norm_num at hbetween
    rcases hbetween with ⟨hlower, hupper⟩
    interval_cases p <;> exact absurd hp (by decide)
  have hnotTerm : ¬ Term 529 := by
    intro hterm
    exact (by decide : ¬ Nat.Prime 529) hterm.2.1
  exact hnotTerm ((hclaim 529 (by norm_num)).mpr hgap)

#print axioms Term
#print axioms NoPrimeInGap
#print axioms claim
#print axioms result

end D5.S0.Certificates.CloitrePrimeGapDivisorCharacterizationRefutation
