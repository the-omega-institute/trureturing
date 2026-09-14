/- GID: D5/S0/Certificates/IanakievOddNonunitaryPowerSumRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/IanakievOddNonunitaryPowerSumRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.NumberTheory.Divisors]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/IanakievOddNonunitaryPowerSumRefutation.claim; result=D5/S0/Certificates/IanakievOddNonunitaryPowerSumRefutation.result; claim=D5/S0/Certificates/IanakievOddNonunitaryPowerSumRefutation.claim
   digest: The value 9216 refutes Ianakiev's power-sum divisibility conjecture for OEIS A319927. -/

import Mathlib.NumberTheory.Divisors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S0.Certificates.IanakievOddNonunitaryPowerSumRefutation

/-!
OEIS A319927 contains the positive integers whose nonzero sum of squares of
odd non-unitary divisors divides the sum of squares of all non-unitary
divisors.  Ianakiev conjectured that the analogous divisibility holds for
every nonnegative power at every member of the sequence.

The member `9216` refutes that conjecture at power one.  Its odd
non-unitary divisors have sum `3`, while all its non-unitary divisors have
sum `16361`.
-/

/-- The divisors `d` of `n` that are not unitary: `d` and `n / d` are not
coprime. -/
def nonunitaryDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter (fun d => 1 < Nat.gcd d (n / d))

/-- The sum of the `k`-th powers of the non-unitary divisors of `n`. -/
def S (k n : ℕ) : ℕ :=
  ∑ d ∈ nonunitaryDivisors n, d ^ k

/-- The sum of the `k`-th powers of the odd non-unitary divisors of `n`. -/
def O (k n : ℕ) : ℕ :=
  ∑ d ∈ (nonunitaryDivisors n).filter (fun d => d % 2 = 1), d ^ k

/-- Membership in A319927, including the source program's nonzero
odd-divisor-sum guard. -/
def member (n : ℕ) : Prop :=
  0 < n ∧ 0 < O 2 n ∧ O 2 n ∣ S 2 n

/-- Ianakiev's conjecture that every nonnegative power preserves the
defining divisibility at every member of A319927. -/
def claim : Prop :=
  ∀ n : ℕ, member n → ∀ k : ℕ, O k n ∣ S k n

/-- The sequence member `9216` refutes the conjecture at power one. -/
theorem result : ¬ claim := by
  intro hclaim
  have hmember : member 9216 := by
    unfold member
    decide
  have hfailure : ¬ O 1 9216 ∣ S 1 9216 := by decide
  exact hfailure (hclaim 9216 hmember 1)

#print axioms nonunitaryDivisors
#print axioms S
#print axioms O
#print axioms member
#print axioms claim
#print axioms result

end D5.S0.Certificates.IanakievOddNonunitaryPowerSumRefutation
