/- GID: D5/S3/Arith/Congruence/KrizekAllMultiplesOfTheOrder
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/KrizekAllMultiplesOfTheOrder
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.GeomSum]
   utility: none
   digest: OEIS A260407: divisibility at exponent n-1 is equivalent to divisibility at every positive multiple. -/

import Mathlib.Algebra.Ring.GeomSum

namespace D5.S3.Arith.Congruence.KrizekAllMultiplesOfTheOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The modulus `(n - 1)^2 + 1` from OEIS A260407. -/
def modulus (n : ℕ) : ℕ :=
  (n - 1) ^ 2 + 1

/-- Membership in OEIS A260407. -/
def inSequence (n : ℕ) : Prop :=
  modulus n ∣ 2 ^ (n - 1) - 1

/-- Divisibility at every positive multiple of the source exponent. -/
def allMultiples (n : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → modulus n ∣ 2 ^ (k * (n - 1)) - 1

/-- Jaroslav Krizek's 2016 conjecture in OEIS A260407. -/
theorem result : ∀ n : ℕ, 1 ≤ n → (inSequence n ↔ allMultiples n) := by
  intro n _
  unfold inSequence allMultiples
  constructor
  · intro h k _
    exact h.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 (dvd_mul_left (n - 1) k))
  · intro h
    simpa using h 1 (by decide)

#print axioms modulus
#print axioms inSequence
#print axioms allMultiples
#print axioms result

end D5.S3.Arith.Congruence.KrizekAllMultiplesOfTheOrder
