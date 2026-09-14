/- GID: D5/S3/Arith/Congruence/CloitreBernoulliIntegralityRefutation
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/CloitreBernoulliIntegralityRefutation
   mirror-E: none(waiver:symbolic-refutation-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.NumberTheory.Bernoulli]
   utility: none
   digest: Cloitre's A090825 integrality conjecture fails at n = 833. -/

import Mathlib.NumberTheory.Bernoulli

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace D5.S3.Arith.Congruence.CloitreBernoulliIntegralityRefutation

/-- The rational expression defining OEIS A090825. Mathlib's `bernoulli`
uses the convention `B₁ = -1/2`; the index here is always even. -/
def F (n : ℕ) : ℚ :=
  (3 / 2) * (1 / (n : ℚ)) * (2 * n + 1) * (3 ^ n + 1) * bernoulli (2 * n)

/-- The prime sequence A053176: primes `p` for which `2p+1` is composite. -/
def A053176 (p : ℕ) : Prop :=
  Nat.Prime p ∧ ¬ Nat.Prime (2 * p + 1)

/-- Cloitre's 2004 conjecture in OEIS A090825. -/
def claim : Prop :=
  ∀ n : ℕ, 1 < n → ¬ Nat.Prime n →
    (∀ p : ℕ, Nat.Prime p → p ∣ n → A053176 p) →
      ∃ z : ℤ, F n = z

end D5.S3.Arith.Congruence.CloitreBernoulliIntegralityRefutation
