/- GID: D5/S3/Arith/EuclidLemma
   generality: G
   mirror-B: D5/B/S3/Arith/EuclidLemma
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A prime dividing a product of two naturals divides one of the factors. -/

import Mathlib.Data.Nat.Prime.Basic

namespace D5.S3.Arith.EuclidLemma

/-- Euclid's lemma: if a prime `p` divides the product `a * b` of two natural
numbers, then `p` divides `a` or `p` divides `b`. -/
theorem euclid_prime_dvd_mul {p a b : ℕ} (hp : Nat.Prime p) (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b :=
  hp.dvd_mul.mp h

end D5.S3.Arith.EuclidLemma
