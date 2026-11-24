/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/FiniteRangeExtended
   generality: I
   mirror-B: D5/B/S3/Arith/PrimitiveRoot/SmallPrimes/FiniteRangeExtended
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks05/Block0426.checked0426
   digest: Every odd prime below the enlarged analytic threshold has a smaller prime root. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.FiniteRange
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Groups.Group06
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Groups.Group07
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Groups.Group08

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem extended_odd_slots :
    ∀ (k : ℕ), k < 758259 → (3483483 + 2 * k).Prime →
      ∃ (q : ℕ), q.Prime ∧ q < 3483483 + 2 * k ∧
        orderOf (q : ZMod (3483483 + 2 * k)) = 3483483 + 2 * k - 1 := by
  intro k hk hp
  by_cases h0 : k < 327680
  · have hindex : k - 0 < 327680 := by omega
    have heq : 3483483 + 2 * (k - 0) = 3483483 + 2 * k := by omega
    have h := group06_sound (k - 0) hindex
    rw [heq] at h
    exact h hp
  by_cases h1 : k < 655360
  · have hindex : k - 327680 < 327680 := by omega
    have heq : 4138843 + 2 * (k - 327680) = 3483483 + 2 * k := by omega
    have h := group07_sound (k - 327680) hindex
    rw [heq] at h
    exact h hp
  have hindex : k - 655360 < 102899 := by omega
  have heq : 4794203 + 2 * (k - 655360) = 3483483 + 2 * k := by omega
  have h := group08_sound (k - 655360) hindex
  rw [heq] at h
  exact h hp

/-- Complete finite coverage for the unconditional principal-term threshold. -/
theorem small_prime_primitiveRoot_extended (p : ℕ) (hp3 : 3 ≤ p) (hlt : p < 5000000)
    (hp : p.Prime) :
    ∃ (q : ℕ), q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 := by
  by_cases hold : p < 3483482
  · exact small_prime_primitiveRoot p hp3 hold hp
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have heq : 3483483 + 2 * ((p - 3483483) / 2) = p := by omega
  have hindex : (p - 3483483) / 2 < 758259 := by omega
  have h := extended_odd_slots ((p - 3483483) / 2) hindex
  rw [heq] at h
  exact h hp

#print axioms small_prime_primitiveRoot_extended

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
