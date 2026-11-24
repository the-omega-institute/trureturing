/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/FiniteRange
   generality: I
   mirror-B: D5/B/S3/Arith/PrimitiveRoot/SmallPrimes/FiniteRange
   mirror-E: none(waiver:kernel-checked-literal-certificates)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks00/Block0000.checked0000
   digest: Every odd prime below the exact sieve threshold has a smaller prime root. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Groups.Group00
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Groups.Group01
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Groups.Group02
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Groups.Group03
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Groups.Group04
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Groups.Group05

set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-! Complete odd-slot coverage uses only kernel-checked literal blocks.
The prime hypothesis excludes the explicitly certified composite slots. The lower
endpoint excludes 2, where there is no smaller prime. -/

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem all_odd_slots :
    ∀ (k : ℕ), k < 1741740 → (3 + 2 * k).Prime →
      ∃ (q : ℕ), q.Prime ∧ q < 3 + 2 * k ∧
        orderOf (q : ZMod (3 + 2 * k)) = 3 + 2 * k - 1 := by
  intro k hk hp
  by_cases h0 : k < 327680
  ·
    have hindex : k - 0 < 327680 := by omega
    have heq : 3 + 2 * (k - 0) = 3 + 2 * k := by omega
    have h := group00_sound (k - 0) hindex
    rw [heq] at h
    exact h hp
  by_cases h1 : k < 655360
  ·
    have hindex : k - 327680 < 327680 := by omega
    have heq : 655363 + 2 * (k - 327680) = 3 + 2 * k := by omega
    have h := group01_sound (k - 327680) hindex
    rw [heq] at h
    exact h hp
  by_cases h2 : k < 983040
  ·
    have hindex : k - 655360 < 327680 := by omega
    have heq : 1310723 + 2 * (k - 655360) = 3 + 2 * k := by omega
    have h := group02_sound (k - 655360) hindex
    rw [heq] at h
    exact h hp
  by_cases h3 : k < 1310720
  ·
    have hindex : k - 983040 < 327680 := by omega
    have heq : 1966083 + 2 * (k - 983040) = 3 + 2 * k := by omega
    have h := group03_sound (k - 983040) hindex
    rw [heq] at h
    exact h hp
  by_cases h4 : k < 1638400
  ·
    have hindex : k - 1310720 < 327680 := by omega
    have heq : 2621443 + 2 * (k - 1310720) = 3 + 2 * k := by omega
    have h := group04_sound (k - 1310720) hindex
    rw [heq] at h
    exact h hp
  have hindex : k - 1638400 < 103340 := by omega
  have heq : 3276803 + 2 * (k - 1638400) = 3 + 2 * k := by omega
  have h := group05_sound (k - 1638400) hindex
  rw [heq] at h
  exact h hp

/-- The complete finite small-prime premise of conditional Erdős #985. -/
theorem small_prime_primitiveRoot (p : ℕ) (hp3 : 3 ≤ p) (hlt : p < 3483482)
    (hp : p.Prime) :
    ∃ (q : ℕ), q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 := by
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have heq : 3 + 2 * ((p - 3) / 2) = p := by omega
  have hindex : (p - 3) / 2 < 1741740 := by omega
  have h := all_odd_slots ((p - 3) / 2) hindex
  rw [heq] at h
  exact h hp

#print axioms small_prime_primitiveRoot

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
