/- GID: D5/S3/Arith/ResidueSeparation
   generality: I
   mirror-B: D5/B/S3/Arith/ResidueSeparation
   mirror-E: none(waiver:analytic-proof-only)
   anchors: []
   digest: A modulus above both operands makes the modular reading separate distinct naturals. -/

import Mathlib.Order.MinMax

namespace D5.S3.Arith.ResidueSeparation

/-- **Residue separation.** For natural numbers `m ≠ n`, any modulus `M`
strictly greater than both operands keeps their modular readings apart:
`m % M ≠ n % M`.

The hypothesis `max m n < M` says exactly that `M` exceeds each of `m` and `n`,
so both lie in the canonical residue range `[0, M)`. There the remainder map is
the identity: `Nat.mod_eq_of_lt` gives `m % M = m` and `n % M = n`. The two
readings therefore differ precisely because the operands do, which is the given
`m ≠ n`. The strictness of `max m n < M` is essential: with `M = max m n` the
larger operand would wrap to a smaller residue and the separation could fail. -/
theorem residue_separation (m n M : ℕ) (hmn : m ≠ n) (hlt : max m n < M) :
    m % M ≠ n % M := by
  obtain ⟨hm, hn⟩ := max_lt_iff.mp hlt
  rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn]
  exact hmn

end D5.S3.Arith.ResidueSeparation
