# LowBits

## Abstract

Second peak SecondPeakHighD: LowBits

Submask means inclusion of every actual binary bit. Low-bit inclusion survives arbitrary high blocks; predecessor blocks provide all lower physical bits. These statements support the physical bank inventory and proper-mask construction.

**Definition 1.1 (Submask).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits.Submask`

*Formalization.* `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits.Submask` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Definition Submask in the source module; Submask means inclusion of every actual binary bit. Low-bit inclusion survives arbitrary high blocks; predecessor blocks provide all lower physical bits. These statements support the physical bank inventory and proper-mask construction.

**Theorem 1.2 (bit_below).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits.bit_below`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits.bit_below` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem bit_below (m k e : ℕ) (hm : m<2^k) (he : m.testBit e=true) : e<k

**Theorem 1.3 (submask_le).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits.submask_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits.submask_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem submask_le (m M : ℕ) (hs : Submask m M) : m≤M

**Theorem 1.4 (submask_of_land).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits.submask_of_land`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits.submask_of_land` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem submask_of_land (m M : ℕ) (h : m &&& M=m) : Submask m M

**Theorem 1.5 (submask_high_block).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits.submask_high_block`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits.submask_high_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem submask_high_block (k n c m : ℕ) (hc : c<2^k)     (hm : m<2^k) (hs : Submask m c) : Submask m (2^k*n+c)

**Theorem 1.6 (submask_predecessor).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits.submask_predecessor`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits.submask_predecessor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem submask_predecessor (k n m : ℕ) (hn : 1≤n) (hm : m<2^k) :     Submask m (2^k*n-1)

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits.Submask`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits.bit_below`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits.submask_high_block`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits.submask_le`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits.submask_of_land`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits.submask_predecessor`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/Algebra](Algebra.md)
