# Masks

## Abstract

Second peak SecondPeakA2: Masks

Dyadic exponent partitions and exact residues retain all exponents. The ordinary small-p mask has low bits 6 or 7; the h=2 mask is odd. In the exceptional h=1,p=4 sector, m=2q+1 retains its high physical bit and its literal low bit, and M=(32q-27)/5 satisfies the charged window exactly.

**Theorem 1.1 (pow_two_mod_five).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Masks.pow_two_mod_five`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Masks.pow_two_mod_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem pow_two_mod_five (s : ℕ) :     2^s%5=1 ∨ 2^s%5=2 ∨ 2^s%5=4 ∨ 2^s%5=3

**Theorem 1.2 (dyadic_eight).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Masks.dyadic_eight`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Masks.dyadic_eight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem dyadic_eight (s : ℕ) (hs : 64≤2^s) : 2^s%8=0

**Theorem 1.3 (dyadic_large_partition).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Masks.dyadic_large_partition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Masks.dyadic_large_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem dyadic_large_partition (s : ℕ) (hs : 2≤2^s) :     2^s=2 ∨ 2^s=4 ∨ 2^s=8 ∨ 16≤2^s

**Theorem 1.4 (dyadic_small_partition).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Masks.dyadic_small_partition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Masks.dyadic_small_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem dyadic_small_partition (s : ℕ) (hs : 2≤2^s) (hsmall : 2^s<64) :     2^s=2 ∨ 2^s=4 ∨ 2^s=8 ∨ 2^s=16 ∨ 2^s=32

**Theorem 1.5 (dyadic_p_partition).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Masks.dyadic_p_partition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Masks.dyadic_p_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem dyadic_p_partition (s : ℕ) (hs : 4≤2^s) :     2^s=4 ∨ 2^s=8 ∨ 2^s=16 ∨ 2^s=32 ∨ 64≤2^s

**Theorem 1.6 (small_delta).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Masks.small_delta`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Masks.small_delta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem small_delta (p q : ℕ)     (hp : p=4 ∨ p=8 ∨ p=16 ∨ p=32) (hq : 64≤q)     (hq8 : q%8=0) (hq5 : q%5≠0) (hex : p=4 → q%5≠1) :     ∃ delta : ℕ, 2≤delta ∧ delta≤4*p ∧       (8*p*(q-1)+delta)%5=0 ∧       ((8*p*(q-1)+delta)/5%8=6 ∨ (8*p*(q-1)+delta)/5%8=7)

**Theorem 1.7 (odd_mask).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Masks.odd_mask`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Masks.odd_mask` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem odd_mask (p q : ℕ) (hp : 4≤p) (hq : 64≤q) :     ∃ M : ℕ, 1<M ∧ SecondPeakHighD.Submask 1 M ∧       (4≤5*(M:ℤ)-(y p q 2-16*(p:ℤ))) ∧       (5*(M:ℤ)-(y p q 2-16*(p:ℤ))<14)

**Theorem 1.8 (exceptional_mask).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Masks.exceptional_mask`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Masks.exceptional_mask` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural s with 64<=2^s and 2^s mod 5=1, let q:Nat=2^s, m:Nat=2*q+1 and M:Nat=(32*q-27)/5. Then m<M, SecondPeakHighD.Submask m M, and 5*(M:Int)-(y 4 q 1-32)=5. The divisions and subtractions defining M are natural operations; the final charged equality is in the integers.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Masks.dyadic_eight`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Masks.dyadic_large_partition`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Masks.dyadic_p_partition`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Masks.dyadic_small_partition`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Masks.exceptional_mask`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Masks.odd_mask`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Masks.pow_two_mod_five`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Masks.small_delta`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Large](Large.md)
