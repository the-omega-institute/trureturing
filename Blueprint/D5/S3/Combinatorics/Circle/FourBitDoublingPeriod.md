# Four-gap actual doubling periods

## Abstract

The primitive directed gap block determines the actual doubling period of every four-bit seed with gaps at least two.

**Theorem 1.1 (Actual minimal period and every natural return).**

Lean statement: `D5/S3/Combinatorics/Circle/FourBitDoublingPeriod.four_gap_actual_period`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourBitDoublingPeriod.four_gap_actual_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a,b,c,d be arbitrary natural numbers, each at least two. Put r=a+b+c+d, M=2^r-1 and Q=1+2^a+2^(a+b)+2^(a+b+c). Define p=a when a=b=c=d, p=a+b when a=c and b=d but not all four gaps are equal, and p=r otherwise. The theorem asserts NarrowDoublingOrbit.period(M,Q)=p, where period is Function.minimalPeriod of doubling on ZMod(M), and for every natural h, including zero, residue(M,Q,h)=Q if and only if p divides h.

The occupied exponents are 0,a,a+b,a+b+c in Fin(r). Their complement contains exponent one, since each gap is at least two. A proper support and each of its translates have binary mask strictly below M. Multiplication by 2^h translates the support by h modulo r. Binary geometric-sum injectivity therefore converts equality of the two residues into equality of the actual finite supports. No cancellation of Q occurs.

A stabilizing shift below r sends occupied zero to one of the four occupied prefixes. Translating backwards by a, a+b or a+b+c gives increasing occupied-prefix sets with directed gap words (b,c,d,a), (c,d,a,b) or (d,a,b,c). Equality of increasing prefix sets forces, respectively, all equal gaps, alternating gaps, or all equal gaps. The primitive gap block thus has one, two or four entries, and its sum is exactly p. Exhibiting that return and classifying the positive minimal return proves the actual minimal-period equality. Function.isPeriodicPt_iff_minimalPeriod_dvd then gives all natural returns.

These statements include nonunit Q modulo M and every unequal orientation of the gap word. Only the multiplier two has an invertible action; the seed need not be a unit. The result classifies this four-bit family, rather than a conditional proposed period or a support-cardinality surrogate. The binary encoding and cyclic addition reuse ZeroSumSubsets.mask, CircularWords.cycAdd, Finset.geomSum_injective and Nat.geomSum_lt. No literature novelty is asserted. This arithmetic classification does not construct the full physical circle ordering or settle the original all-source Circle Conjecture 3.1.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourBitDoublingPeriod.four_gap_actual_period`
- Dependency: [D5/S3/Combinatorics/Circle/NarrowDoublingOrbit](NarrowDoublingOrbit.md)
- Dependency: [D5/S3/Combinatorics/Circle/ZeroSumSubsets](ZeroSumSubsets.md)
