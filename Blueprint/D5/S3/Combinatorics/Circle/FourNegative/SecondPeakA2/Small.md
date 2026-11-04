# Small

## Abstract

Second peak SecondPeakA2: Small

The unbounded small-p sectors use q=64+u polynomial certificates. The exceptional sector uses q=4u and the high/low mask. These branches preserve the same Good predicate and both possible locations of the literal fresh insertion.

**Theorem 1.1 (small_exists).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Small.small_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Small.small_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem small_exists (p s h : ℕ)     (hp : p=4 ∨ p=8 ∨ p=16 ∨ p=32) (hq : 64≤2^s) (hh : h=1 ∨ h=2) :     ∃ v m M : ℕ, ∃ before : Bool, Good p (2^s) h v m M before

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Small.small_exists`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Masks](Masks.md)
