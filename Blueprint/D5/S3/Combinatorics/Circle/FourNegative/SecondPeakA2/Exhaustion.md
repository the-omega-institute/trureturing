# Exhaustion

## Abstract

Second peak SecondPeakA2: Exhaustion

Every independent dyadic p=2^u>=4, q=2^s>=2, and h in {1,2} enters either the large-p branch, the small-p infinite-q branch or the forty-row remainder. The resulting Good witness has no feasibility assumption.

**Theorem 1.1 (dyadic_exists).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Exhaustion.dyadic_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Exhaustion.dyadic_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem dyadic_exists (u s h : ℕ) (hu : 2≤u) (hs : 1≤s) (hh : h=1 ∨ h=2) :     ∃ v m M : ℕ, ∃ before : Bool, Good (2^u) (2^s) h v m M before

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Exhaustion.dyadic_exists`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Finite](Finite.md)
