# A Finite Upper Bound for Fair-Source Window Defects

## Abstract

One fixed deterministic window table attains a reciprocal endpoint bound with a collision correction.

**Theorem 1.1 (A deterministic table for every admissible word length).**

Lean statement: `D5/S3/Combinatorics/FairWindowUpperBound.fair_window_defect_upper_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FairWindowUpperBound.fair_window_defect_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of natural numbers R and m satisfying 1 <= m <= R, there exists one function f from all binary R-words to one bit such that fairDefect(R,f) <= 1/(R-m+2) + choose(R-m+2,2)/2^m. Here fairDefect is the sum of the actual transport-defect indicators over every binary context of length R+1, divided by 2^(R+1). Thus all joint contexts have their exact independent fair-source weights. The table has no online random input or auxiliary state. For two candidate words at distance d, equality forces the encompassing block to repeat its first d bits periodically. Restriction to the bits outside the second word is a bijection onto R+1-m free bits, so each collision has exact probability 2^(-m), including overlapping words. Summing over the choose(R-m+2,2) pairs bounds all collisions. On every context without collisions, the offline ordering and label average is 1/(R-m+2). Commuting these finite averages with the exact source average and choosing an ordering and a label table no worse than their averages gives the asserted fixed deterministic function.

## References

- Truth anchor: `D5/S3/Combinatorics/FairWindowUpperBound.fair_window_defect_upper_bound`
- Dependency: [D5/S3/Combinatorics/FairWindowMinimizer](FairWindowMinimizer.md)
