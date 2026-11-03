# Exact physical construction and coupled prefix strips

## Abstract

Independent adjacent paired gaps have a common physical joint order

**Theorem 1.1 (Every independent pair of adjacent equal gaps).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/Adjacent/FourNegativeAdjacentPairsJointLift.actualSource_four_negative_adjacent_pairs_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/Adjacent/FourNegativeAdjacentPairsJointLift.actualSource_four_negative_adjacent_pairs_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of independent natural r,s>=2, set k=2r+2s and A=1+2^r+2^(2r)+2^(2r+s). The theorem actualSource_four_negative_adjacent_pairs_joint_lift constructs a list sigma of Fin k and a natural j<=k for which OriginalOrder k A sigma and OriginalOrder (k+1) (2A) (earWord k sigma j) both hold. Each OriginalOrder includes permutation of all physical labels, exact zero total, and the centered strip bound for every natural prefix.

The five dyadic branches exhaust the independent parameters. The diagonal and s=r+1 constructions, including the boundary (2,3), use the near theorem; r=s+1 directly consumes the accepted FourNegativeAdjacentDoublePhysical.actualSource_four_negative_adjacent_double_joint_lift. The two far branches use the explicit complement and interval masks in FourNegativeAdjacentFarRight and FourNegativeAdjacentFarLeft. Cuts are zero on the diagonal and reverse-near branches, 2s+r on the accepted double branch, r+2s on the far-left branch and k-1 on the far-right branch.

The connection with the group action is through the actual doubling action on centered residues. The uniform table follows successive source coefficient recurrences in moduli N=2^k-1 and 2N+1. A physical occurrence is an index in the original action word, even when values coincide. Permutations act on these occurrences and the new word inserts the original fresh occurrence k. The proof therefore includes nonunit gcd values and shorter numerical periods without identifying labels, rotating phases or assuming a favorable schedule.

The source registration mirrors the complete four-binder telescope. Its two predicate-valued readouts are the actual old and new OriginalOrder predicates. The bridge is definitional equivalence; a rejecting realization, deletion of either role, and actual seed-dependent readouts witness variation, sensitivity and dependence. The continuation field is unknown and makes no undecidability claim. This establishes the adjacent paired-gap subfamily only; the unrestricted four-independent-gap physical J theorem and Circle C3.1 remain active and open. No external novelty is asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/Adjacent/FourNegativeAdjacentPairsJointLift.actualSource_four_negative_adjacent_pairs_joint_lift`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/Adjacent/FourNegativeAdjacentFarLeft](FourNegativeAdjacentFarLeft.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/Adjacent/FourNegativeAdjacentFarRight](FourNegativeAdjacentFarRight.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/Adjacent/FourNegativeAdjacentNearJointLift](FourNegativeAdjacentNearJointLift.md)
