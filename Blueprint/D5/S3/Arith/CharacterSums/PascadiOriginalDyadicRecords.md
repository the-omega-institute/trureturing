# Global moments of actual retained records

## Abstract

The actual reduced physical bases determine every dyadic coordinate box and give the global retained moment without supplied coordinate heights or scale counts.

Fix a prime p, positive real widths X<=Y with 3Y<p^2, and H>0 with H^2=XY. The finite parameters (w,t) are the original integer middle entries in the literal box. Each selected parameter has an actual reduced basis of its index-p^3 middle lattice; the basis witnesses are required only on this finite set. The anchor is the actual integer vector -(w,t). Every endpoint is an actual original WordSolution in the physical box. The long-chart, unit shortest-coordinate and unit middle/endpoint hypotheses remain explicit.

**Theorem 1.1 (All physical scales of the large fibers).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalDyadicRecords.actual_dyadic_large_second_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalDyadicRecords.actual_dyadic_large_second_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each epsilon>0 there is a constant C_epsilon independent of p, widths and selected bases. If every actual fiber has at least twice its actual maximum derivative-zero degree, the sum of its squared cardinalities is at most C_epsilon p^epsilon (XY/p^3)^5 (1+log(2p)/log 2). Neither a bound for the number of scales nor coordinate-height data is an input.

Both shortest-vector coordinates are nonzero: the first is a unit and the second follows from the original lattice relation and unit middle entries. The weighted square is therefore at least two. Reduction also bounds it by 2p^3. Dyadic annuli thus cover all actual shortest lengths using at most 2(1+log(2p)/log 2) scales. On each occupied annulus, the actual basis proves J1=8H/s0, J2=4Hs0/p^3, J1>=J2>2 and J1J2=32XY/p^3. The actual good-record second moment then bounds that annulus; summing the finite cover proves the global estimate.

**Theorem 1.2 (Retained endpoints without a minimum fiber size).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalDyadicRecords.actual_dyadic_retained_endpoint_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalDyadicRecords.actual_dyadic_retained_endpoint_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Without any minimum size assumption, the sum of actual fiber cardinalities is bounded by twice the sum of their actual bad degrees plus the square root of the number of original parameters times C_epsilon p^epsilon (XY/p^3)^5 (1+log(2p)/log 2).

Partition the actual finite parameters according to whether their fiber has at least twice its actual derivative-zero degree. Small fibers pay that degree once. Apply the proved global second moment to the large subset, then finite Cauchy-Schwarz and cardinality monotonicity. No supplied count, injection or coordinate box replaces an actual incidence.

This closes the physical scale summation and the small/large fiber split. The sum of bad degrees must still be bounded using PascadiOriginalBadDegree and the physical weight average. Recovering every original ReturnRows chart, absorbing small-prime and logarithmic losses, and assembling the final Pascadi prime-cube bound are separate remaining steps; this module does not claim that full conjecture.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalDyadicRecords.actual_dyadic_large_second_moment`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalDyadicRecords.actual_dyadic_retained_endpoint_count`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalGoodRecordMoment](PascadiOriginalGoodRecordMoment.md)
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalWeightAverage](PascadiOriginalWeightAverage.md)
