# Positive normalized stationary tuples

## Abstract

The stationary criterion holds for the arithmetic mean and a cubic Gini mean.

**Theorem 1.1 (The two characteristic derivatives).**

Lean statement: `D5/S3/ArithSums/GiniStationaryTest/Stationary.chiDeriv_parameters`

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/GiniStationaryTest/Stationary.chiDeriv_parameters` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. Grünwald; Zs. Páles (2024). *Comparison of Gini means with fixed number of variables*. URL: <https://arxiv.org/abs/2408.07658v1>.

*Commentary.*

At a positive real z, the characteristic derivative for (1,0) is one and the characteristic derivative for (2,-1) is (2z+1/z squared)/3. These formulas reduce the common multiplier equations to equality of one scalar function at every coordinate.

**Theorem 1.2 (Stationary tuples pass the comparison test).**

Lean statement: `D5/S3/ArithSums/GiniStationaryTest/Stationary.stationaryTest_one_zero_two_negOne`

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/GiniStationaryTest/Stationary.stationaryTest_one_zero_two_negOne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. Grünwald; Zs. Páles (2024). *Comparison of Gini means with fixed number of variables*. URL: <https://arxiv.org/abs/2408.07658v1>.

*Commentary.*

For every positive tuple of any nonzero length, normalization by the Gini parameters (1,0) means that the sum of coordinates equals the length. The two characteristic derivatives are 1 and (2z+1/z squared)/3. The stationary equations therefore place all coordinates on one common level of 2z+1/z squared.

Distinct positive points a and b on such a level satisfy a+b=2(ab) squared. For a third level point z, reciprocal substitution turns the level equation into (z inverse) cubed equal to an affine function of z inverse. The strictly convex cubic on the positive half-line cannot meet that affine function at three distinct points, so the level has at most two values. A nonconstant normalized tuple consequently has precisely two values a<1<b. If S=a+b and P=ab, each coordinate obeys z squared=S*z-P and 1/z=(S-z)/P. Summing and dividing by the tuple length gives second moment S-P and reciprocal moment (S-1)/P. Positivity of (1-a)(b-1)=(P-1)(2P+1) gives P>1. The difference of moments is (P-1)(1-a)(b-1)/P, which is positive. On the constant tuple both moments are one. Thus the Gini mean with parameters (2,-1) is at least one at every normalized stationary tuple, and it is strictly greater than one whenever the tuple is not constant.

## References

- Truth anchor: `D5/S3/ArithSums/GiniStationaryTest/Stationary.chiDeriv_parameters`
- Truth anchor: `D5/S3/ArithSums/GiniStationaryTest/Stationary.stationaryTest_one_zero_two_negOne`
- Dependency: [D5/S3/ArithSums/GiniStationaryTest/Defs](Defs.md)
- Dependency: [D5/S3/Quantum/Matrix/AlternativeMeanLinearization](../../Quantum/Matrix/AlternativeMeanLinearization.md)
