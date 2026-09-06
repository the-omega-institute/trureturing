# The exact admissible eight-tuple optimum

## Abstract

The exact admissible eight-tuple optimum.

**Theorem 1.1 (The exact admissible eight-tuple optimum).**

$$\operatorname{MinimalAdmissibleDiameter}\left(8, 26\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeGaps/OptimalAdmissibleEightTuple.minimalAdmissibleDiameter_eight_26` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

MinimalAdmissibleDiameter 8 26 asserts that an all-prime admissible natural eight-tuple exists in the width-26 window and that, for every natural C less than 26, no such tuple exists in the width-C window. The positive witness is {0,2,6,8,12,18,20,26}. The lower bound normalizes an arbitrary witness and applies a kernel-checked residue obstruction modulo 3, 5, and 7. This formalizes a standard numerical optimum and does not claim new number theory.

## References

- Truth anchor: `D5/S3/PrimeGaps/OptimalAdmissibleEightTuple.minimalAdmissibleDiameter_eight_26`
- Dependency: [D5/S3/PrimeGaps/AdmissibleWindowFiniteSearch](AdmissibleWindowFiniteSearch.md)
