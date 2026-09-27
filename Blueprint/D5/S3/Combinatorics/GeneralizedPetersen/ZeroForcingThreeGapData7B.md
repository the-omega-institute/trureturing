# Bounded Gap Roots

## Abstract

The mask recurrence accepts the stated rooted bounded-gap families.

**Theorem 1.1 (7 gaps with root 5 to 6).**

$$\forall q \in \mathrm{Nat},\; \left(5 \le q \land q \le 6\right) \Rightarrow \operatorname{maskCheck}\left(7, 6, q, [q]\right) = \mathrm{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapData7B.roots7` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

For 7 positive gaps, maskCheck accepts the root prefix [q] with 6 remaining entries and maximum gap q, for q from 5 through 6.

## References

- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapData7B.roots7`
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute](ZeroForcingThreeGapCompute.md)
