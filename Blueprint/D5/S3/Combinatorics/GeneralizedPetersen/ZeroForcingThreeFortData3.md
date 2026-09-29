# Forts for the outerPrev Anchor

## Abstract

An ordered family assigns a disjoint fort to every seven-vertex set with the specified first force.

**Theorem 1.1 (A complete ordered fort family).**

$$\exists rows \in \operatorname{List}\left(\mathrm{Nat}\times \mathrm{Nat}\right),\; \operatorname{familyOrderOK}\left(rows\right) = \mathrm{true} \land \left(\forall row \in \mathrm{Nat}\times \mathrm{Nat},\; row \in rows \Rightarrow \left(\operatorname{candidateShapeOK}\left(\mathrm{outerPrev}, \operatorname{fst}\left(row\right)\right) = \mathrm{true} \land \operatorname{rowOK}\left(row\right) = \mathrm{true}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFortData3.certifiedFamily` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

The outerPrev family has 7315 strictly increasing candidate masks. Each row satisfies candidateShapeOK for this anchor and rowOK, whose fortOK and disjointOK tests certify a nonempty fort disjoint from the candidate.

## References

- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFortData3.certifiedFamily`
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore](ZeroForcingThreeFiniteCore.md)
