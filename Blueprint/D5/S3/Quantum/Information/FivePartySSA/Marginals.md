# Five Party Actual Marginals

## Abstract

Tensor permutations and partial traces define all marginals used by the copy proof.

For a density on A tensor B tensor C tensor D tensor E, splitS puts the retained registers S first and their complement second. marginalS is reduceState splitS rho. Thus all entropy expressions belong to one actual density state; no abstract entropy-vector realization is assumed.

**Definition 1.1 (Discard the copied register).**

$$\operatorname{marginalABCD}\left(\rho\right) = \operatorname{TrE}\left(\rho\right)$$

*Formalization.* `D5/S3/Quantum/Information/FivePartySSA/Marginals.marginalABCD` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

marginalABCD traces the E index from the actual five-party matrix. The definition is consumed by the physical copy-discard identity and the marginal consistency lemmas.

## References

- Truth anchor: `D5/S3/Quantum/Information/FivePartySSA/Marginals.marginalABCD`
- Dependency: [D5/S3/Quantum/Information/MarginalCalculus](../MarginalCalculus.md)
