# Optimal fixed counts for coloured parity seeds

## Abstract

The minimum coordinate fixed mass has an exact optimum at each feasible positive seed budget.

**Theorem 1.1 (The greatest minimum coordinate fixed count).**

$$\forall n \in Nat,\; \forall k \in Nat,\; 0 < k \Rightarrow ((\exists A \in \operatorname{UniformRealizations}\left(n, k\right),\; \forall i \in \operatorname{Coordinates}\left(n\right),\; \operatorname{BestCount}\left(n, k\right) \le \operatorname{FixedCount}\left(A, i\right)) \land (\forall A \in \operatorname{UniformRealizations}\left(n, k\right),\; \exists i \in \operatorname{Coordinates}\left(n\right),\; \operatorname{FixedCount}\left(A, i\right) \le \operatorname{BestCount}\left(n, k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/ParitySeedOptimization.best_fixed_seed_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coordinates(n) is Fin(n+2). UniformRealizations(n,k) consists of finite group sets of size N = 2 to the power n+3 times k with an equivariant map to the product of the even and odd coloured parity classes. An acting binary vector adds its entries over the zero coordinates of an output profile to that output colour, leaving the profile fixed. The two readouts have the same seed count above each of their possible coloured outputs. FixedCount(A,i) counts seeds fixed by the subgroup that acts only in coordinate i. BestCount(n,k) is four times M minus four times the ceiling of M divided by n+2, where M is k times 2 to the power n.

An equivariant map takes fixed seeds to fixed output pairs. Pooling the two colours and dividing each count by four gives an integer profile coupling of marginal multiplicity k. The sharp common-one bound for that coupling, multiplied by four, bounds the fixed-seed count.

Starting with a profile coupling that attains the sharp bound, retain every colour pair over each profile copy and let the group preserve the copy index. Then a seed is fixed in a coordinate exactly when both profile bits equal one in that coordinate.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/ParitySeedOptimization.best_fixed_seed_count`
- Dependency: [D5/S3/Combinatorics/Graph/Hypercube/ParityProfileMatching](../../Combinatorics/Graph/Hypercube/ParityProfileMatching.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/ParitySeedBudget](ParitySeedBudget.md)
