# Concept Entropy under Refinement

## Abstract

Refinement increases concept information and decreases residual entropy.

**Theorem 1.1 (Refinement increases information and decreases residual entropy).**

$$\begin{gathered}\forall X, C, D,\\{}[\operatorname{Fintype}(X)] [\operatorname{Fintype}(C)] [\operatorname{Fintype}(D)],\\{}mu: X \to \mathbb{R},\\{}q_{C}: X \to C, q_{D}: X \to D,\\{}((\forall x, 0 \leq mu(x)) \land \sum_{x} mu(x) = 1) \land \operatorname{Refines}(q_{C}, q_{D}) \Rightarrow\\{}(\operatorname{conceptInformation}(mu, q_{C}) \leq \operatorname{conceptInformation}(mu, q_{D})) \land\\{}(\operatorname{conceptResidual}(mu, q_{D}) \leq \operatorname{conceptResidual}(mu, q_{C})).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Information/RefinementEntropyMonotonicity.refinement_information_residual_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let mu be a normalized nonnegative mass function on a finite state carrier. Concept information is the Shannon entropy of the readout pushforward, while concept residual is the conditional entropy of the source state given that readout.

Both laws are constructed from mu and the canonical concept readouts. Refinement uses the family factorization relation: the coarse readout is obtained by deterministically forgetting the fine one.

The displayed information and residual inequalities are separate public conjuncts. The proof directly applies the frozen deterministic pushforward entropy classification and then the finite entropy chain rule to the graph-supported readout laws.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Information/RefinementEntropyMonotonicity.refinement_information_residual_monotone`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
- Dependency: [D5/S3/Entropy/Forgetting/DeterministicEntropyEquality](../../Entropy/Forgetting/DeterministicEntropyEquality.md)
