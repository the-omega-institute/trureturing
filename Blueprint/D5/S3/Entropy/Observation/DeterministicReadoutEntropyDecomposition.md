# Deterministic Readout Entropy Decomposition

## Abstract

A deterministic finite readout splits source entropy into retained and residual parts, while garbling can only increase the residual.

**Theorem 1.1 (Finite deterministic readouts split entropy and order residuals).**

$$\forall X \in Type, Fine \in Type, Coarse \in Type, mu \in X \to Real, q0 \in \operatorname{Concept}\left(X, Fine\right), q1 \in \operatorname{Concept}\left(X, Coarse\right), r \in Fine \to Coarse,\; \left(\left(\operatorname{Fintype}\left(X\right) \land \left(\operatorname{Fintype}\left(Fine\right) \land \operatorname{Fintype}\left(Coarse\right)\right)\right) \land \left(\left(\forall x \in X,\; 0 \le mu\left(x\right)\right) \land \left(\operatorname{sum}\left(mu\right) = 1 \land q1 = \operatorname{compose}\left(r, q0\right)\right)\right)\right) \Rightarrow \left(\operatorname{shannonEntropy}\left(mu\right) = \operatorname{conceptInformation}\left(mu, q0\right) + \operatorname{conceptResidual}\left(mu, q0\right) \land \operatorname{conceptResidual}\left(mu, q0\right) \le \operatorname{conceptResidual}\left(mu, q1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Observation/DeterministicReadoutEntropyDecomposition.deterministic_readout_entropy_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source, fine-readout, and coarse-readout carriers are finite. The source mass is nonnegative and normalized, so it represents the finite random state in the theorem.

The first conjunct identifies source entropy with the sum of the classification entropy retained by the fine readout and the conditional entropy remaining in its fibers.

The equation coarse = forget composed with fine is the deterministic garbling premise. The second conjunct states that the fine readout leaves no more conditional entropy than the coarse one.

## References

- Truth anchor: `D5/S3/Entropy/Observation/DeterministicReadoutEntropyDecomposition.deterministic_readout_entropy_decomposition`
- Dependency: [D5/S3/ConceptDynamics/Information/RefinementEntropyMonotonicity](../../ConceptDynamics/Information/RefinementEntropyMonotonicity.md)
- Dependency: [D5/S3/Entropy/Fusion/QuotientFiberDecomposition](../Fusion/QuotientFiberDecomposition.md)
