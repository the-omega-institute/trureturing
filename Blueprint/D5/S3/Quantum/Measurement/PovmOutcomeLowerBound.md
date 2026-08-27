# POVM Outcome Lower Bound

## Abstract

A normalized finite effect family needs at least d squared outcomes for completeness.

**Theorem 1.1 (An informationally complete POVM has at least d squared outcomes).**

$$\begin{gathered}\forall d, m: \operatorname{Nat}, \operatorname{NeZero}\left(d\right),\\{}E: \operatorname{Fin}\left(m\right) \to \operatorname{HermitianSpace}\left(d\right),\\{}\sum_{a \in \operatorname{Fin}\left(m\right)} E_{a} = \operatorname{identityHermitian}\left(d\right) \Rightarrow\\{}C_{a} := \operatorname{centeredHermitianMap}\left(d, E_{a}\right),\\{}\sum_{a \in \operatorname{Fin}\left(m\right)} C_{a} = 0 \land\\{}\operatorname{finrank}\left(\mathbb{R}, \operatorname{span}\left(\mathbb{R}, \{C_{a}: a \in \operatorname{Fin}\left(m\right)\}\right)\right) \leq m - 1 \land\\{}(\operatorname{span}\left(\mathbb{R}, \{C_{a}: a \in \operatorname{Fin}\left(m\right)\}\right) = \operatorname{traceZeroHermitian}\left(d\right) \Rightarrow d^{2} \leq m).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/PovmOutcomeLowerBound.povm_outcome_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The effects are a finite family on the canonical real Hermitian carrier whose sum is the identity. The displayed centered family is constructed by the repository's canonical trace-removal map.

Normalization gives a nonzero all-ones coefficient relation among the centered effects. Their real span therefore has dimension at most one less than the number of outcomes.

When that span is the whole real trace-zero Hermitian carrier, its dimension is d squared minus one, so the outcome count is at least d squared.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/PovmOutcomeLowerBound.povm_outcome_lower_bound`
- Dependency: [D5/S3/Quantum/PredictionDepth/FiniteSequentialWordCertificate](../PredictionDepth/FiniteSequentialWordCertificate.md)
- Dependency: [D5/S3/Quantum/Tomography/InformationalCompletenessEquivalence](../Tomography/InformationalCompletenessEquivalence.md)
