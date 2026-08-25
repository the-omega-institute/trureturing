# Canonical Completion Information Chain Decomposition

## Abstract

Canonical source laws express the observation-word chain rule and stable completion information decomposition without redeclaring induced distributions.

**Theorem 1.1 (Completion information decomposes through the canonical laws).**

$$\begin{gathered}\forall m \geq 0, H(W_{m}) = H(O_{0}) + \sum_{k=1}^{m} H(O_{k} \mid W_{k-1}),\\{}E: \operatorname{range}(W_{m_{*}}) \equiv CompletedState,\\{}\forall y, E(W_{m_{*}}(y)) = \operatorname{completionProjection}(y),\\{}H(CompletedState \mid O_{0}) = \sum_{k=1}^{m_{*}} H(O_{k} \mid W_{k-1}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Observation/CompletionInformationChainDecompositionCanonical.completion_information_chain_decomposition_canonical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Y and O be finite, with a deterministic update, a readout, and a normalized nonnegative initial mass. The word law is conceptLaw applied to futureReadoutWord, and each increment is the canonical nextReadoutJointLaw.

At a depth where consecutive word kernels agree, the named stable realized-word equivalence computes to completionProjection on every source state. This is the canonical bijection used by the entropy identity, not an equivalence chosen from that identity.

The final conditional entropy uses completionLaw on the initial readout and completionProjection. Unfolding these three imported canonical laws reduces the statement to the frozen chain-decomposition machinery.

Pinned Mathlib searches found no matching finite real-valued Shannon chain rule. Repository exact hits entropy_chain_rule, shannonEntropy_extend_injective, finiteWordRangeEquiv, and stableCompletionEquiv supply the imported proof.

## References

- Truth anchor: `D5/S3/Entropy/Observation/CompletionInformationChainDecompositionCanonical.completion_information_chain_decomposition_canonical`
- Dependency: [D5/S3/ConceptDynamics/Completion/CompletionInformationCost](../../ConceptDynamics/Completion/CompletionInformationCost.md)
- Dependency: [D5/S3/ConceptDynamics/Information/RefinementEntropyMonotonicity](../../ConceptDynamics/Information/RefinementEntropyMonotonicity.md)
- Dependency: [D5/S3/Entropy/Observation/CompletionInformationChainDecomposition](CompletionInformationChainDecomposition.md)
- Dependency: [D5/S3/ObserverMemory/Prediction/ConditionalEntropyStability](../../ObserverMemory/Prediction/ConditionalEntropyStability.md)
