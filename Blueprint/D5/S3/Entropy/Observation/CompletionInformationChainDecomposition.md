# Observation-Word and Completion Information Decomposition

## Abstract

Finite observation words obey the Shannon chain rule, and stable completion information is the sum of the later conditional observation entropies.

**Theorem 1.1 (Completion information decomposes along the observation chain).**

$$\begin{gathered}\forall m \geq 0, H(W_{m}) = H(O_{0}) + \sum_{k=1}^{m} H(O_{k} \mid W_{k-1}),\\{}E: \operatorname{range}(W_{m_{*}}) \equiv CompletedState,\\{}\forall y, E(W_{m_{*}}(y)) = \operatorname{completionProjection}(y),\\{}H(CompletedState \mid O_{0}) = \sum_{k=1}^{m_{*}} H(O_{k} \mid W_{k-1}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Observation/CompletionInformationChainDecomposition.completion_information_chain_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Y and O be finite, let tau : Y -> Y be a deterministic update, and let q : Y -> O be a readout. A normalized nonnegative initial mass function induces the law of each word W_m = (O_0, ..., O_m) by pushforward through the iterated readout map.

For every m, splitting the final coordinate identifies the word law at depth m + 1 with the joint law of W_m and O_(m+1). The imported finite entropy chain rule gives one conditional term, and induction gives the displayed finite sum with H(O_0) as its base.

At a depth where consecutive observation kernels agree, the named stableObservationCompletionEquiv composes the canonical kernel-range equivalence with the existing stable finite-to-complete quotient equivalence. Its public computation rule sends every realized word to the canonical completion class of the realizing state.

The law of (O_0, completion) has the same joint entropy as the stable word law: both are injective relabelings of their common realized quotient. Applying the chain rule once more and canceling H(O_0) proves the stable conditional-entropy identity. No observation law, completion object, or stable depth is defined from the target equality.

Pinned-library searches found no finite real-valued Shannon chain rule. Repository exact hits entropy_chain_rule, shannonEntropy_extend_injective, futureReadoutWord, finiteWordRangeEquiv, and stableCompletionEquiv are applied directly.

## References

- Truth anchor: `D5/S3/Entropy/Observation/CompletionInformationChainDecomposition.completion_information_chain_decomposition`
- Dependency: [D5/S3/Entropy/Forgetting/CapacityMonotone](../Forgetting/CapacityMonotone.md)
- Dependency: [D5/S3/Entropy/Relabeling/InjectiveInvariance](../Relabeling/InjectiveInvariance.md)
- Dependency: [D5/S3/ObserverMemory/Refinement/GradedPredictionShift](../../ObserverMemory/Refinement/GradedPredictionShift.md)
