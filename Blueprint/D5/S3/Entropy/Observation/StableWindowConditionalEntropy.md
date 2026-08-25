# Stable Window Conditional Entropy

## Abstract

Stable finite observation kernels have zero next-readout conditional entropy, and a full-support law detects kernel stability.

**Theorem 1.1 (Kernel stability and zero conditional entropy).**

$$\begin{gathered}\forall Y, O: \operatorname{FiniteType},\\{}F: Y \to Y, q: Y \to O, n: N,\\{}((\operatorname{kernel}(\operatorname{futureReadoutWord}(F, q, n)) = \operatorname{kernel}(\operatorname{futureReadoutWord}(F, q, n + 1))) \Rightarrow \forall p: Y \to R, (\operatorname{ProbabilityLaw}(p)) \Rightarrow (\operatorname{conditionalEntropy}(\operatorname{nextReadoutJointLaw}(F, q, p, n)) = 0)) \land\\{}(\forall p: Y \to R, (\operatorname{ProbabilityLaw}(p) \land \operatorname{FullSupport}(p)) \Rightarrow (\operatorname{conditionalEntropy}(\operatorname{nextReadoutJointLaw}(F, q, p, n)) = 0) \Rightarrow (\operatorname{kernel}(\operatorname{futureReadoutWord}(F, q, n)) = \operatorname{kernel}(\operatorname{futureReadoutWord}(F, q, n + 1)))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Observation/StableWindowConditionalEntropy.stable_window_conditional_entropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite word and its consecutive kernels are the canonical futureReadoutWord objects. The joint law is the deterministic pushforward pairing the word through depth n with the next readout.

If the consecutive kernels agree, the next readout is constant on every word fiber. The imported point-mass criterion therefore makes its conditional entropy zero for every normalized initial law, including laws that do not have full support.

Conversely, strict positivity gives every state and every realized word positive mass. Zero conditional entropy then forces both next readouts in any common word fiber to equal the same point-mass value, which reconstructs equality of the consecutive kernels.

## References

- Truth anchor: `D5/S3/Entropy/Observation/StableWindowConditionalEntropy.stable_window_conditional_entropy`
- Dependency: [D5/S3/ObserverMemory/Prediction/ConditionalEntropyStability](../../ObserverMemory/Prediction/ConditionalEntropyStability.md)
