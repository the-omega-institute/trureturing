# Prediction Stability from Zero Conditional Entropy

## Abstract

Full support identifies stability depth with first zero conditional entropy.

**Theorem 1.1 (Prediction stability depth is the first zero conditional entropy).**

$$\begin{gathered}\forall Y, O, [\operatorname{Fintype}(Y)] [\operatorname{Fintype}(O)],\\tau: Y \to Y, q: Y \to O, p: Y \to \mathbb{R},\\(\forall y, 0 < p(y)) \Rightarrow\\\operatorname{predictionStabilityDepth}(tau, q) = \operatorname{sInf} \{m \in \mathbb{N} \mid \operatorname{conditionalEntropy}(\operatorname{nextReadoutJointLaw}(tau, q, p, m)) = 0\}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/ConditionalEntropyStability.prediction_stability_depth_eq_conditional_entropy_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Y and O be finite types, tau a deterministic state update, q a readout, and p a strictly positive real weight on every state. The word at depth m consists of the readouts at times zero through m. Prediction is stable at m when equality of those words forces equality of the readout at time m+1.

The joint weight nextReadoutJointLaw records each depth-m word together with its next readout. Strict positivity makes every realized word fiber carry positive mass. The frozen repository theorem conditional_entropy_eq_zero_iff_point_mass_on_support then says exactly that each such fiber has one next-readout value. Equality of the stable-depth set and zero-entropy-depth set yields equality of their natural infima.

The pinned-library search found Nat.sInf_mem and Nat.sInf_def for the minimum semantics and Finset.single_le_sum for positivity of a realized pushforward cell; all three are applied in Lean. The library has no matching finite conditional-entropy theorem. LeanSearch returned only unrelated binary-entropy and measure-level conditional-distribution results, while the repository search found the slice-level theorem but no prediction-depth characterization.

A normalized full-support probability law is a special case: normalization is not required because the conditional ratios and their point-mass property are unchanged by positive common scaling. The theorem is finite and deterministic. It supplies no stochastic-process or measure-theoretic extension and no quantitative upper bound on the first stable depth.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/ConditionalEntropyStability.prediction_stability_depth_eq_conditional_entropy_zero`
- Dependency: [D5/S3/Entropy/ConditionalEntropyEquality](../../Entropy/ConditionalEntropyEquality.md)
- Dependency: [D5/S3/Entropy/Forgetting/CapacityMonotone](../../Entropy/Forgetting/CapacityMonotone.md)
