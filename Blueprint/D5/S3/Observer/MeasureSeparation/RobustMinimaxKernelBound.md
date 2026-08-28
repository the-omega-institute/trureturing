# Robust Minimax Kernel Bound

## Abstract

Robust policies, set-valued beliefs, and common-kernel binary risk bounds.

**Definition 1.1 (Worst-case model cost).**

$$\operatorname{worstCaseCost}\left(models, J, pi\right) = \operatorname{supModelCost}\left(models, J, pi\right)$$

*Formalization.* `D5/S3/Observer/MeasureSeparation/RobustMinimaxKernelBound.worstCaseCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source cost J_M is specialized to an extended nonnegative cost. The worst-case cost is its supremum over the supplied model set; the empty supremum is zero.

**Definition 1.2 (Minimax policies).**

$$\operatorname{minimaxPolicies}\left(models, J\right) = \operatorname{argminWorstCaseCost}\left(models, J\right)$$

*Formalization.* `D5/S3/Observer/MeasureSeparation/RobustMinimaxKernelBound.minimaxPolicies` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This named set is exactly argmin over policies of the model-wise supremum. It records exact minimizers without asserting that one exists.

**Definition 1.3 (Distributionally robust belief update).**

$$\operatorname{robustBeliefUpdate}\left(models, B, i, y\right) = \left\{\operatorname{BayesUpdate}\left(i, M, pi, y\right) \mid \operatorname{pair}\left(pi, M\right) \in \operatorname{product}\left(B, models\right)\right\}$$

*Formalization.* `D5/S3/Observer/MeasureSeparation/RobustMinimaxKernelBound.robustBeliefUpdate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The probability-law carrier is Mathlib PMF, the faithful discrete version of P(X). The update contains every Bayes update of every current PMF under every allowed model.

**Definition 1.4 (Binary zero-one error).**

$$\operatorname{binaryError}\left(mu, x\right) = \operatorname{mass}\left(mu, \operatorname{not}\left(x\right)\right)$$

*Formalization.* `D5/S3/Observer/MeasureSeparation/RobustMinimaxKernelBound.binaryError` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a Boolean truth, zero-one error is the PMF mass on the opposite label.

**Definition 1.5 (A fragile and a robust interface).**

$$\operatorname{channel}\left(fragile, nominal, x\right) = \operatorname{scaledBit}\left(\frac{1}{1000}, x\right) \land \operatorname{channel}\left(robust, M, x\right) = \operatorname{bit}\left(x\right)$$

*Formalization.* `D5/S3/Observer/MeasureSeparation/RobustMinimaxKernelBound.fragilityWitnessChannel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The false interface separates states only in the nominal model and changes by at most 1/1000 under misspecification. The true interface reports the state in both models.

**Definition 1.6 (Adversarial blind risk).**

$$\operatorname{fragilityBlindRisk}\left(i, M\right) = \operatorname{indicator}\left(\operatorname{channel}\left(i, M, false\right) = \operatorname{channel}\left(i, M, true\right)\right)$$

*Formalization.* `D5/S3/Observer/MeasureSeparation/RobustMinimaxKernelBound.fragilityBlindRisk` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The concrete zero-one design cost is one exactly when an interface is blind to the two states under the selected model, and zero otherwise.

**Definition 1.7 (Classifier for the necessity audits).**

$$\operatorname{classify}\left(\operatorname{dirac}\left(false\right)\right) = false \land \operatorname{classify}\left(\operatorname{dirac}\left(true\right)\right) = true$$

*Formalization.* `D5/S3/Observer/MeasureSeparation/RobustMinimaxKernelBound.separatedDiracClassifier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This law-level classifier distinguishes the two Boolean Dirac transcript laws.

**Theorem 1.8 (A small channel perturbation defeats the nominal interface).**

$$\operatorname{sensitivityAtMost}\left(\frac{1}{1000}\right) \land \left(\operatorname{separates}\left(fragile, nominal\right) \land \left(\left(\neg \operatorname{separates}\left(fragile, perturbed\right)\right) \land \left(\operatorname{separatesEveryModel}\left(robust\right) \land \left(\neg \operatorname{minimaxPolicies}\left(fragile\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/RobustMinimaxKernelBound.fragile_interface_not_minimax` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact nominal separability replaces mutual information in this witness. A 1/1000 response perturbation makes the fragile interface blind, while the robust interface remains separating and has lower worst-case cost. Primality is unused: prime is only the source's interface name.

**Theorem 1.9 (A common transcript kernel forces both binary lower bounds).**

$$\left(\operatorname{KernelFactorsThrough}\left(q, K\right) \land \left(\operatorname{q}\left(x\right) = \operatorname{q}\left(y\right) \land x \ne y\right)\right) \Rightarrow \left(\frac{1}{2} \le \operatorname{max}\left(errorX, errorY\right) \land \operatorname{min}\left(a, 1 - a\right) \le a \cdot errorX + \left(1 - a\right) \cdot errorY\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/RobustMinimaxKernelBound.common_kernel_minimax_lower_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The imported factorization theorem first makes the complete transcript laws equal on the common interface fiber. Congruence then gives the same classifier-output PMF. Its complementary Boolean masses sum to one, yielding max error at least 1/2 and Bayes risk at least min(a,1-a). The classifier is any function of the transcript law, which also covers deterministic and randomized final classifiers.

**Theorem 1.10 (Transcript factorization is necessary).**

$$\operatorname{booleanInterface}\left(false\right) = \operatorname{booleanInterface}\left(true\right) \land \left(\left(\neg \operatorname{KernelFactorsThrough}\left(booleanInterface, distinguishingBooleanTranscriptKernel\right)\right) \land \operatorname{maxError}\left(\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/RobustMinimaxKernelBound.transcript_factorization_is_necessary_for_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A constant interface has equal values at false and true, but the two Dirac transcript laws do not factor through it. The named classifier is perfect, so the one-half conclusion is false without factorization.

**Theorem 1.11 (The common-fiber premise is necessary).**

$$\operatorname{KernelFactorsThrough}\left(id, distinguishingBooleanTranscriptKernel\right) \land \left(\operatorname{id}\left(false\right) \ne \operatorname{id}\left(true\right) \land \operatorname{maxError}\left(\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/RobustMinimaxKernelBound.same_fiber_is_necessary_for_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity interface supports the factorized state-recording Dirac law, but false and true lie in different fibers and are classified without error.

**Theorem 1.12 (Distinct states are necessary).**

$$\operatorname{KernelFactorsThrough}\left(booleanInterface, constantBooleanTranscriptKernel\right) \land \left(x = y \land \operatorname{maxError}\left(\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/RobustMinimaxKernelBound.distinct_states_is_necessary_for_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At x equal to y equal to false, a constant transcript and constant correct classifier satisfy factorization and same-fiber equality but have zero error, contradicting a one-half bound.

## References

- Truth anchor: `D5/S3/Observer/MeasureSeparation/RobustMinimaxKernelBound.binaryError`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/RobustMinimaxKernelBound.common_kernel_minimax_lower_bounds`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/RobustMinimaxKernelBound.distinct_states_is_necessary_for_lower_bound`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/RobustMinimaxKernelBound.fragile_interface_not_minimax`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/RobustMinimaxKernelBound.fragilityBlindRisk`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/RobustMinimaxKernelBound.fragilityWitnessChannel`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/RobustMinimaxKernelBound.minimaxPolicies`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/RobustMinimaxKernelBound.robustBeliefUpdate`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/RobustMinimaxKernelBound.same_fiber_is_necessary_for_lower_bound`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/RobustMinimaxKernelBound.separatedDiracClassifier`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/RobustMinimaxKernelBound.transcript_factorization_is_necessary_for_lower_bound`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/RobustMinimaxKernelBound.worstCaseCost`
- Dependency: [D5/S3/Observer/MeasureSeparation/FactorizedTranscriptKernelBarrier](FactorizedTranscriptKernelBarrier.md)
