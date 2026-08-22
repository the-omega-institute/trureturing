# Translation Loss under Postprocessing

## Abstract

Deterministic postprocessing preserves target defects and cannot reduce target loss.

**Definition 1.1 (Joint readout-target law).**

$$\operatorname{readoutTargetLaw}(\mu, q, T) = \operatorname{pushforward}(\mu, x \mapsto (q(x), T(x))).$$

*Formalization.* `D5/S3/ConceptDynamics/Communication/TranslationLossMonotonicity.readoutTargetLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Push the finite state law through the paired map x maps to (q(x), T(x)). This directly constructs the joint law used by the source's conditional target entropy.

**Definition 1.2 (Target residual entropy).**

$$\operatorname{targetResidualEntropy}(\mu, q, T) = \operatorname{conditionalEntropy}(\operatorname{readoutTargetLaw}(\mu, q, T)).$$

*Formalization.* `D5/S3/ConceptDynamics/Communication/TranslationLossMonotonicity.targetResidualEntropy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Target residual entropy is the finite conditional entropy of T(X) after the readout q(X), evaluated on the constructed paired pushforward law.

**Theorem 1.3 (Translation loss is monotone under postprocessing).**

$$\begin{gathered}\forall X, Y, W, Z: \operatorname{Type},\\{}[\operatorname{Fintype}(X)], [\operatorname{Fintype}(Y)], [\operatorname{Fintype}(W)], [\operatorname{Fintype}(Z)],\\{}\mu: X \to \mathbb{R}, (\forall x: X, 0 \leq \mu(x)) \land \sum_{x} \mu(x) = 1,\\{}h: X \to Y, g: Y \to W, T: X \to Z,\\{}\operatorname{defectRelation}(h, T) \subseteq \operatorname{defectRelation}(g \circ h, T) \land\\{}\operatorname{targetResidualEntropy}(\mu, h, T) \leq \operatorname{targetResidualEntropy}(\mu, g \circ h, T).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Communication/TranslationLossMonotonicity.translation_loss_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let h be a finite readout, g a deterministic postprocessor, T a target, and mu a normalized nonnegative state law. The defect relation is the canonical set of state pairs merged by a readout but separated by T.

Applying g to equal h-values proves the first public inclusion directly. Thus every target distinction already lost by h remains lost after the translation chain.

For the second public conjunct, the proof constructs the deterministic Markov chain T(X), h(X), g(h(X)) and directly applies the accepted data-processing theorem. Entropy-chain and mutual-information identities convert that bound to the displayed conditional-target entropy inequality.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Communication/TranslationLossMonotonicity.readoutTargetLaw`
- Truth anchor: `D5/S3/ConceptDynamics/Communication/TranslationLossMonotonicity.targetResidualEntropy`
- Truth anchor: `D5/S3/ConceptDynamics/Communication/TranslationLossMonotonicity.translation_loss_monotone`
- Dependency: [D5/S3/ConceptDynamics/TargetRisk/RefinementRiskCostTradeoff](../TargetRisk/RefinementRiskCostTradeoff.md)
- Dependency: [D5/S3/Entropy/Forgetting/CapacityMonotone](../../Entropy/Forgetting/CapacityMonotone.md)
- Dependency: [D5/S3/Entropy/MutualInformationSymm](../../Entropy/MutualInformationSymm.md)
- Dependency: [D5/S3/Entropy/Submodularity/MarkovDataProcessing](../../Entropy/Submodularity/MarkovDataProcessing.md)
