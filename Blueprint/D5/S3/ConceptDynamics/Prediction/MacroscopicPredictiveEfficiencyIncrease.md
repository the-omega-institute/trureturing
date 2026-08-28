# Macroscopic Predictive Efficiency Increase

## Abstract

Removing fresh noise strictly improves predictive information per represented bit.

**Theorem 1.1 (Projection removes fresh noise while retaining absolute predictive information).**

$$\begin{gathered}\forall s, sNext, n, nNext\in Bool,\\{}p(((s, n), (sNext, nNext))) = \operatorname{if}\left(s = sNext, \frac{1}{8}, 0\right),\\{}c((s, n)) = s, q = \operatorname{coarseGrainedJoint}\left(p, c\right):\\{}\operatorname{ProbabilityLaw}\left(p\right) \land\\{}\forall s, n, nNext, p(((s, n), (s, nNext))) = \frac{1}{8} \land\\{}\forall s, sNext, n, nNext, s \neq sNext \Rightarrow p(((s, n), (sNext, nNext))) = 0 \land\\{}\forall x, \operatorname{marginal}\left(p\right)(x) = \frac{1}{4} \land\\{}\forall x, \operatorname{marginal}\left(\operatorname{swap}\left(p\right)\right)(x) = \frac{1}{4} \land\\{}\frac{\operatorname{shannonEntropy}\left(\operatorname{marginal}\left(p\right)\right)}{\operatorname{log}\left(2\right)} = 2 \land \frac{\operatorname{mutualInformation}\left(p\right)}{\operatorname{log}\left(2\right)} = 1 \land\\{}\frac{\frac{\operatorname{mutualInformation}\left(p\right)}{\operatorname{log}\left(2\right)}}{\frac{\operatorname{shannonEntropy}\left(\operatorname{marginal}\left(p\right)\right)}{\operatorname{log}\left(2\right)}} = \frac{1}{2} \land\\{}\forall b, \operatorname{marginal}\left(q\right)(b) = \frac{1}{2} \land\\{}\frac{\operatorname{shannonEntropy}\left(\operatorname{marginal}\left(q\right)\right)}{\operatorname{log}\left(2\right)} = 1 \land \frac{\operatorname{mutualInformation}\left(q\right)}{\operatorname{log}\left(2\right)} = 1 \land\\{}\frac{\frac{\operatorname{mutualInformation}\left(q\right)}{\operatorname{log}\left(2\right)}}{\frac{\operatorname{shannonEntropy}\left(\operatorname{marginal}\left(q\right)\right)}{\operatorname{log}\left(2\right)}} = 1 \land \frac{\frac{\operatorname{mutualInformation}\left(p\right)}{\operatorname{log}\left(2\right)}}{\frac{\operatorname{shannonEntropy}\left(\operatorname{marginal}\left(p\right)\right)}{\operatorname{log}\left(2\right)}} < \frac{\frac{\operatorname{mutualInformation}\left(q\right)}{\operatorname{log}\left(2\right)}}{\frac{\operatorname{shannonEntropy}\left(\operatorname{marginal}\left(q\right)\right)}{\operatorname{log}\left(2\right)}} \land\\{}\operatorname{mutualInformation}\left(q\right) = \operatorname{mutualInformation}\left(p\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Prediction/MacroscopicPredictiveEfficiencyIncrease.macroscopic_predictive_efficiency_strictly_increases` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The microscopic state consists of a persistent fair bit and a fresh fair noise bit. The displayed joint law gives mass one eighth to exactly the transitions that preserve the first coordinate.

Both microscopic time marginals are uniform on four states. Entropy and mutual information are converted from the repository's natural-log units to bits by division by log two.

The coarse concept keeps the persistent coordinate. Its marginal is fair, its entropy and mutual information are each one bit, and its efficiency is one rather than one half. Absolute mutual information stays equal.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Prediction/MacroscopicPredictiveEfficiencyIncrease.macroscopic_predictive_efficiency_strictly_increases`
- Dependency: [D5/S3/ConceptDynamics/Prediction/CoarseGrainingCannotAddInformation](CoarseGrainingCannotAddInformation.md)
- Dependency: [D5/S3/Entropy/MutualInformationEntropy](../../Entropy/MutualInformationEntropy.md)
