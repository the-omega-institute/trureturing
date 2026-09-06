# Conditional Information and Support Sufficiency

## Abstract

For a finite prior and stochastic target kernel, zero conditional information is equivalent both to conditional independence and to target-kernel constancy on every positive-prior concept fiber.

**Theorem 1.1 (Zero conditional information characterizes support sufficiency).**

$$\forall X \in Type, C \in Type, Y \in Type,\; \left(\operatorname{Fintype}\left(X\right) \land \left(\operatorname{Fintype}\left(C\right) \land \operatorname{Fintype}\left(Y\right)\right)\right) \Rightarrow \left(\forall mu \in \operatorname{PMF}\left(X\right), K \in X \to \operatorname{PMF}\left(Y\right), concept \in X \to C,\; \operatorname{let} jointLaw := ((x,(c,y)) \mapsto \operatorname{ite}\left(c = concept\left(x\right), \operatorname{toReal}\left(mu\left(x\right)\right) \cdot \operatorname{toReal}\left(K\left(x\right)\left(y\right)\right), 0\right)); \operatorname{let} conditionedLaw := \operatorname{yFirstLaw}\left(jointLaw\right); \left(\operatorname{conditionalMutualInformation}\left(conditionedLaw\right) = 0 \Leftrightarrow \left(\forall c \in C,\; \operatorname{marginal}\left(conditionedLaw, c\right) \ne 0 \Rightarrow \operatorname{conditional}\left(conditionedLaw, c\right) = ((x,y): \operatorname{Prod}\left(X, Y\right) \mapsto \operatorname{marginal}\left(\operatorname{conditional}\left(conditionedLaw, c\right), x\right) \cdot \operatorname{marginal}\left(((y,x): \operatorname{Prod}\left(Y, X\right) \mapsto \operatorname{conditional}\left(conditionedLaw, c, x, y\right)), y\right))\right)\right) \land \left(\operatorname{conditionalMutualInformation}\left(conditionedLaw\right) = 0 \Leftrightarrow \left(\forall x \in X, xprime \in X,\; \left(0 < \operatorname{toReal}\left(mu\left(x\right)\right) \land \left(0 < \operatorname{toReal}\left(mu\left(xprime\right)\right) \land concept\left(x\right) = concept\left(xprime\right)\right)\right) \Rightarrow K\left(x\right) = K\left(xprime\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Completion/ConditionalInformationSufficiency.conditional_information_zero_iff_support_sufficiency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite PMF prior, a PMF-valued target kernel, and a deterministic concept readout construct the displayed joint law. The concept coordinate is moved first before conditional information is read.

The first equivalence is the conditional-product law on every occupied concept fiber. The second equivalence says precisely that two positive-prior states with the same concept have the same target law.

For the reverse implication, one positive-prior representative is chosen from each occupied fiber. Its target law supplies a normalized channel, and the resulting Markov factorization forces zero conditional information.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Completion/ConditionalInformationSufficiency.conditional_information_zero_iff_support_sufficiency`
- Dependency: [D5/S3/Entropy/Submodularity/MarkovDataProcessing](../../Entropy/Submodularity/MarkovDataProcessing.md)
