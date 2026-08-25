# Target-Pair Coverage and Information Contrast

## Abstract

Finite target identification is a pair-cover condition that positive statistical information alone need not satisfy.

**Theorem 1.1 (Target-pair coverage is not replaced by mutual information).**

$$\begin{aligned}(\forall n: Nat, E, R, Y: \operatorname{Type},\\\operatorname{DecidableEq}\left(E\right) \Rightarrow \forall A: \operatorname{Finset}\left(E\right),\\r: E \to \operatorname{Fin}\left(n\right) \to R, T: \operatorname{Fin}\left(n\right) \to Y,\\(\forall i, j: \operatorname{Fin}\left(n\right), T(i) \neq T(j) \Rightarrow \exists a \in A,\\r(a)(i) \neq r(a)(j)) \iff \\\{\{i, j\} \mid T(i) \neq T(j)\} \subseteq \operatorname{Union}\left(a \in A, \{\{i, j\} \mid r(a)(i) \neq r(a)(j)\}\right)) \land \\(\operatorname{let} \mu: Bool \times Bool \to \mathbb{R} := ((b, c) \mapsto \operatorname{if}\left(b = false, \frac{1}{2}, 0\right)), \\e: Bool \times Bool \to Bool := ((b, c) \mapsto c), \\T: Bool \times Bool \to Bool := ((b, c) \mapsto b)\;\\\operatorname{mutualInformation}\left(\operatorname{readoutTargetLaw}\left(\mu, e, id\right)\right) = \log 2 \land e((false, false)) \neq e((false, true)) \land \\T((false, false)) = T((false, true)) \land e((false, false)) = e((true, false)) \land \\T((false, false)) \neq T((true, false)) \land \neg\exists f: Bool \to Bool, T = f \circ e).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiment/TargetPairCoverageInformationContrast.target_pair_coverage_and_information_contrast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finitely indexed models and a finite selected experiment set, target identification is equivalent to covering every unordered target-disagreement pair by one selected experiment's separation set. This is the finite hitting-set form of the cover criterion.

The concrete prior is supported on two models with the same target. Reading the nuisance coordinate carries exactly log two nats about the full model and separates those same-target models.

A second displayed pair has different targets but the same experiment response. Consequently the target cannot factor through the experiment, despite its positive model information.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Experiment/TargetPairCoverageInformationContrast.target_pair_coverage_and_information_contrast`
- Dependency: [D5/S3/ConceptDynamics/Communication/TranslationLossMonotonicity](../Communication/TranslationLossMonotonicity.md)
- Dependency: [D5/S3/ConceptDynamics/Interventions/TargetRelativePairUniverse](../Interventions/TargetRelativePairUniverse.md)
