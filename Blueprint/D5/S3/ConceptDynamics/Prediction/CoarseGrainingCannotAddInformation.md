# Coarse-Graining Cannot Add Information

## Abstract

Deterministic coarse-graining preserves finite probability laws and cannot increase mutual information.

**Lemma 1.1 (A deterministic right-coordinate image preserves probability laws).**

$$\begin{gathered}\forall A, B, D: \operatorname{Type},\\{}[\operatorname{Fintype}(A)] [\operatorname{Fintype}(B)] [\operatorname{Fintype}(D)],\\p: A \times B \to \mathbb{R}, f: B \to D,\\\operatorname{ProbabilityLaw}(p) \Rightarrow \operatorname{ProbabilityLaw}(\operatorname{deterministicRight}\left(p, f\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Prediction/CoarseGrainingCannotAddInformation.deterministicRight_is_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Start with a normalized nonnegative mass function on A times B and send only its B-coordinate through a deterministic map f. The mass at (a,d) is the sum of p(a,b) over the fiber f(b)=d, so it remains nonnegative. Summing over d counts every b exactly once and preserves total mass one.

**Lemma 1.2 (Deterministic right-coordinate processing cannot increase information).**

$$\begin{gathered}\forall A, B, D: \operatorname{Type},\\{}[\operatorname{Fintype}(A)] [\operatorname{Fintype}(B)] [\operatorname{Fintype}(D)],\\p: A \times B \to \mathbb{R}, f: B \to D,\\\operatorname{ProbabilityLaw}(p) \Rightarrow \operatorname{mutualInformation}(\operatorname{deterministicRight}\left(p, f\right)) \leq \operatorname{mutualInformation}(p).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Prediction/CoarseGrainingCannotAddInformation.mutual_information_deterministic_right_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The map f defines the deterministic channel W(b,d)=1 when f(b)=d and zero otherwise. Coupling this channel to p gives a normalized Markov law A to B to D whose A-B marginal is p and whose A-D marginal is the deterministic right-coordinate image.

Markov data processing therefore bounds the mutual information between A and f(B) by that between A and B. The result applies to every map f; no injectivity or surjectivity is required.

**Theorem 1.3 (Coarse-graining both states cannot add mutual information).**

$$\begin{gathered}\forall X, C: \operatorname{Type},\\{}[\operatorname{Fintype}(X)] [\operatorname{Fintype}(C)],\\p: X \times X \to \mathbb{R}, c: X \to C,\\\operatorname{ProbabilityLaw}(p) \Rightarrow \operatorname{mutualInformation}(\operatorname{coarseGrainedJoint}\left(p, c\right)) \leq \operatorname{mutualInformation}(p).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Prediction/CoarseGrainingCannotAddInformation.coarse_graining_cannot_add_information` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the same deterministic concept map to both coordinates of a finite joint law. Processing the second coordinate first cannot increase mutual information. Coordinate-swap symmetry then turns processing the first coordinate into a second application of the same one-coordinate data-processing bound.

The resulting law is exactly the fiber-sum coarseGrainedJoint: each coarse pair receives all microscopic mass mapped to it. Thus the mutual information between consecutive coarse states is at most the mutual information between the original microscopic states.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Prediction/CoarseGrainingCannotAddInformation.coarse_graining_cannot_add_information`
- Truth anchor: `D5/S3/ConceptDynamics/Prediction/CoarseGrainingCannotAddInformation.deterministicRight_is_law`
- Truth anchor: `D5/S3/ConceptDynamics/Prediction/CoarseGrainingCannotAddInformation.mutual_information_deterministic_right_le`
- Dependency: [D5/S3/Entropy/MutualInformationSymm](../../Entropy/MutualInformationSymm.md)
- Dependency: [D5/S3/Entropy/Submodularity/MarkovDataProcessing](../../Entropy/Submodularity/MarkovDataProcessing.md)
