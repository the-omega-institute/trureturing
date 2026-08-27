# Source-Cutset Inclusion-Minimal Hitting Duality

## Abstract

Source cuts are exactly the hitting sets of the canonical family of inclusion-minimal proof supports, with equal minimum cardinalities.

**Theorem 1.1 (Source cuts and canonical minimal-support hitting sets coincide).**

$$\begin{gathered}\forall Source: \operatorname{Type}, P: \operatorname{Finset}\left(Source\right) \to Prop,\\{}\operatorname{Fintype}\left(Source\right) \land \operatorname{DecidableEq}\left(Source\right) \land \operatorname{Monotone}\left(P\right) \Rightarrow\\{}\operatorname{let} hitsEveryInclusionMinimalSupport := \lambda H: \operatorname{Finset}\left(Source\right), \forall S: \operatorname{Finset}\left(Source\right), \operatorname{InclusionMinimalSupport}\left(P, S\right) \Rightarrow \operatorname{Nonempty}\left(\operatorname{inter}\left(H, S\right)\right)\\{}\operatorname{in} (\forall H: \operatorname{Finset}\left(Source\right), \operatorname{IsSourceCut}\left(P, H\right) \iff \operatorname{hitsEveryInclusionMinimalSupport}\left(H\right)) \land\\{}\operatorname{proofResilience}\left(P\right) = \operatorname{sInf}\left(\{n: \mathbb{N} \mid \exists H: \operatorname{Finset}\left(Source\right), \operatorname{hitsEveryInclusionMinimalSupport}\left(H\right) \land \operatorname{card}\left(H\right) = n\}\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Provenance/SourceCutsetInclusionMinimalHittingDuality.source_cutset_inclusion_minimal_hitting_duality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite source carrier, decidable equality, and monotone provability predicate are explicit premises. InclusionMinimalSupport is imported from the canonical dependency-support family.

The displayed local predicate expands hitting every canonical minimal support. It is not identified with the cut predicate: the equivalence is inherited from the frozen source-cutset theorem through the exact alpha-equivalence of the old and canonical support predicates.

Proof resilience retains its independent frozen definition as the least source-cut cardinality. The second conjunct identifies it with the natural infimum of cardinalities satisfying the displayed hitting predicate.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Provenance/SourceCutsetInclusionMinimalHittingDuality.source_cutset_inclusion_minimal_hitting_duality`
- Dependency: [D5/S3/ConceptDynamics/DagCompletion/MinimalDependencySupport](../DagCompletion/MinimalDependencySupport.md)
- Dependency: [D5/S3/ConceptDynamics/Provenance/SourceCutsetHittingDuality](SourceCutsetHittingDuality.md)
