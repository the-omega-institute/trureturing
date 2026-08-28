# Source-Cutset Hitting Duality

## Abstract

Source cuts are exactly hitting sets of all minimal proof supports.

**Theorem 1.1 (Source cuts and minimal-support hitting sets have the same minimum size).**

$$\begin{gathered}\forall Source: \operatorname{Type}, P: Finset\left(Source\right) \to Prop,\\{}Fintype\left(Source\right) \land DecidableEq\left(Source\right) \land Monotone\left(P\right) \Rightarrow\\{}(\forall H: Finset\left(Source\right), IsSourceCut\left(P, H\right) \iff HitsEveryMinimalProofSupport\left(P, H\right)) \land\\{}proofResilience\left(P\right) = minimumHittingCardinality\left(P\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Provenance/SourceCutsetHittingDuality.source_cutset_hitting_duality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite source carrier and monotone provability predicate are the source primitives. A minimal proof support is a proving finite set with no proper proving subset. A source cut is a removal whose finite complement does not prove the conclusion.

If a cut missed a minimal support, monotonicity would make the remaining sources prove the conclusion. Conversely, any proving remainder has a least-cardinality proving subset, and that minimal support contradicts the claim that every minimal support was hit.

Proof resilience and minimum hitting cardinality are defined separately as natural infima. The cut-hitting equivalence identifies their candidate cardinality sets and therefore their minima.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Provenance/SourceCutsetHittingDuality.source_cutset_hitting_duality`
