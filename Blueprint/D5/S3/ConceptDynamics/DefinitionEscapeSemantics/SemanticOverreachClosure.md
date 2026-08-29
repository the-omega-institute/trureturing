# Semantic Overreach Closure

## Abstract

Semantic overreach is exactly the absence of a licensed closing report.

**Theorem 1.1 (Strict expansion overreaches exactly when no report license closes it).**

$$\begin{gathered}\forall S, report, J,\\{}\operatorname{SemanticStrictSubset}\left(S, J, \operatorname{reportedDomain}\left(report\right)\right) \Rightarrow\\{}\operatorname{claimScope}\left(S, \operatorname{claim}\left(report\right)\right) = J \Rightarrow\\{}(\operatorname{SemanticOverreach}\left(S, report, J\right) \iff \neg \operatorname{OverreachClosure}\left(S, report, J\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeSemantics/SemanticOverreachClosure.semantic_overreach_iff_not_overreach_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A licensed semantic transport report carries a typed certificate for the same claim, source domain, reported domain, and claim version, and preserves the certificate premises exactly as its condition.

Given the directed strict expansion and the exact original claim scope, semantic overreach is equivalent to the absence of that license. The argument is constructive and uses neither closure decidability nor double-negation elimination.

This discharges obligation 57.3-D from definition-escape-completion-theory atom generic-residual-6a153578be42b0dc05d1bf74fa4fe146f63b6fc6a6e6cee245ad9a9835653ca4.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeSemantics/SemanticOverreachClosure.semantic_overreach_iff_not_overreach_closure`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscapeSemantics/SemanticTransportCertificateValidity](SemanticTransportCertificateValidity.md)
