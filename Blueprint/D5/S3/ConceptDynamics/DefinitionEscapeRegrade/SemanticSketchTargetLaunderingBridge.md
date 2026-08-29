# Semantic Sketch Target-Laundering Bridge

## Abstract

An exact temporal bridge identifies sketch laundering with body laundering plus its report timestamp.

**Theorem 1.1 (Sketch laundering is body laundering plus the sketch timestamp).**

$$\begin{gathered}\forall Commitment, Evidence, Verdict, Time, TargetChain, Domain, Epsilon, Condition, Comparator, Baseline, WeightSpec, Report: \operatorname{Type},\\{}[\operatorname{LT}\left(Time\right)],\\{}S: \operatorname{RegradeSemantics}\left(Commitment, Evidence, Verdict, Time, \operatorname{ProtectedCoordinates}\left(TargetChain, Domain, Epsilon, Condition, Comparator, Baseline, WeightSpec\right), Report\right),\\{}oldK, newK: Commitment, Z: Evidence,\\{}regrade: \operatorname{SemanticRegrade}\left(S\right), bridge: \operatorname{RegradeTemporalBridge}\left(S\right),\\{}\operatorname{SemanticSketchTargetLaunderingAt}\left(S, oldK, newK, Z, regrade\right) \iff\\{}\operatorname{SemanticTargetLaunderingAt}\left(S, oldK, newK, Z, regrade\right) \land\\{}S.reportOccurredAt(regrade.report) = S.freezeTime(newK).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeRegrade/SemanticSketchTargetLaunderingBridge.semantic_sketch_target_laundering_iff_body_and_timestamp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary semantic regrade frame, commitments, evidence, and regrade report, assume the explicit RegradeTemporalBridge equating freeze visibility with strict arrival before the commitment freeze.

The bridge converts only the temporal clause. Report identity, original attribution, and the closed nonempty protected-coordinate witness bundle remain unchanged, while the sketch-only report timestamp is retained as the additional conjunct.

This discharges obligation 57.2-D from definition-escape-completion-theory atom generic-residual-b41cab36c0664076d72484d1cc20fe14a1f832df6131b1650816f3eb19119363.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeRegrade/SemanticSketchTargetLaunderingBridge.semantic_sketch_target_laundering_iff_body_and_timestamp`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscapeRegrade/SemanticTargetLaunderingBundleElimination](SemanticTargetLaunderingBundleElimination.md)
