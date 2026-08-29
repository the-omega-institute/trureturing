# Semantic Target-Laundering Bundle Elimination

## Abstract

Body-level semantic target laundering eliminates its coordinate witness bundle.

**Theorem 1.1 (Body-level laundering is characterized by protected-coordinate inequality).**

$$\begin{gathered}\forall Commitment, Evidence, Verdict, Time, TargetChain, Domain, Epsilon, Condition, Comparator, Baseline, WeightSpec, Report: \operatorname{Type},\\{}[\operatorname{LT}\left(Time\right)], [\operatorname{DecidableEq}\left(TargetChain\right)], [\operatorname{DecidableEq}\left(Domain\right)], [\operatorname{DecidableEq}\left(Epsilon\right)],\\{}[\operatorname{DecidableEq}\left(Condition\right)], [\operatorname{DecidableEq}\left(Comparator\right)], [\operatorname{DecidableEq}\left(Baseline\right)], [\operatorname{DecidableEq}\left(WeightSpec\right)],\\{}S: \operatorname{RegradeSemantics}\left(Commitment, Evidence, Verdict, Time, \operatorname{ProtectedCoordinates}\left(TargetChain, Domain, Epsilon, Condition, Comparator, Baseline, WeightSpec\right), Report\right),\\{}oldK, newK: Commitment, Z: Evidence, regrade: \operatorname{SemanticRegrade}\left(S\right),\\{}\operatorname{SemanticTargetLaunderingAt}\left(S, oldK, newK, Z, regrade\right) \iff\\{}\operatorname{SemanticRegradeAt}\left(regrade, oldK, newK, Z\right) \land\\{}\operatorname{PostArrivalSemanticRegrade}\left(S, regrade\right) \land\\{}S.reportAttributedTo(regrade.report) = oldK \land\\{}S.protected(oldK) \neq S.protected(newK).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeRegrade/SemanticTargetLaunderingBundleElimination.semantic_target_laundering_iff_protected_coordinates_ne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The semantic frame reads protected coordinates, evaluations, timing, and report fields from existing carriers. SemanticTargetLaunderingAt retains report identity, strict post-arrival timing, attribution to the original commitment, and a closed nonempty coordinate witness bundle.

The frozen coordinate-bundle characterization replaces only that final bundle with inequality of the complete protected-coordinate records. No report condition, timing condition, or attribution condition is removed, and neither verdict change nor a report-timestamp equality is assumed.

This discharges obligation 57.2-C from definition-escape-completion-theory atom generic-residual-c42f6cc861bde491da258e3f06a84362929990f099ec729da096b9d25774bb1b.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeRegrade/SemanticTargetLaunderingBundleElimination.semantic_target_laundering_iff_protected_coordinates_ne`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscapeRegrade/CoordinateWitnessBundle](CoordinateWitnessBundle.md)
