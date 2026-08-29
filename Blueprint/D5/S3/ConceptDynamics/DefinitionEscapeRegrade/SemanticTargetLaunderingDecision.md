# Semantic Target-Laundering Decision

## Abstract

Decidable protected coordinates and report conditions yield an exact laundering decision.

**Theorem 1.1 (The laundering predicate has a certified Boolean decision).**

$$\begin{gathered}\forall Commitment, Evidence, Verdict, Time, TargetChain, Domain, Epsilon, Condition, Comparator, Baseline, WeightSpec, Report: \operatorname{Type},\\{}[\operatorname{LT}\left(Time\right)],\\{}[\operatorname{DecidableEq}\left(Commitment\right)], [\operatorname{DecidableEq}\left(Evidence\right)],\\{}[\operatorname{DecidableEq}\left(TargetChain\right)], [\operatorname{DecidableEq}\left(Domain\right)], [\operatorname{DecidableEq}\left(Epsilon\right)],\\{}[\operatorname{DecidableEq}\left(Condition\right)], [\operatorname{DecidableEq}\left(Comparator\right)], [\operatorname{DecidableEq}\left(Baseline\right)], [\operatorname{DecidableEq}\left(WeightSpec\right)],\\{}[\operatorname{DecidableRel}\left((\cdot < \cdot): Time \to Time \to Prop\right)],\\{}S: \operatorname{RegradeSemantics}\left(Commitment, Evidence, Verdict, Time, \operatorname{ProtectedCoordinates}\left(TargetChain, Domain, Epsilon, Condition, Comparator, Baseline, WeightSpec\right), Report\right),\\{}oldK, newK: Commitment, Z: Evidence,\\{}regrade: \operatorname{SemanticRegrade}\left(S\right),\\{}\operatorname{Nonempty}\left(\operatorname{TargetLaunderingDecision}\left(S, oldK, newK, Z, regrade\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeRegrade/SemanticTargetLaunderingDecision.target_laundering_decision_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary regrade semantic frame, commitment and evidence equality, each of the seven protected-coordinate equalities, and strict time comparison are decidable. No finite carrier, verdict equality, inhabited commitment type, or verdict-change premise is used.

Dependent protected-coordinate extensionality first supplies equality decision for the complete coordinate record. The frozen body-level characterization then decides the laundering predicate, and the returned Boolean carries its exact correctness equivalence.

The same module transcribes the standard interpreter from the existing prospective-commitment and regrade-report carriers and proves a named specialization through that interpreter. This discharges obligation 57.2-E from definition-escape-completion-theory atom generic-residual-18a12b09c5e901f1df86ba136d7ef48402e6fbabd170dd510c85c64d00c8a9f8.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeRegrade/SemanticTargetLaunderingDecision.target_laundering_decision_nonempty`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscapeRegrade/SemanticTargetLaunderingBundleElimination](SemanticTargetLaunderingBundleElimination.md)
