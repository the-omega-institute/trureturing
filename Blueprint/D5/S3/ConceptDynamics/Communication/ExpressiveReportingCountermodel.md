# Expressive Reporting Countermodel

## Abstract

A report carrier can encode every type while incentives still select a nontruthful report.

**Theorem 1.1 (Expressive report capacity does not force truthful revelation).**

$$\begin{gathered}\exists p: \operatorname{ReportProfile}\left(\operatorname{Bool}, \operatorname{Bool}, \operatorname{Bool}\right), g: \operatorname{Bool} \to \operatorname{Bool},\\{}u: \operatorname{Bool} \to \left(\operatorname{Bool} \to \mathbb{R}\right),\\{}p.trueReport = id \land\\{}p.sentReport(true) = false \land\\{}p.sentReport \neq p.trueReport \land\\{}(\forall theta: \operatorname{Bool}, u(theta, g(false)) > u(theta, g(true))) \land\\{}\forall theta, r: \operatorname{Bool}, u(theta, g(p.sentReport(theta))) \geq u(theta, g(r)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Communication/ExpressiveReportingCountermodel.expressive_report_space_does_not_force_truthful_revelation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The type carrier and report carrier are both Bool, and the profile's truthful direct report is the identity. The report interface can therefore encode either true type without loss.

The mechanism uses the reported Boolean as its outcome. Utility is one at outcome false and zero at outcome true for both types, so both types strictly prefer the result induced by report false.

The sent strategy is constantly false and is utility-maximizing against every alternative report. In particular, true type true reports false, and the sent strategy differs from truthful reporting.

This explicit strategic countermodel separates expressive capacity from truthful revelation; the missing ingredient is an incentive condition, not another report symbol.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Communication/ExpressiveReportingCountermodel.expressive_report_space_does_not_force_truthful_revelation`
- Dependency: [D5/S3/ConceptDynamics/Communication/TruthfulnessSufficiencyIndependence](TruthfulnessSufficiencyIndependence.md)
