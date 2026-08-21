# Strict Separation Impossibility

## Abstract

Common outcome utilities and homogeneous report costs forbid opposite strict preferences.

**Theorem 1.1 (Common utilities forbid opposite strict report preferences).**

$$\forall Theta, R, O: \operatorname{Type}, theta, theta_{prime}: Theta, r_{theta}, r_{theta_{prime}}: R, M: R \to O, u: Theta \to O \to Real, c: R \to Real,\ \forall o: O, u(theta, o) = u(theta_{prime}, o) \Rightarrow \neg ((u(theta, M(r_{theta})) - c(r_{theta}) > u(theta, M(r_{theta_{prime}})) - c(r_{theta_{prime}})) \land (u(theta_{prime}, M(r_{theta_{prime}})) - c(r_{theta_{prime}}) > u(theta_{prime}, M(r_{theta})) - c(r_{theta}))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/StrictSeparationImpossibility.strict_separation_impossible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A mechanism is represented by its result map from reports to outcomes. Both types evaluate every outcome with the same utility, and the report-cost function is independent of type.

The public conclusion rules out the conjunction in which the first type strictly prefers its report and the second type strictly prefers the other report. Transferring the first inequality across the common utility equality contradicts the second.

Repository and pinned-library searches found no exact mechanism theorem. The proof applies equality rewriting and the asymmetry of strict order.

## References

- Truth anchor: `D5/S3/ConceptDynamics/StrictSeparationImpossibility.strict_separation_impossible`
