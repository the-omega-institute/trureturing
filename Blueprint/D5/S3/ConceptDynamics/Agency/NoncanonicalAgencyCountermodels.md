# Noncanonical and Deterministic Agency Countermodels

## Abstract

Fair random choice and reason-sensitive deterministic choice separate canonicity and determinism from internal authorship.

**Theorem 1.1 (Two Boolean countermodels separate canonicity from authorship).**

$$\left(\exists tieLaw \in Bool \to \operatorname{PMF}\left(Bool\right),\; \left(\forall reason \in Bool, action \in Bool,\; tieLaw\left(reason\right)\left(action\right) = \frac{1}{2}\right) \land \left(\left(\forall leftReason \in Bool, rightReason \in Bool,\; tieLaw\left(leftReason\right) = tieLaw\left(rightReason\right)\right) \land \left(\neg \left(\exists selector \in Bool \to Bool,\; \forall reason \in Bool,\; \left(\forall action \in Bool,\; tieLaw\left(reason\right)\left(\operatorname{not}\left(action\right)\right) = tieLaw\left(reason\right)\left(action\right)\right) \Rightarrow \operatorname{not}\left(selector\left(reason\right)\right) = selector\left(reason\right)\right)\right)\right)\right) \land \left(\exists process \in Bool \to \left(Bool \to \operatorname{Set}\left(Bool\right)\right),\; \left(\forall external \in Bool,\; \operatorname{FunctionalFuture}\left(process\left(external\right)\right)\right) \land \left(\exists external \in Bool, reason1 \in Bool, reason2 \in Bool, action1 \in Bool, action2 \in Bool,\; reason1 \ne reason2 \land \left(process\left(external\right)\left(reason1\right) = \left\{action1\right\} \land \left(process\left(external\right)\left(reason2\right) = \left\{action2\right\} \land action1 \ne action2\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Agency/NoncanonicalAgencyCountermodels.noncanonical_and_deterministic_agency_countermodels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first model assigns the uniform Boolean law at every internal reason. Each action has mass one half and changing the reason does not change the law, so this randomized tie-break contains no internal authorship.

Candidate exchange preserves the same fair law. A canonical deterministic selector would therefore have to be fixed by Boolean complement, which no Boolean action is.

The second model is one shared Boolean process. At every external setting it is a functional future, while at one fixed setting false and true internal reasons lead to the distinct singleton actions false and true.

All stochastic, deterministic, and reason-sensitivity clauses are public and use the same objects within each model. The canonical FunctionalFuture predicate and pinned probability-mass-function primitives are reused directly.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Agency/NoncanonicalAgencyCountermodels.noncanonical_and_deterministic_agency_countermodels`
- Dependency: [D5/S3/ConceptDynamics/Agency/SelfFormationFreeWillBoundary](SelfFormationFreeWillBoundary.md)
