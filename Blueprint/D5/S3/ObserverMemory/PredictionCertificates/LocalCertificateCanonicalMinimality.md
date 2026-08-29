# Canonical Local Prediction Minimality

## Abstract

Local distance checks expose the canonical predictive equivalence and unique quotient update.

**Theorem 1.1 (A local certificate determines the canonical minimal completion).**

$$\forall Y, O, C,\ \operatorname{Fintype}(Y) \land \operatorname{Fintype}(C) \land Surjective(c) \land \operatorname{FiberCheck}(c, delta) \land \operatorname{LocalDistanceChecks}(tau, q, delta)\Rightarrow 
\forall y, yPrime, c(y) = c(yPrime) \iff \operatorname{completeItinerary}(tau, q, y) = \operatorname{completeItinerary}(tau, q, yPrime) \land 
\exists! barTau, \forall y, barTau(c(y)) = c(tau(y)) \land 
\exists equiv: C \equiv \operatorname{PredictiveCompletion}(tau, q), \forall y, yPrime, equiv(c(y)) = equiv(c(yPrime)) \iff \operatorname{completeItinerary}(tau, q, y) = \operatorname{completeItinerary}(tau, q, yPrime) \land 
\operatorname{certificateDepth}(delta) = \operatorname{stabilityDepth}(tau, q) \land 
\operatorname{MinimalStateCount}(tau, q, C) \land 
\operatorname{certificateCheckWork}(n) \in \operatorname{BigO}(n^{2}).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/PredictionCertificates/LocalCertificateCanonicalMinimality.local_certificate_canonical_minimality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite types Y and C, a deterministic transition tau, readout q, surjective label c, and distance table delta, assume that equal labels are exactly the entries marked infinite and that delta satisfies the local zero-or-successor recurrence.

The public conclusion states the complete-itinerary fibre identity, the unique quotient update, and the explicit equivalence from C to the canonical predictive completion. It also retains exact certificate depth, finite-realization state-count minimality, and quadratic table-scan work.

## References

- Truth anchor: `D5/S3/ObserverMemory/PredictionCertificates/LocalCertificateCanonicalMinimality.local_certificate_canonical_minimality`
- Dependency: [D5/S3/ObserverMemory/PredictionCertificates/LocalCertificateMinimality](LocalCertificateMinimality.md)
