# Local Prediction Certificate Minimality

## Abstract

Local pair-distance checks certify the canonical minimal predictive quotient.

**Theorem 1.1 (A locally checked distance table certifies global minimality).**

$$\forall tau, q, c, delta,\ \operatorname{CertificateChecks}(tau, q, c, delta) \Rightarrow 
(\operatorname{Fibers}(c) = \operatorname{FutureClasses}(tau, q) \land 
\exists barTau, \forall y,\ barTau(c(y)) = c(tau(y)) \land 
\operatorname{Nonempty}(\operatorname{Equiv}(C, \operatorname{PredictiveCompletion}(tau, q))) \land 
\operatorname{certificateDepth}(delta) = \operatorname{stabilityDepth}(tau, q) \land 
\operatorname{MinimalStateCount}(tau, q, C) \land 
\operatorname{certificateCheckWork}(n) \in \operatorname{BigO}(n^{2})).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/PredictionCertificates/LocalCertificateMinimality.local_certificate_global_minimality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Y be a finite deterministic state space with transition tau and readout q. A candidate label map is surjective, its equal-label pairs are exactly the entries marked infinite by delta, and delta passes the local zero-or-successor recurrence at every state pair.

The recurrence is first proved to determine the unique shortest distinguishing-time table. Consequently, infinite entries are exactly equal complete itineraries, the label fibers are the canonical future-equivalence classes, and the transition on labels is well-defined.

Mathlib's quotientKerEquivOfSurjective identifies the labelled carrier with the complete-itinerary quotient. The existing repository theorem controlled_behavior_universal_property is applied at a singleton input type to show that this carrier has no more states than any finite surjective deterministic realization preserving the transition and readout.

The maximum finite certificate entry equals the canonical stability depth, with zero used when every entry is infinite. A verifier scans one entry for each ordered state pair, so its declared work function is the square of the state count and is therefore quadratic.

## References

- Truth anchor: `D5/S3/ObserverMemory/PredictionCertificates/LocalCertificateMinimality.local_certificate_global_minimality`
- Dependency: [D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality](../Prediction/ControlledBehaviorUniversality.md)
- Dependency: [D5/S3/ObserverMemory/Prediction/ItineraryCompletion](../Prediction/ItineraryCompletion.md)
