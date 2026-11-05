# Minimum Installed Readout

## Abstract

The attained minimum effective installed alphabet for arbitrary finite configuration families.

**Theorem 1.1 (Sink labels plus an actual minimum enabled-event hitting set).**

$$\forall E: \operatorname{Type}, [\operatorname{Fintype}\left(E\right)] [\operatorname{DecidableEq}\left(E\right)], F: \operatorname{Finset}\left(\operatorname{Finset}\left(E\right)\right), \operatorname{Nonempty}\left(F\right) \implies\\{}{{\exists H: \operatorname{Finset}\left(E\right), \operatorname{Hits}\left(F, H\right) \land \lvert H\rvert =\operatorname{hittingNumber}\left(F\right)} \land {\forall K: \operatorname{Finset}\left(E\right), \operatorname{Hits}\left(F, K\right) \implies \operatorname{hittingNumber}\left(F\right) \leq \lvert K\rvert }} \land {\forall Q: \operatorname{Type}, r: \operatorname{State}\left(F\right) \to Q, {\exists p: \operatorname{History}\left(E, Q\right) \to \operatorname{Decision}\left(F\right), \operatorname{Acquires}\left(r, p\right)} \implies \lvert \operatorname{sinks}\left(F\right)\rvert +\operatorname{hittingNumber}\left(F\right) \leq \operatorname{effectiveSize}\left(r\right)} \land {\exists r: \operatorname{State}\left(F\right) \to \operatorname{Sum}\left(\operatorname{State}\left(F\right), E\right), \operatorname{FiniteAcquirable}\left(r\right) \land \operatorname{effectiveSize}\left(r\right)=\lvert \operatorname{sinks}\left(F\right)\rvert +\operatorname{hittingNumber}\left(F\right)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Agency/MinimumInstalledReadout.installed_readout_optimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the finite insertion model, sinks F contains the operational sinks. Hits F H means that H contains an enabled event for every nonsink. The number tau is the least cardinality of a hitting set, defined by minimization over natural numbers. The full event set hits every nonempty enabled set, so this minimum exists. The theorem includes both a minimizing set and its universal minimality property.

effectiveSize r is the cardinality of the actual image of r on F, regardless of its symbol carrier. For an arbitrary successful history policy, each sink has a private symbol. Every other effective fiber has a common enabled event, including singleton nonsinks. Choosing one event per such fiber produces a hitting set whose size is no larger than the number of those fibers. This proves the lower bound for unrestricted history policies.

For attainment, choose a minimum hitting set H and, at each nonsink C, choose one event in H enabled at C. Give a sink its own left label C and a nonsink the right label of its selected event. The two label families are disjoint. Each right-label fiber has a common enabled event, and every sink label is private. The finite acquisition criterion constructs the actual finite-table policy and proves the addition bound. Its effective image has at most card T plus card H symbols; the lower bound forces equality.

The family may be disconnected and need not contain the empty configuration or any root. The empty event type, a singleton family, and an all-sink family are included. If every state is a sink, the empty hitting set has minimum size zero and the readout directly identifies each state. Only the number of effective installed symbols is minimized. Same-run recovery of an earlier state, source transport and physical implementation require their own interfaces.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Agency/MinimumInstalledReadout.installed_readout_optimum`
- Dependency: [D5/S3/ConceptDynamics/Agency/FiniteConfigurationAcquisition](FiniteConfigurationAcquisition.md)
