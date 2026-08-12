# Finite Certificate Depth

## Abstract

Every event-history certificate references only finitely many generating events.

**Theorem 1.1 (Every certificate references finitely many generating events).**

$$\forall c : \operatorname{EventHistory},\ \operatorname{Finite}(\left\{u \mid u \in c\right\}).$$

*Proof.* Machine-checked in Lean as `D5/S0/CertificateHistory/FiniteCertificateDepth.certificate_references_finitely_many_events` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A certificate is represented by the repository's EventHistory carrier. The events referenced by the certificate are exactly those occurring in that history. Their underlying set is finite, with no additional finiteness premise on the certificate.

Pinned Mathlib was searched before proving. The exact supporting result is List.finite_toSet, which states that the set of members of any list is finite. Since EventHistory is the list-based free monoid on Event, the Lean theorem is a one-line honest wrapper over that library result; it does not reprove list finiteness.

## References

- Truth anchor: `D5/S0/CertificateHistory/FiniteCertificateDepth.certificate_references_finitely_many_events`
- Dependency: [D5/S0/History/HistoryCarrier](../History/HistoryCarrier.md)
