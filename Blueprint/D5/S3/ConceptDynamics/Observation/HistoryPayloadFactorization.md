# History Payload Factorization

## Abstract

A summary recovers a payload exactly when the payload is constant on its fibers. Global admission and complete local completion sets are two such payloads.

**Theorem 1.1 (Unique recovery on the realized image).**

$$\operatorname{ker}\left(beta\right) \subseteq \operatorname{ker}\left(P\right) \iff \exists! phi: \operatorname{range}\left(beta\right) \to Z, P = phi \circ \operatorname{rangeFactorization}\left(beta\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.ker_beta_subset_ker_payload_iff_unique_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source, summary, and payload carriers have independent universes and may be empty. The factor is defined only on realized summary values. Existence and uniqueness follow by applying the split-surjection factorization theorem to the canonical range map and its section.

**Theorem 1.2 (Admission on complete raw global records).**

$$(\exists! phi: \operatorname{range}\left(beta\right) \to Bool, \operatorname{admissionIndicator}\left(J, K\right) = phi \circ \operatorname{rangeFactorization}\left(beta\right)) \iff \forall x, y: J, \operatorname{beta}\left(x\right) = \operatorname{beta}\left(y\right) \to (x \in K \iff y \in K)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.global_admission_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The domain is the subtype J, the raw global join. Its Boolean payload is the indicator of K restricted to J. The actual worlds are J intersect K.

**Theorem 1.3 (Actual worlds are a union of whole restricted fibers).**

Lean statement: `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.global_admission_iff_union_fibers`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.global_admission_iff_union_fibers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem identifies J intersect K with the image in the ambient record carrier of all complete J-records sharing a summary with an admitted J-record. This equality is equivalent to unique admission factorization.

**Theorem 1.4 (The recovered admission test remains a constraint).**

Lean statement: `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.admission_factor_test`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.admission_factor_test` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each complete raw record, the recovered Boolean test is true exactly when the record belongs to J intersect K. Factorization does not assert that the test is constantly true or authorize removing it.

**Theorem 1.5 (Canonical empty assignment).**

Lean statement: `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.assignment_eq_empty`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.assignment_eq_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The QI-JOIN empty component is identified with the canonical empty assignment; the dependent Value family and empty carrier remain intact.

**Theorem 1.6 (Completion payloads use complete compatible records).**

Lean statement: `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.mem_completion_payload_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.mem_completion_payload_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An assignment supplies a value for every variable in its scope and requires no value outside that scope. The raw join consists of assignments whose restriction to each node lies in that node's local relation. The complement join also enforces consistency of variables shared between its components.

The completion payload contains precisely those complete complement records matching the entire overlap assignment and whose union with the component record belongs to K. Membership is equivalent to one admitted raw global record having both specified restrictions. The restriction maps and compatible union are explicit.

**Theorem 1.7 (Recovery of the entire local completion set).**

Lean statement: `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.local_completion_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.local_completion_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The payload codomain is the power set of the complete complement join. It factors uniquely through the realized component summary exactly when equal summaries give equal completion sets.

**Theorem 1.8 (Global-record pointwise completion tests).**

Lean statement: `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.local_completion_global_tests`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.local_completion_global_tests` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each summary fiber and complete complement record, completion membership is characterized by existence of an admitted complete raw global record with both exact restrictions. This is the preregistered live consumer of mem_completion_payload_iff; its path uses the pinned dependent-function sheaf gluing owner. The factorization and local-tests companions do not consume this bridge.

**Theorem 1.9 (The equivalent pointwise completion tests).**

Lean statement: `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.local_completion_tests`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.local_completion_tests` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set equality is equivalent to agreement of the membership test for every complete complement record. Each test includes both full boundary compatibility and membership of the union in K.

BoundaryOutputRetention names the additional requirement for later gluing: equal summaries preserve the entire boundary and every specified raw result on compatible complete complements. Results are read on the raw global join. Payload factorization alone does not establish that requirement or gluing congruence.

Source identifiers, dependency sets, and other requested payloads use the same arbitrary-target kernel criterion. Preserving a result image by existential witnesses is a separate contract; it does not recover a discarded payload.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.admission_factor_test`
- Truth anchor: `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.assignment_eq_empty`
- Truth anchor: `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.global_admission_factorization`
- Truth anchor: `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.global_admission_iff_union_fibers`
- Truth anchor: `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.ker_beta_subset_ker_payload_iff_unique_factorization`
- Truth anchor: `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.local_completion_factorization`
- Truth anchor: `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.local_completion_global_tests`
- Truth anchor: `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.local_completion_tests`
- Truth anchor: `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.mem_completion_payload_iff`
- Dependency: [D5/S0/Rewriting/Quotients/SplitSurjectionFactorization](../../../S0/Rewriting/Quotients/SplitSurjectionFactorization.md)
