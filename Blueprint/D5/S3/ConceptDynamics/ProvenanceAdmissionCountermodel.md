# Provenance-Sensitive Report Admission

## Abstract

Equal report contents can carry provenance with opposite admission status.

**Theorem 1.1 (Equal content does not determine provenance-sensitive admission).**

$$\exists r_{1}, r_{2}: \operatorname{ProvenanceReport}(Bool),\ \operatorname{content}(r_{1}) = \operatorname{content}(r_{2}) \land\\\operatorname{provenance}(r_{1}) \neq \operatorname{provenance}(r_{2}) \land\\\operatorname{admitted}(r_{1}) \land\\\neg \operatorname{admitted}(r_{2}) \land\\\neg {\operatorname{admitted}(r_{1}) \iff \operatorname{admitted}(r_{2})} \land\\\neg (\operatorname{content}(r_{1}) = \operatorname{content}(r_{2}) \Rightarrow {\operatorname{admitted}(r_{1}) \iff \operatorname{admitted}(r_{2})}).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ProvenanceAdmissionCountermodel.equal_content_does_not_determine_admission` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A provenance record contains the reported content together with checks for the data source, observation device, timestamp, reasoning procedure, intermediate proof, signature, dependency versions, and admission precondition. Validity requires content agreement and every check.

The two concrete reports both contain the Boolean value false. Their provenance records differ only at the signature check: the first is verified and admitted, while the second is unverified and rejected.

All six countermodel clauses are public, including the explicit failure of content equality to imply equal admission status. Admission is computed from the source evidence checks and is not defined from that failure.

Repository and pinned-library searches found no canonical certified-report carrier or theorem to reuse. The exact Boolean inequality theorem is applied to the differing signature fields.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ProvenanceAdmissionCountermodel.equal_content_does_not_determine_admission`
