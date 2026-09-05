# Structural Catalog Strictness

## Abstract

Structural strictness is certified by relation inclusion and a separating pair, and finite embeddings preserve the verdict.

**Definition 1.1 (Structural joint kernel).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog.jointKernel`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog.jointKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two states are related exactly when every primitive of every selected theorem relates them.

**Definition 1.2 (Structural escape lowering).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog.StructurallyLowersEscape`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog.StructurallyLowersEscape` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The full relation refines the leave-one-out relation and the reverse pointwise refinement fails.

**Definition 1.3 (Structural strictness certificate).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog.StructuralStrictnessCertificate`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog.StructuralStrictnessCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A certificate stores full-to-without inclusion and a pair accepted without the theorem but rejected by the full catalog.

**Theorem 1.4 (A certificate proves structural strictness).**

$$\forall certificate: \operatorname{StructuralStrictnessCertificate}(catalog, i), \operatorname{StructurallyLowersEscape}(catalog, i).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog.structurallyLowersEscape_of_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying a hypothetical reverse inclusion to the certificate pair contradicts full separation.

**Theorem 1.5 (Structural strictness yields a certificate).**

$$\operatorname{StructurallyLowersEscape}(catalog, i) \Rightarrow \operatorname{Nonempty}(\operatorname{StructuralStrictnessCertificate}(catalog, i)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog.exists_certificate_of_structurallyLowersEscape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Classical failure of reverse pointwise inclusion supplies the separating pair.

**Theorem 1.6 (Structural strictness is certificate inhabitation).**

$$\operatorname{StructurallyLowersEscape}(catalog, i) \Leftrightarrow \operatorname{Nonempty}(\operatorname{StructuralStrictnessCertificate}(catalog, i)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog.structurallyLowersEscape_iff_exists_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The strictness proposition and the inhabited certificate type determine one another.

**Theorem 1.7 (Finite triviality is failure to lower escape).**

$$\operatorname{Nondegenerate}(arena) \Rightarrow {\operatorname{TrivialInCatalog}(catalog, i) \Leftrightarrow \neg\operatorname{LowersEscape}(catalog, i)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog.trivialInCatalog_iff_not_lowersEscape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a nondegenerate finite arena, the landed positive-count criterion turns empty unique capture into the negated rate verdict.

**Theorem 1.8 (Finite selection kernels are preserved).**

$$\forall S, x, y, \operatorname{relation}(\operatorname{jointKernel}(\operatorname{toStructuralCatalog}(catalog), \operatorname{coe}(S)), x, y) \Leftrightarrow \operatorname{indistinguishable}(catalog, S, x, y).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog.toStructuralCatalog_jointKernel_relation_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite selection, the embedded structural relation is the landed indistinguishability relation.

**Definition 1.9 (Finite witness to structural certificate).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog.toStructuralCatalog_certificate_of_uniqueCapture_witness`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog.toStructuralCatalog_certificate_of_uniqueCapture_witness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite unique-capture pair constructs a structural certificate with exactly the same left and right states.

**Theorem 1.10 (Structural certificate to finite witness).**

$$\forall certificate: \operatorname{StructuralStrictnessCertificate}(\operatorname{toStructuralCatalog}(catalog), i), \operatorname{left}(certificate) \neq \operatorname{right}(certificate) \land \left({\forall j, j \neq i \Rightarrow \operatorname{agrees}(catalog, j, \operatorname{left}(certificate), \operatorname{right}(certificate))} \land \neg\operatorname{agrees}(catalog, i, \operatorname{left}(certificate), \operatorname{right}(certificate))\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog.uniqueCapture_witness_of_toStructuralCatalog_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An embedded certificate preserves its pair and yields distinctness, leave-one-out agreement, and separation by the removed theorem.

**Theorem 1.11 (Structural certificates are positive finite capture).**

$$\operatorname{Nonempty}(\operatorname{StructuralStrictnessCertificate}(\operatorname{toStructuralCatalog}(catalog), i)) \Leftrightarrow 0 < \operatorname{uniqueCaptureCount}(catalog, i).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog.toStructuralCatalog_exists_certificate_iff_uniqueCaptureCount_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The landed finite witness theorem transports the same separating pair in both directions.

**Theorem 1.12 (Finite structural verdicts are preserved).**

$$\operatorname{StructurallyLowersEscape}(\operatorname{toStructuralCatalog}(catalog), i) \Leftrightarrow \operatorname{StructurallyLowersEscape}(catalog, i).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog.toStructuralCatalog_structurallyLowersEscape_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The universal pointwise-order verdict agrees with the landed finite Set-level verdict.

**Theorem 1.13 (Finite rate verdicts are preserved).**

$$\operatorname{Nondegenerate}(arena) \Rightarrow {\operatorname{StructurallyLowersEscape}(\operatorname{toStructuralCatalog}(catalog), i) \Leftrightarrow \operatorname{LowersEscape}(catalog, i)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog.toStructuralCatalog_structurallyLowersEscape_iff_lowersEscape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a nondegenerate arena, the structural embedding agrees with the exact finite escape-rate verdict.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog.StructuralStrictnessCertificate`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog.StructurallyLowersEscape`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog.exists_certificate_of_structurallyLowersEscape`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog.jointKernel`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog.structurallyLowersEscape_iff_exists_certificate`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog.structurallyLowersEscape_of_certificate`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog.toStructuralCatalog_certificate_of_uniqueCapture_witness`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog.toStructuralCatalog_exists_certificate_iff_uniqueCaptureCount_pos`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog.toStructuralCatalog_jointKernel_relation_iff`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog.toStructuralCatalog_structurallyLowersEscape_iff`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog.toStructuralCatalog_structurallyLowersEscape_iff_lowersEscape`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog.trivialInCatalog_iff_not_lowersEscape`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralCatalog.uniqueCapture_witness_of_toStructuralCatalog_certificate`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/StructuralNovelty](../InformationEscape/StructuralNovelty.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralArena](StructuralArena.md)
