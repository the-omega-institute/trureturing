# Historical Equivalence of Rich Histories

## Abstract

Historical isomorphism preserves the complete finite archive data and its signed readout.

**Definition 1.1 (Historical isomorphism extends an archive embedding).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/HistoricalEquivalence.HistoricalIsoData`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/HistoricalEquivalence.HistoricalIsoData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An isomorphism is a surjective archive embedding, hence an event bijection, preserving and reflecting causal order and all four absolute attributes. It also maps both current and selected regions exactly, for every dimension d.

**Theorem 1.2 (Historical isomorphism is reflexive).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/HistoricalEquivalence.historical_iso_refl`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/HistoricalEquivalence.historical_iso_refl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity archive embedding preserves both distinguished regions.

**Theorem 1.3 (Historical isomorphism is symmetric).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/HistoricalEquivalence.historical_iso_symm`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/HistoricalEquivalence.historical_iso_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Inverting the event bijection reverses the isomorphism.

**Theorem 1.4 (Historical isomorphism is transitive).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/HistoricalEquivalence.historical_iso_trans`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/HistoricalEquivalence.historical_iso_trans` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Composition of archive embeddings preserves both region images.

**Theorem 1.5 (Encoded equality gives historical isomorphism).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/HistoricalEquivalence.encoded_equality_implies_historical`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/HistoricalEquivalence.encoded_equality_implies_historical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rich-code round trip is injective, so equal codes identify the same dependent rich object. Its identity archive embedding supplies the required isomorphism.

**Theorem 1.6 (Historical isomorphism preserves the signed readout).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/HistoricalEquivalence.historical_iso_readout_eq`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/HistoricalEquivalence.historical_iso_readout_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The selected-image equality and finite-sum reindexing transport every contribution. Sign preservation, as part of the full attribute equality, makes the summands equal before reindexing.

The parallel-versus-temporal nonisomorphism is intentionally left to the B2 worked-history specialization, which supplies those two causal relations.

**Theorem 1.7 (A genuine HF renaming refutes the code converse).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/HistoricalEquivalence.encoded_equality_converse_refuted`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/HistoricalEquivalence.encoded_equality_converse_refuted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Singleton archives with different HF names have the same attributes, current image and empty selection, so renaming their sole event is a historical isomorphism. The witness works for every d with position Fin d to Int constantly zero. The closed converse claim quantifies over Rich 3, and its negation uses the dimension-three witness with HF names natCode 0 and natCode 1. Their literal rich codes differ. The separate numerical-converse example remains downstream.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/HistoricalEquivalence.HistoricalIsoData`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/HistoricalEquivalence.encoded_equality_converse_refuted`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/HistoricalEquivalence.encoded_equality_implies_historical`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/HistoricalEquivalence.historical_iso_readout_eq`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/HistoricalEquivalence.historical_iso_refl`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/HistoricalEquivalence.historical_iso_symm`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/HistoricalEquivalence.historical_iso_trans`
- Dependency: [D5/S0/History/Spacetime/ArchiveCarrier](../../../S0/History/Spacetime/ArchiveCarrier.md)
- Dependency: [D5/S0/History/Spacetime/ArchiveEncoding](../../../S0/History/Spacetime/ArchiveEncoding.md)
- Dependency: [D5/S3/ConceptDynamics/Spacetime/ComplementCharge](ComplementCharge.md)
