# No paired coherent pure designs above dimension four

## Abstract

No paired coherent pure designs above dimension four

**Definition 1.1 (The precise conditional construction).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormDesignObstruction.PureDesign`

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormDesignObstruction.PureDesign` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

A nonempty family consists of actual complex rank-one density projectors, is coherent with sum (v/n)I, and has a common real distinct-pair trace overlap. Design existence is an input to the original conditional constructions, not a theorem for all dimensions or cardinalities.

**Theorem 1.2 (A global qubit cardinality bound).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormDesignObstruction.qubit_design_cardinality`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormDesignObstruction.qubit_design_cardinality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

Every such actual qubit design has 2≤v≤4. Coherence excludes a common overlap of one. Taking traces of a vanishing linear combination, then pairing it with each projector, proves complex linear independence. The full complex qubit matrix space has dimension four. The one-member case contradicts coherence and idempotence. The received written derivation also gives the overlap (v-2)/(2(v-1)) and the positive-definite Gram form (1-mu)I+mu*11 transpose; the formal proof uses the equivalent direct linear-independence argument. No finite cardinality search is used.

**Theorem 1.3 (Coherence needs enough pure projectors).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormDesignObstruction.design_dimension_le_cardinality`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormDesignObstruction.design_dimension_le_cardinality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

In every positive local dimension n, a coherent pure design has n≤v. The proof pairs the coherent sum with any projector, retains its unit self-pairing, and uses positivity of every other actual PSD trace pairing.

**Theorem 1.4 (The exact coherent-pair obstruction).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormDesignObstruction.no_coherent_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormDesignObstruction.no_coherent_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

For every integer D≥5 there is no common-size nonempty pair of the specified regular coherent degree-one pure designs in dimensions 2 and D. The preceding global bounds give D≤v≤4. This excludes precisely that paired construction; it does not refute arbitrary designs or every interpretation of Peled et al.’s broad general-p design characterization. Attainment of the unrestricted fourth-order maximum is proved separately by CorrelationMinorNormQubitBound.coherent_pair_obstruction_with_attainment using the actual zero-noise tetrahedral state for every D>=5. No design-existence premise supplies that attainment. Source: the CC BY 4.0 return note by Haobo Ma (Chrono AI, Singapore) and Wenlin Zhang (NUS and Chrono AI, Singapore). No novelty, consent, publication or submission claim.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormDesignObstruction.PureDesign`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormDesignObstruction.design_dimension_le_cardinality`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormDesignObstruction.no_coherent_pair`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormDesignObstruction.qubit_design_cardinality`
- Dependency: [D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry](CorrelationMinorNormGeometry.md)
