# Local coordinate permutations and outcome relabelings

## Abstract

Exact symmetries of the centered original EJM local blocks.

The ten-coordinate triangle and nine-coordinate singleton blocks use their actual 12 local coordinate permutations. Reindexing the exact head-outcome sums proves the centered-block symmetries. The actual F1 and F2 coefficient invariances then supply the score-preservation facts consumed by local row bounds and cache association.

**Theorem 1.1 (Triangle-block coordinate symmetry).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMScoreSymmetry.triangleCentered_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMScoreSymmetry.triangleCentered_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full centered triangle block inherits the 12 local coordinate symmetries of its coefficient function. The head outcome sum is reindexed by the induced identity or A,B swap.

**Theorem 1.2 (Singleton-block coordinate symmetry).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMScoreSymmetry.singletonCentered_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMScoreSymmetry.singletonCentered_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The centered singleton block inherits each local coordinate symmetry. The singleton coordinate is fixed and the other eight coordinates are permuted.

**Theorem 1.3 (Triangle-block outcome symmetry).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMScoreSymmetry.triangleCentered_relabel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMScoreSymmetry.triangleCentered_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A common outcome bijection preserving the coefficient function also preserves its centered triangle block, including its weighted head contraction.

**Theorem 1.4 (Singleton-block outcome symmetry).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMScoreSymmetry.singletonCentered_relabel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMScoreSymmetry.singletonCentered_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reindexing the singleton outcome sum transports coefficient relabeling invariance to the entire centered singleton block.

**Theorem 1.5 (Actual triangle-block coordinate symmetry).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMScoreSymmetry.actual_triangleCentered_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMScoreSymmetry.actual_triangleCentered_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual F1 lookup supplies the local coordinate invariance consumed by the triangle partial-state bound replay.

**Theorem 1.6 (Actual singleton-block coordinate symmetry).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMScoreSymmetry.actual_singletonCentered_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMScoreSymmetry.actual_singletonCentered_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual F2 lookup supplies the local coordinate invariance consumed by the singleton partial-state bound replay.

**Theorem 1.7 (Actual triangle-block outcome symmetry).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMScoreSymmetry.actual_triangleCentered_relabel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMScoreSymmetry.actual_triangleCentered_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every common outcome bijection preserves the actual centered triangle block. The finite bound replay uses this fact to work with canonical equality patterns.

**Theorem 1.8 (Actual singleton-block outcome symmetry).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMScoreSymmetry.actual_singletonCentered_relabel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMScoreSymmetry.actual_singletonCentered_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every common outcome bijection preserves the actual centered singleton block, supplying the outcome-symmetry premise for its partial-state replay.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMScoreSymmetry.actual_singletonCentered_coordinate`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMScoreSymmetry.actual_singletonCentered_relabel`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMScoreSymmetry.actual_triangleCentered_coordinate`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMScoreSymmetry.actual_triangleCentered_relabel`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMScoreSymmetry.singletonCentered_coordinate`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMScoreSymmetry.singletonCentered_relabel`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMScoreSymmetry.triangleCentered_coordinate`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMScoreSymmetry.triangleCentered_relabel`
- Dependency: [D5/S3/Quantum/Entanglement/EJM/EJMCertificateData](EJMCertificateData.md)
- Dependency: [D5/S3/Quantum/Entanglement/EJMInflationScore](../EJMInflationScore.md)
