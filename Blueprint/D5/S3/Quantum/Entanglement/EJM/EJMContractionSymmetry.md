# Tail contractions inherit the earned centered-score symmetries

## Abstract

Exact local EJM contraction symmetry for tail representatives.

Fixing any head event and cancelling the common leading coefficient term in the already proved centered-score symmetry yields the exact contraction symmetry. The proof retains the full head sum. A finite replay may calculate one representative contraction per tail orbit, then transport it by these earned identities; representative arithmetic and every concrete tail match remain separate obligations.

**Theorem 1.1 (Triangle-tail coordinate action).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMContractionSymmetry.triangleContraction_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMContractionSymmetry.triangleContraction_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact three-head contraction is invariant under each induced seven-tail coordinate action when F has the corresponding full local coordinate symmetry.

**Theorem 1.2 (Singleton-tail coordinate action).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMContractionSymmetry.singletonContraction_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMContractionSymmetry.singletonContraction_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four singleton-head terms are invariant under the induced eight-tail coordinate action when F has the corresponding full local coordinate symmetry.

**Theorem 1.3 (Triangle-tail outcome bijection).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMContractionSymmetry.triangleContraction_relabel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMContractionSymmetry.triangleContraction_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A common outcome bijection preserving F preserves the entire weighted triangle-head contraction.

**Theorem 1.4 (Singleton-tail outcome bijection).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMContractionSymmetry.singletonContraction_relabel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMContractionSymmetry.singletonContraction_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A common outcome bijection preserving F preserves the exact singleton-head contraction.

**Theorem 1.5 (Actual F1 tail-coordinate symmetry).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMContractionSymmetry.actual_triangleContraction_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMContractionSymmetry.actual_triangleContraction_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual coefficient lookup supplies the earned symmetry needed to reuse contracted seven-tail representatives.

**Theorem 1.6 (Actual F2 tail-coordinate symmetry).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMContractionSymmetry.actual_singletonContraction_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMContractionSymmetry.actual_singletonContraction_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual coefficient lookup supplies the earned symmetry needed to reuse contracted eight-tail representatives.

**Theorem 1.7 (Actual F1 tail-outcome symmetry).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMContractionSymmetry.actual_triangleContraction_relabel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMContractionSymmetry.actual_triangleContraction_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original F1 contraction is invariant under all common outcome bijections, allowing equality-pattern tail representatives.

**Theorem 1.8 (Actual F2 tail-outcome symmetry).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMContractionSymmetry.actual_singletonContraction_relabel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMContractionSymmetry.actual_singletonContraction_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original F2 contraction is invariant under all common outcome bijections. The singleton contraction contains four F2 terms; its factor 64 remains in the separate centered score.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMContractionSymmetry.actual_singletonContraction_coordinate`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMContractionSymmetry.actual_singletonContraction_relabel`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMContractionSymmetry.actual_triangleContraction_coordinate`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMContractionSymmetry.actual_triangleContraction_relabel`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMContractionSymmetry.singletonContraction_coordinate`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMContractionSymmetry.singletonContraction_relabel`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMContractionSymmetry.triangleContraction_coordinate`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMContractionSymmetry.triangleContraction_relabel`
- Dependency: [D5/S3/Quantum/Entanglement/EJM/EJMScoreSymmetry](EJMScoreSymmetry.md)
