# Compactness of attainable memory scores

## Abstract

Attainment of finite-memory pure-state guessing optima.

**Theorem 1.1 (The unrestricted CPTP and POVM score set is compact).**

Lean statement: `D5/S3/Quantum/PureState/PhaseMemoryCompact.successSet_isCompact`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/PhaseMemoryCompact.successSet_isCompact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For fixed finite input, memory and label sets, at most dim(input) times dim(memory) Kraus operators suffice to represent every CPTP encoder. Use an array of that size with zero padding and the completeness equation ΣₖKₖ†Kₖ = I. Its diagonal bounds all Kraus entries in the complex unit disk. The finite POVM tuples are closed with 0 ≤ Dⱼ ≤ I. The product of these compact sets maps continuously onto the full score set by the Born expression. The proof of compactness holds for arbitrary fixed vectors, including normalized signal vectors.

**Theorem 1.2 (A nonempty memory and label set admit an optimal strategy).**

Lean statement: `D5/S3/Quantum/PureState/PhaseMemoryCompact.exists_isGreatest_successSet`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/PhaseMemoryCompact.exists_isGreatest_successSet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A reset channel and a deterministic guess give an attainable score when the memory and label sets are nonempty. Compactness then supplies a greatest score realized by one CPTP encoder and one POVM.

## References

- Truth anchor: `D5/S3/Quantum/PureState/PhaseMemoryCompact.exists_isGreatest_successSet`
- Truth anchor: `D5/S3/Quantum/PureState/PhaseMemoryCompact.successSet_isCompact`
- Dependency: [D5/S3/Quantum/Entanglement/FiniteSectorPhysicalConstruction](../Entanglement/FiniteSectorPhysicalConstruction.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](PureStateHandshake.md)
