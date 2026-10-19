# Compact actual local-row and action data

## Abstract

Compact actual local-row and action data

The exact coefficient score and scale remain unchanged. A row mirror records a literal base-five hash, its already scaled integer lower, coordinate-slot proposals and 25-bit next-row/action proposals. None of these definitions proves the mirror or a transition is correct. The complete kernel receipts compare every original raw hash and scaled lower once, then a proved generic bridge recovers the whole assignment equality with the original 164-bit decoder. Every unknown-coordinate/value transition is still checked over its entire assignment. The literal incidence maps refer to the original sixteen triangle and sixteen singleton blocks.

**Definition 1.1 (Small literal fields and per-row transitions).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMLocalCacheData.MirrorRow`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMLocalCacheData.MirrorRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The hash and integer lower are stored as direct literals. Each unknown coordinate has all four 25-bit transition words, so no actual branch is discarded.

**Definition 1.2 (Total binary lookup of a proposed mirror).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMLocalCacheData.get`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMLocalCacheData.get` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lookup follows literal indices and returns a zero row at an empty tree. Exact mirrors must therefore be earned by finite-domain receipts, including every actual row index.

**Definition 1.3 (Check the original raw hash and scaled lower once).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMLocalCacheData.checkRawMirror`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMLocalCacheData.checkRawMirror` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The terminal or branch row must have the exact literal mirror hash and the same lower multiplied by the original scale. This checker supplies no external numerical premise.

**Theorem 1.4 (Checked raw fields preserve the complete original assignment).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMLocalCacheData.checked_raw_mirror_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMLocalCacheData.checked_raw_mirror_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary positive coordinate dimension and row count, acceptance entails equality of the whole original partial-event function and of the exact scaled lower. Both original row constructors are covered by the same symbolic proof.

**Definition 1.5 (Decode one row/action proposal).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMLocalCacheData.readTransition`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMLocalCacheData.readTransition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four-bit coordinate slot chooses one of four consecutive 25-bit words. Sixteen bits hold the proposed next row and nine bits hold the action. Modular finite-index conversions supply totality and no semantic correctness premise.

**Definition 1.6 (Compose exact triangle actions in the required order).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMLocalCacheData.triangleCompose`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMLocalCacheData.triangleCompose` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Applying the new action t after the old action s uses coordinate map pi_s composed with pi_t and outcome map o_t composed with o_s. The multiplication and inverse tables receive separate actual function-law receipts.

**Definition 1.7 (Compose exact singleton actions).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMLocalCacheData.singletonCompose`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMLocalCacheData.singletonCompose` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same action order uses the actual singleton coordinate table; agreement with the concrete partial action is proved by the companion cache laws.

**Definition 1.8 (Original triangle-block incidence).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMLocalCacheData.triangleIncidence`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMLocalCacheData.triangleIncidence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each global node and original block, the table proposes its unique local coordinate or none. The actual incidence laws check this against lhsTriangle and preserve the entire projection on unaffected blocks.

**Definition 1.9 (Original singleton-block incidence).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMLocalCacheData.singletonIncidence`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMLocalCacheData.singletonIncidence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the analogous actual nine-coordinate block table, checked against lhsSingleton before any update uses it.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMLocalCacheData.MirrorRow`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMLocalCacheData.checkRawMirror`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMLocalCacheData.checked_raw_mirror_eq`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMLocalCacheData.get`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMLocalCacheData.readTransition`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMLocalCacheData.singletonCompose`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMLocalCacheData.singletonIncidence`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMLocalCacheData.triangleCompose`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMLocalCacheData.triangleIncidence`
- Dependency: [D5/S0/Certificates/FiniteLocalRowCache](../../../../S0/Certificates/FiniteLocalRowCache.md)
- Dependency: [D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundTransport](EJMPartialBoundTransport.md)
- Dependency: [D5/S3/Quantum/Entanglement/EJMInflationScore](../EJMInflationScore.md)
