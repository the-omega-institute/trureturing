# Thirty-two exact local cache proposals

## Abstract

Thirty-two exact local cache proposals

The executable cache stores sixteen triangle and sixteen singleton states. Each state carries a representative index, earned-action proposal and small mirror row. Retaining the row removes packed lower decoding at leaves, while its equality with the indexed mirror is a separate proved invariant. These definitions assert no score bound or replay acceptance.

**Definition 1.1 (Transport and update an affected triangle state).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCacheState.triangleStep`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMCacheState.triangleStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The old action sends the actual fill into representative coordinates and values. The per-row word supplies the new row and action, and the new action is composed with the old one in the checked order.

**Definition 1.2 (Transport and update an affected singleton state).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCacheState.singletonStep`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMCacheState.singletonStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The analogous actual singleton action and transition decode retain a new literal row for later arithmetic.

**Definition 1.3 (Update exactly the affected original blocks).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCacheState.step`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMCacheState.step` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal incidence selects each affected block's local coordinate. Blocks absent from the incidence retain their entire previous state and row literal.

**Definition 1.4 (Sum all thirty-two literal lower fields).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCacheState.lower`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMCacheState.lower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original sixteen triangle and sixteen singleton bounds are all included with unchanged signs and weights. No sorted multiset or branch shape substitutes for actual cache association.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCacheState.lower`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCacheState.singletonStep`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCacheState.step`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCacheState.triangleStep`
- Dependency: [D5/S3/Quantum/Entanglement/EJM/EJMSingletonCacheData](EJMSingletonCacheData.md)
- Dependency: [D5/S3/Quantum/Entanglement/EJM/EJMTriangleCacheData](EJMTriangleCacheData.md)
