# Untrusted triangle cache mirrors and all unknown-coordinate transitions

## Abstract

Untrusted triangle cache mirrors and all unknown-coordinate transitions

All 41294 original rows are retained. The data proposes 342224 transitions, one for every unknown coordinate and each of its four possible values. The cached integer lower is a literal mirror of the original row lower multiplied by the same scale; it is not an imported minimum. Full finite-domain receipt modules must check all mirror assignments, bounds and action/update equations before the cache consumer uses them.

**Definition 1.1 (Proposed literal row mirror).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMTriangleCacheData.mirror`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMTriangleCacheData.mirror` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The total binary mirror tree provides hash, lower and all per-row transition words. Missing-data fallback cannot establish correctness; every actual row is independently checked.

**Definition 1.2 (Whole original partial event from the small hash).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMTriangleCacheData.assignment`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMTriangleCacheData.assignment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original base-five decoder is applied to the mirror hash. Unknown coordinates and known outcomes retain exactly the original partial-event semantics.

**Definition 1.3 (Literal scaled lower proposal).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMTriangleCacheData.lower`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMTriangleCacheData.lower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This reads the small integer field. Its equality with the original row interpreter's exact scaled lower is a complete kernel obligation.

**Definition 1.4 (Proposed next row and actual symmetry tag).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMTriangleCacheData.transition`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMTriangleCacheData.transition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selected word supplies a new representative row and action. A later receipt verifies that action on the whole updated assignment, not merely a hash or prefix mask.

**Definition 1.5 (Check exact original raw fields once per mirror).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMTriangleCacheData.checkMirrorFields`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMTriangleCacheData.checkMirrorFields` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original raw hash and scaled lower are compared to the complete mirror row. The generic checked-raw-mirror theorem earns the entire original assignment equality from these fields.

**Definition 1.6 (Compare each mirror with the original row).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMTriangleCacheData.checkMirror`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMTriangleCacheData.checkMirror` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Boolean checks equality of the entire partial-assignment function and equality of the exact integer lower with the original row.

**Definition 1.7 (Check all actual unknown-coordinate transitions).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMTriangleCacheData.checkTransitions`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMTriangleCacheData.checkTransitions` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every unknown coordinate and all four outcomes are quantified. The entire new assignment must equal the actual partial action applied to the complete original updated representative.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMTriangleCacheData.assignment`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMTriangleCacheData.checkMirror`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMTriangleCacheData.checkMirrorFields`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMTriangleCacheData.checkTransitions`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMTriangleCacheData.lower`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMTriangleCacheData.mirror`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMTriangleCacheData.transition`
- Dependency: [D5/S3/Quantum/Entanglement/EJM/EJMLocalCacheData](EJMLocalCacheData.md)
