# An exact conflict in the original EJM inflation supports

## Abstract

Three original support factors cannot coexist in any full event.

The triangle support contains 132 actual local assignments, obtained from original rows 104, 259, 332 and 464. The singleton support contains 168 assignments from original rows 220 and 252. Each support retains its complete orbit under all twelve local-coordinate actions and all twenty-four simultaneous outcome permutations. The literal original marginal maps are used in their original order. No coordinate-zero normalization is imposed.

**Definition 1.1 (A common event for original factors 24, 2 and 3).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalSupportConflict.claim`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMOriginalSupportConflict.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The claim asserts the existence of one full twenty-coordinate, four-outcome event in singleton marginal 8 and triangle marginals 2 and 3. Singleton 8 is factor 24 in the original sixteen-plus-sixteen numbering. Compatibility quantifies over every coordinate of each actual local row.

**Theorem 1.2 (The actual empty natural join refutes the common event).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalSupportConflict.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMOriginalSupportConflict.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The kernel evaluates the exact finite join of these three complete supports. General join soundness preserves any putative full event through both joins, contradicting the empty final relation. This excludes simultaneous inside membership; it does not establish the original uniform positive EJM score margin, nonlocality or a strict noise region. Those require the subsequent exact averaging and dual-certificate proof.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalSupportConflict.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalSupportConflict.result`
- Dependency: [D5/S0/Certificates/FiniteNaturalJoin](../../../../S0/Certificates/FiniteNaturalJoin.md)
- Dependency: [D5/S3/Quantum/Entanglement/EJMInflationScore](../EJMInflationScore.md)
