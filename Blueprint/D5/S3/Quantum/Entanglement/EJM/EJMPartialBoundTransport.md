# Local symmetry edges in the finite bound DAG

## Abstract

Faithful transport of actual partial EJM block events.

Each symmetry is a pair consisting of one of the 12 recorded local coordinate actions and one of the producer's 24 lexicographic four-outcome permutations. The action first reads the old event at the permuted coordinate and then maps its outcome. Partial events use the same action, with unknown coordinates retained as unknown.

**Theorem 1.1 (Compatibility follows the exact event action).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundTransport.compatible_act`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundTransport.compatible_act` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A full event agreeing with every known coordinate of a partial event still agrees after both receive the same coordinate and outcome action. This fact does not require a trusted canonicalization procedure.

**Theorem 1.2 (The actual ten-coordinate transport).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundTransport.triangle_compatible`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundTransport.triangle_compatible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every recorded local triangle symmetry transports compatibility between the actual ten-coordinate partial assignment and its full event.

**Theorem 1.3 (The actual nine-coordinate transport).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundTransport.singleton_compatible`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundTransport.singleton_compatible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every recorded local singleton symmetry transports compatibility between the actual nine-coordinate partial assignment and its full event.

**Theorem 1.4 (The actual centered triangle score is preserved).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundTransport.triangle_score_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundTransport.triangle_score_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact F1 centered score is unchanged by every recorded coordinate and outcome action. This uses the actual coefficient lookup and the head-contraction symmetry proved by EJMScoreSymmetry.

**Theorem 1.5 (The actual centered singleton score is preserved).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundTransport.singleton_score_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundTransport.singleton_score_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact F2 centered score is unchanged by every recorded local action. Compatibility and score invariance are the two earned premises consumed by the partial-bound DAG soundness theorem; they do not establish any numerical bound until the concrete rows and terminal scores are checked.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundTransport.compatible_act`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundTransport.singleton_compatible`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundTransport.singleton_score_invariant`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundTransport.triangle_compatible`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundTransport.triangle_score_invariant`
- Dependency: [D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData](EJMPartialBoundData.md)
- Dependency: [D5/S3/Quantum/Entanglement/EJM/EJMScoreSymmetry](EJMScoreSymmetry.md)
