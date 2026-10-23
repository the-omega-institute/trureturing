# All 192 original source actions

## Abstract

The actual source-copy actions transport ordered marginals and preserve the EJM score.

The finite maps act on the original twenty coordinates and retain every ordered coordinate in each of the sixteen triangle and sixteen singleton marginals. Lean checks the exact maps, inverse witnesses and local transports. The averaged original-support cut consumes these transports; no symmetry is imposed on an event or on a hidden-variable distribution.

**Theorem 1.1 (Transporting the entire ordered triangle marginal).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMSourceActionClosure.triangle_map_closure`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMSourceActionClosure.triangle_map_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each source action, the transformed ten-node marginal is its recorded original marginal index composed with one of the twelve actual local coordinate permutations. The averaged cut uses this equality on the full 132-row triangle support.

**Theorem 1.2 (Transporting the entire ordered singleton marginal).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMSourceActionClosure.singleton_map_closure`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMSourceActionClosure.singleton_map_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each transformed nine-node marginal factors through the recorded original singleton index and local permutation. This transports the full 168-row support in the actual-event conflict proof.

**Theorem 1.3 (The complete centered score under source actions).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMSourceActionClosure.score_sourceSymmetry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMSourceActionClosure.score_sourceSymmetry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The local coefficient invariances and the bijections of all sixteen marginal indices preserve the sum of centered blocks. Every source action is checked, with no replacement of the original score by a residual score.

**Theorem 1.4 (A common bijection of the four outcomes).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMSourceActionClosure.score_relabel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMSourceActionClosure.score_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reindexing the exact head contractions proves score invariance when both coefficient functions are invariant under the common outcome bijection.

**Theorem 1.5 (The original coefficient functions and all source actions).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMSourceActionClosure.actual_score_sourceSymmetry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMSourceActionClosure.actual_score_sourceSymmetry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual F1 and F2 coordinate invariances instantiate the source-score theorem. This supplies score preservation, while a positive global margin still requires a complete checked certificate.

**Theorem 1.6 (The original coefficient functions and common outcome relabeling).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMSourceActionClosure.actual_score_relabel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMSourceActionClosure.actual_score_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equality-pattern lookup for the original coefficient functions preserves their values under every common outcome bijection. The theorem proves exact score equality and carries no positivity claim.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMSourceActionClosure.actual_score_relabel`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMSourceActionClosure.actual_score_sourceSymmetry`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMSourceActionClosure.score_relabel`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMSourceActionClosure.score_sourceSymmetry`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMSourceActionClosure.singleton_map_closure`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMSourceActionClosure.triangle_map_closure`
- Dependency: [D5/S3/Quantum/Entanglement/EJM/EJMScoreSymmetry](EJMScoreSymmetry.md)
