# Local cache soundness for the actual EJM score

## Abstract

Exact local cache updates preserve the full projected assignment and bound the unchanged EJM score.

The twenty inflation coordinates have four outcomes. Each global cache contains sixteen ten-coordinate triangle rows and sixteen nine-coordinate singleton rows. A row index and its entire coordinate and outcome action remain associated with the original projected partial assignment; a scalar lower alone cannot supply the update invariant.

The concrete premises exhaust all 41,294 triangle rows and 8,689 singleton rows, all unknown-coordinate updates at every outcome, the complete local bound DAGs, and the terminal contraction and tag checks. These numerical premises are proved in the same delivery and are used by the cache soundness proofs. No producer observation is a mathematical assumption.

**Theorem 1.1 (A triangle row remains associated after a fill).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.triangle_step_valid`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.triangle_step_valid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any valid triangle row and partial assignment, filling any currently unknown coordinate at any of the four outcomes preserves the complete row association and the exact updated partial assignment. The transition's full canonical coordinate and outcome action is composed with the current action.

**Theorem 1.2 (A singleton row remains associated after a fill).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.singleton_step_valid`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.singleton_step_valid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The corresponding statement covers every valid singleton row, every unknown coordinate and every outcome, with the complete action retained.

**Theorem 1.3 (A global fill preserves every actual local projection).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.step_associated`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.step_associated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every associated cache and global partial assignment, any unknown global-coordinate fill preserves association to the updated assignment in all thirty-two placements. Injective incidence laws derive each affected local update; unaffected projections stay associated.

**Theorem 1.4 (The actual initial cache represents the empty original assignment).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.initial_associated`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.initial_associated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both actual root rows have the empty assignment. Their full identity actions establish association in all thirty-two placements, giving the exact starting invariant for every subsequent unknown fill. This reuses the existing checked same-certificate initialization proof.

**Theorem 1.5 (Every compatible triangle completion satisfies its lower).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.triangle_valid_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.triangle_valid_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any valid cached triangle row and any complete local event compatible with the represented partial assignment, its stored integer lower is at most the original centered triangle score with the exact pinned coefficient function F1. Complete local acceptance and score invariance discharge the numeric premises.

**Theorem 1.6 (Every compatible singleton completion satisfies its lower).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.singleton_valid_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.singleton_valid_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The corresponding lower bound applies to the original centered singleton score with the exact pinned coefficient function F2.

**Theorem 1.7 (All thirty-two local bounds control the original score).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.associated_lower_le_score`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.associated_lower_le_score` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every globally associated cache, every represented partial assignment and every compatible complete event, the sum of its thirty-two stored lowers is at most the unchanged actual integer EJM inflation score. The proof applies the earned local inequalities to the actual injective placements and sums them.

This result validates the local cache and lower-bound part of the certificate pipeline. It supplies neither complete global search acceptance nor a positive global score margin. Nonlocality of the ideal EJM law and a concrete source-noise region still require those further proofs; this local delivery makes no such claim.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.associated_lower_le_score`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.initial_associated`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.singleton_step_valid`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.singleton_valid_lower`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.step_associated`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.triangle_step_valid`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.triangle_valid_lower`
- Dependency: [D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws](EJMCacheLaws.md)
- Dependency: [D5/S3/Quantum/Entanglement/EJM/EJMCacheState](EJMCacheState.md)
- Dependency: [D5/S3/Quantum/Entanglement/EJM/EJMLocalBoundAcceptance](EJMLocalBoundAcceptance.md)
- Dependency: [D5/S3/Quantum/Entanglement/EJM/EJMSingletonCacheReceipts](EJMSingletonCacheReceipts.md)
- Dependency: [D5/S3/Quantum/Entanglement/EJM/EJMTriangleCacheReceipts](EJMTriangleCacheReceipts.md)
