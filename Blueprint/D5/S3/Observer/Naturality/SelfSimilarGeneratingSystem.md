# Self-Similar Generating Systems

## Abstract

A generating system combines six structural components with geometric and observer-compatible self-similarity laws.

**Definition 1.1 (Geometric and generative self-similarity).**

Lean statement: `D5/S3/Observer/Naturality/SelfSimilarGeneratingSystem.System`

*Formalization.* `D5/S3/Observer/Naturality/SelfSimilarGeneratingSystem.System` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The system carries a state carrier, a family of branches, a reflection or duality, a positive region, a scale-indexed observation interface, and a completion operation. A represented branch at each scale supplies the second displayed law.

Geometric self-similarity requires the union of all branch images to cover the carrier. Generative self-similarity requires every observation map to semiconjugate each branch to its represented branch at that scale.

All components and both laws are jointly realizable on the two-point Boolean carrier. The one branch, reflection, observation, completion, and represented branch are identities, while the positive region is the whole carrier.

The source gives no involutivity, cone algebra, or completion idempotence axioms. Its closing philosophical description adds no further mathematical condition, so none of these claims is formalized.

Repository and pinned-package searches found concrete self-similar sets and generic semiconjugacy components, but no aggregate structure with these six components and both laws.

## References

- Truth anchor: `D5/S3/Observer/Naturality/SelfSimilarGeneratingSystem.System`
