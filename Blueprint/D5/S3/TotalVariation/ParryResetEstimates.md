# Three-step common mass

## Abstract

Three-step common mass.

**Theorem 1.1 (Three-step common mass).**

Lean statement: `D5/S3/TotalVariation/ParryResetEstimates.parry_three_step_minorization`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParryResetEstimates.parry_three_step_minorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k >= 2, every state s in State k, and every sign a in Bool, put p = parryParameter k and let z be the zero suffix in Fin k. Then the three-step kernel satisfies (kernel k p)^3(s,(a,z)) >= 1/8. The paths 000 and 010 reach respectively the complementary and unchanged zero-suffix signs; each path product is p^3 divided by the starting suffix weight, and each is at least 1/8. Consequently the two zero-suffix states carry at least common mass 1/4 in every three-step row.

## References

- Truth anchor: `D5/S3/TotalVariation/ParryResetEstimates.parry_three_step_minorization`
- Dependency: [D5/S3/TotalVariation/ParryResetLaw](ParryResetLaw.md)
