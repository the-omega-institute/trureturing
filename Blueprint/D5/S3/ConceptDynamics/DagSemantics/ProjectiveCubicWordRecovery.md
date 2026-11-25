# Projective recovery of cubic words

## Abstract

Consecutive ternary equality observers retain exactly the relative sign in each nonzero incidence run.

**Theorem 1.1 (The exact collisions of consecutive ternary observers).**

Lean statement: `D5/S3/ConceptDynamics/DagSemantics/ProjectiveCubicWordRecovery.projective_cubic_word_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagSemantics/ProjectiveCubicWordRecovery.projective_cubic_word_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two words of any finite length over the three-element field, compare all entry-equality tests at distance one or two. The tests coincide if and only if their signed path differences differ by an independent sign on each run of nonzero differences. Zero differences separate the runs. Adjacent squared differences detect support, and the squared two-step difference detects the product of two consecutive nonzero differences.

This is an exact finite-word fibre statement. It supplies the collision analysis for local equality observations of oriented cubic probe words. The formal statement does not assert a distribution over primes or compatible starting points, nor a statement about the physical faces of a random graph embedding.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DagSemantics/ProjectiveCubicWordRecovery.projective_cubic_word_recovery`
