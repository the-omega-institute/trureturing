# FiniteTreeObstruction

## Abstract

Common-terminal history amplification is incompatible with a strict all-time finite Bowen bound.

**Theorem 1.1 (Common-terminal history contradiction).**

Lean statement: `D5/S1/Dynamics/Shadowing/FiniteTreeObstruction.amplification_contradiction`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/FiniteTreeObstruction.amplification_contradiction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an actual metric carrier, a finite family of pairwise disjoint subsets whose iterates stay strictly eta-close through a common terminal time and have the same nonempty terminal image gives distinct points in one strict all-time Bowen set. The proof includes time zero and uses terminal equality for every later natural time. This declaration is the reusable cardinal endpoint; it does not encode a tree, a recurrence mechanism, or a fold.

**Theorem 1.2 (Amplification excludes finite positive expansivity).**

Lean statement: `D5/S1/Dynamics/Shadowing/FiniteTreeObstruction.not_finitelyPositiveExpansive_of_amplification`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/FiniteTreeObstruction.not_finitelyPositiveExpansive_of_amplification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a concrete carrier construction supplies an amplified common-terminal family for every positive eta and every finite N, then its continuous selfmap cannot be finitely positively expansive. The finite-tree realization, finite test arcs, terminal covering component, regular-target crossing, and fold construction remain separate obligations and are intentionally not assumed by this endpoint.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/FiniteTreeObstruction.amplification_contradiction`
- Truth anchor: `D5/S1/Dynamics/Shadowing/FiniteTreeObstruction.not_finitelyPositiveExpansive_of_amplification`
- Dependency: [D5/S1/Dynamics/Shadowing/IntervalObstruction/Basic](IntervalObstruction/Basic.md)
