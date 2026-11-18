# Every positive finite neighborhood-shadowing level

## Abstract

Every positive finite neighborhood-shadowing level

Jonathan Meddaugh and Elyssa Stephens, Shadowing with small diameter sets of bounded cardinality, arXiv:2509.04312v1, Questions 5.1 and 5.2 ask which N admit neighborhood (N+1)-shadowing without neighborhood N-shadowing, for dynamical systems and for subshifts. The explicit X_(N+2) supplies every positive finite level.

**Theorem 1.1 (Invertibility of the two-sided shift).**

Lean statement: `D5/S1/Dynamics/Shadowing/LacunaryShadowingHierarchy.lacunary_shift_bijective`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/LacunaryShadowingHierarchy.lacunary_shift_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Translation by minus one is a legal inverse of translation by one.

**Theorem 1.2 (The full finite hierarchy).**

Lean statement: `D5/S1/Dynamics/Shadowing/LacunaryShadowingHierarchy.lacunary_shadowing_hierarchy`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/LacunaryShadowingHierarchy.lacunary_shadowing_hierarchy` (`✓ std3`). ∎

*Resolves.* `Problems/meddaugh-stephens-2025-neighborhood-shadowing-hierarchy` (proved) by `D5/S1/Dynamics/Shadowing/LacunaryShadowingHierarchy.lacunary_shadowing_hierarchy`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"meddaugh-stephens-2025-neighborhood-shadowing-hierarchy","declaration_gid":"D5/S1/Dynamics/Shadowing/LacunaryShadowingHierarchy.lacunary_shadowing_hierarchy","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

For every natural N>=1, X_(N+2) is nonempty and compact, its shift is continuous and bijective, and it has neighborhood (N+1)-shadowing while neighborhood N-shadowing fails. NeighborhoodFiniteShadowing means: for each positive accuracy, one positive tolerance works for every infinite natural-time pseudo-orbit; one fixed nonempty finite set A has cardinality at most the specified bound and initial diameter below the accuracy, and the distance to its shifted image is below the accuracy at every time. The member providing the approximation may vary with time; the set does not. Taking N=2 gives the previously highlighted neighborhood three but not two case. No all-time image-diameter bound or coherent single tracer is asserted.

The lacunary progression construction and phase-cover argument are attributed to the supplied Pro proposal; Codex implemented the complete Lean proof. The inspected primary v1 poses both hierarchy questions. A bounded search found no exact prior answer, but the full text of Ellie Stephens, Local Variations of Shadowing, announced by Baylor on November 6, 2026, was unavailable. The announcement concerns neighborhood shadowing but does not state a hierarchy theorem. No exhaustive priority claim follows.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/LacunaryShadowingHierarchy.lacunary_shadowing_hierarchy`
- Truth anchor: `D5/S1/Dynamics/Shadowing/LacunaryShadowingHierarchy.lacunary_shift_bijective`
- Dependency: [D5/S1/Dynamics/Shadowing/LacunaryShadowingLower](LacunaryShadowingLower.md)
- Dependency: [D5/S1/Dynamics/Shadowing/LacunaryShadowingUpper](LacunaryShadowingUpper.md)
