# Branching futures and finite positive expansivity

## Abstract

Branching futures and finite positive expansivity

**Theorem 1.1 (Counting pasts by their last nondefault choice).**

Lean statement: `D5/S1/Dynamics/Symbolic/RightTailBranching.finite_extensions_of_not_periodic`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/RightTailBranching.finite_extensions_of_not_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a two-sided subshift, let B be the finite set of futures with at least two possible immediate predecessor letters. A nonperiodic right tail has at most 1 + |B|(|A| - 1) two-sided extensions, where A is the alphabet. Distinct depths of the same extension cannot yield the same future, since shifting both futures to the prescribed tail would make that tail periodic. Choose a default predecessor at every realized future. Each past follows those defaults beyond its last nondefault choice. That choice and its future determine the entire past, giving the cardinal bound.

**Theorem 1.2 (The periodic-future obstruction).**

Lean statement: `D5/S1/Dynamics/Symbolic/RightTailBranching.uniform_finite_extensions_iff`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/RightTailBranching.uniform_finite_extensions_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a periodic future has a nonperiodic extension, shifting by multiples of the future's period gives infinitely many extensions. Periodic extensions of one future agree everywhere by translating both by a common period. Thus the same explicit bound holds for all futures exactly when every periodic future has only periodic extensions.

**Theorem 1.3 (Bowen cardinality and the number of pasts).**

Lean statement: `D5/S1/Dynamics/Symbolic/RightTailBranching.forwardBowenBound_iff_bounded_extensions`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/RightTailBranching.forwardBowenBound_iff_bounded_extensions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Lemma 4.7 of Gangloff, Guillon and Oprocha identifies positive finite expansivity with a uniform bound on predecessor fibers. For any compatible metric, closeness at every nonnegative time forces equality of every nonnegative coordinate at a sufficiently small scale. Conversely, shifting a future fiber forward by the radius of a sufficiently large window embeds it in a single strict forward Bowen ball.

**Theorem 1.4 (Finite positive expansivity with finitely many branching futures).**

Lean statement: `D5/S1/Dynamics/Symbolic/RightTailBranching.finitelyPositiveExpansive_iff_periodic_extensions`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/RightTailBranching.finitelyPositiveExpansive_iff_periodic_extensions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With finitely many branching futures, finite positive expansivity is equivalent to every periodic future having only periodic extensions. The counting argument applies to the full two-sided subshift and every compatible metric.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/RightTailBranching.finite_extensions_of_not_periodic`
- Truth anchor: `D5/S1/Dynamics/Symbolic/RightTailBranching.finitelyPositiveExpansive_iff_periodic_extensions`
- Truth anchor: `D5/S1/Dynamics/Symbolic/RightTailBranching.forwardBowenBound_iff_bounded_extensions`
- Truth anchor: `D5/S1/Dynamics/Symbolic/RightTailBranching.uniform_finite_extensions_iff`
- Dependency: [D5/S1/Dynamics/Shadowing/IntervalObstruction/Basic](../Shadowing/IntervalObstruction/Basic.md)
- Dependency: [D5/S1/Dynamics/Shadowing/LanguageCharacterization](../Shadowing/LanguageCharacterization.md)
