# Effective iteration bound for binary rank-one morphisms

## Abstract

A primitive binary rank-one morphism has an effective bounded criterion for eventual abelian periodicity.

**Theorem 1.1 (The bounded source criterion).**

Lean statement: `D5/S1/Words/RankOneMorphismIterationBound.effective_iteration_bound`

*Proof.* Machine-checked in Lean as `D5/S1/Words/RankOneMorphismIterationBound.effective_iteration_bound` (`✓ std3`). ∎

*Resolves.* `Problems/filimonova-puzynina-2026-rank-one-iteration-bound` (proved) by `D5/S1/Words/RankOneMorphismIterationBound.effective_iteration_bound`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"filimonova-puzynina-2026-rank-one-iteration-bound","declaration_gid":"D5/S1/Words/RankOneMorphismIterationBound.effective_iteration_bound","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Arina Filimonova; Svetlana Puzynina (2026). *On abelian periodicity of purely morphic words*. URL: <https://arxiv.org/abs/2605.30306v1>.

*Commentary.*

For every actual nonerasing, prolongable, primitive binary morphism of rank one and every actual all-iterate fixed word x, eventual abelian periodicity with arbitrary finite preperiod is equivalent to the original four-word cyclic block witness at some 1 ≤ K ≤ 2^((f 0).length + (f 1).length). The witness uses exact Parikh equality and nonempty common-vector blocks on both complete rotations.

**Theorem 1.2 (Executable finite checker).**

Lean statement: `D5/S1/Words/RankOneMorphismIterationBound.finiteChecker_uap`

*Proof.* Machine-checked in Lean as `D5/S1/Words/RankOneMorphismIterationBound.finiteChecker_uap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arina Filimonova; Svetlana Puzynina (2026). *On abelian periodicity of purely morphic words*. URL: <https://arxiv.org/abs/2605.30306v1>.

*Commentary.*

The executable finite-image checker returns true exactly when the actual fixed word is ultimately abelian periodic on the same complete source domain. Leading-zero digits, alternating and unary edge cases, and arbitrary preperiods remain in scope.

## References

- Truth anchor: `D5/S1/Words/RankOneMorphismIterationBound.effective_iteration_bound`
- Truth anchor: `D5/S1/Words/RankOneMorphismIterationBound.finiteChecker_uap`
- Dependency: [D5/S1/Words/RankOneMorphismIterationBoundChecker](RankOneMorphismIterationBoundChecker.md)
- Dependency: [D5/S1/Words/RankOneMorphismIterationBoundReduction](RankOneMorphismIterationBoundReduction.md)
