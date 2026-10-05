# Effective iteration bound for binary rank-one morphisms

## Abstract

For a nonerasing prolongable primitive binary morphism of rank one, eventual
abelian periodicity of the actual fixed word is equivalent to an original
cyclic block witness at an iteration bounded by the computable quantity
`2^((f 0).length + (f 1).length)`.

**Theorem 1.1 (The bounded source criterion).**

*Formalization.* `D5/S1/Words/RankOneMorphismIterationBound.effective_iteration_bound` (`✓ std3`).

*Citation.* Arina Filimonova and Svetlana Puzynina (2026). *On abelian periodicity of purely morphic words*. URL: <https://arxiv.org/abs/2605.30306v1>.

*Commentary.*

The morphism has the actual binary alphabet `Fin 2`, is nonerasing,
prolongable, primitive, and has rank-one incidence columns.  The fixed word
`x` is required to satisfy the actual all-iterate fixed-word semantics.  The
property `UltimatelyAbelianPeriodic x` permits an arbitrary finite preperiod.
The witness is the source's four-word split of the two actual iterates: the
prefixes have equal exact Parikh vectors and both complete cyclic rotations
split into nonempty blocks with one common exact Parikh vector.  The theorem
places its iteration at `1 ≤ K ≤ 2^((f 0).length + (f 1).length)`.

**Theorem 1.2 (Executable finite checker).**

*Formalization.* `D5/S1/Words/RankOneMorphismIterationBound.finiteChecker_uap` (`✓ std3`).

*Commentary.*

`finiteChecker f` enumerates the finite source-image checker.  On the same
complete hypotheses and actual fixed-word semantics it returns `true` exactly
when the fixed word is ultimately abelian periodic.  The checker includes
leading-zero digits, alternating and unary edge cases, and arbitrary
preperiods.

*Proof.* Machine-checked in Lean as the declarations above (`✓ std3`). ∎

*Resolves.* `Problems/filimonova-puzynina-2026-rank-one-iteration-bound` (proved)
by `D5/S1/Words/RankOneMorphismIterationBound.effective_iteration_bound`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"filimonova-puzynina-2026-rank-one-iteration-bound","declaration_gid":"D5/S1/Words/RankOneMorphismIterationBound.effective_iteration_bound","resolution_kind":"proved"} -->

## References

- Truth anchor: `D5/S1/Words/RankOneMorphismIterationBound.effective_iteration_bound`
- Truth anchor: `D5/S1/Words/RankOneMorphismIterationBound.finiteChecker_uap`
- Dependency: [Library/Words/filimonova-puzynina2026abelianperiodicity](../../../Library/Words/filimonova-puzynina2026abelianperiodicity.md)
