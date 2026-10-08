# Morphism Iteration Bound Automaton

This Blueprint mirror records the machine-checked source module.

*Formalization.* `D5/S1/Words/RankOneMorphismIterationBoundAutomaton` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The module provides the finite-state and word-combinatorial suppliers used by `D5/S1/Words/RankOneMorphismIterationBound.effective_iteration_bound`. Its declarations are kernel-checked in the actual binary rank-one morphism setting; no proxy fixed word or frequency-only replacement is used.

## Declarations

- `heightMachine`
- `root`
- `root_nonempty`
- `Monochromatic`
- `monochromaticDecidable`
- `subsetMachine`
- `subset_eval`
- `subset_card`
- `RootAccepts`
- `rootAcceptsDecidable`
- `root_cutoff`
- `digitWords`
- `mem_digitWords`
- `subsetChecker`
- `subsetChecker_correct`

- Truth anchor: `D5/S1/Words/RankOneMorphismIterationBoundAutomaton`
