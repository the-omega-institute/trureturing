# Morphism Iteration Bound Checker

This Blueprint mirror records the machine-checked source module.

*Formalization.* `D5/S1/Words/RankOneMorphismIterationBoundChecker` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The module provides the finite-state and word-combinatorial suppliers used by `D5/S1/Words/RankOneMorphismIterationBound.effective_iteration_bound`. Its declarations are kernel-checked in the actual binary rank-one morphism setting; no proxy fixed word or frequency-only replacement is used.

## Declarations

- `sourceCharge`
- `witnessChecker`
- `finiteChecker`
- `sourceCharge_eq`
- `sourceCharge_eq_iff`
- `iterated_quotient`
- `samples_reference`
- `witnessChecker_correct`
- `finiteChecker_correct`

- Truth anchor: `D5/S1/Words/RankOneMorphismIterationBoundChecker`
