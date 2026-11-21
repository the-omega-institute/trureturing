# Sound checking of equality branches for arbitrary order-four arrays

## Abstract

Sound checking of equality branches for arbitrary order-four arrays.

**Theorem 1.1 (realizes_initial).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.realizes_initial`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.realizes_initial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Singleton partition classes constrain no distinct cells to have equal labels.

**Theorem 1.2 (known_of_mem).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.known_of_mem`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.known_of_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Retrieve the closure proposition for a partition found in the checked reuse list.

**Theorem 1.3 (sound).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.sound`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A successful check closes the given equality state. Transversal branches cover all six row pairs, clashes contradict row or column injectivity, and exact partition matches allow reuse. A motif branch splits on the fifth cell equality. A columns leaf supplies a match for each row in each pair of columns.

## References

- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.known_of_mem`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.realizes_initial`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.sound`
- Dependency: [D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LatinCore](LatinCore.md)
