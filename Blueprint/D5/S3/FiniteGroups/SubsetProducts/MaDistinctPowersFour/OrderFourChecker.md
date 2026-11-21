# Sound checking of equality branches for arbitrary order-four arrays

## Abstract

Sound checking of equality branches for arbitrary order-four arrays.

**Definition 1.1 (Position).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.Position`

*Formalization.* `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.Position` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A cell is a pair of indices in Fin 4 × Fin 4, with row first and column second.

**Definition 1.2 (Partition).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.Partition`

*Formalization.* `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.Partition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An equality state is a Vector Nat 16 assigning a natural-number symbol to each cell.

**Definition 1.3 (initial).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.initial`

*Formalization.* `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.initial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The initial Partition assigns each cell its own index in the sixteen-entry vector.

**Definition 1.4 (symbol).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.symbol`

*Formalization.* `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.symbol` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Read the natural-number symbol of a Position in a Partition using the standard index equivalence from Fin 4 × Fin 4 to Fin 16.

**Definition 1.5 (value).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.value`

*Formalization.* `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.value` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Read the label of a Position in an array with rows and columns indexed by Fin 4 and labels in an arbitrary type.

**Definition 1.6 (Realizes).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.Realizes`

*Formalization.* `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.Realizes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An array realizes a Partition if any two cells with equal partition symbols have equal array labels.

**Definition 1.7 (merge).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.merge`

*Formalization.* `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.merge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Given a Partition and two positions p and q, return the partition formed by replacing every occurrence of the symbol at q with the symbol at p.

**Definition 1.8 (Closed).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.Closed`

*Formalization.* `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.Closed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every label type and every order-four array that is Latin, has no rainbow transversal and realizes the given Partition, the array has equal column symbol sets or the prescribed motif.

**Definition 1.9 (Known).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.Known`

*Formalization.* `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.Known` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a List Partition, the empty list gives True and a nonempty list requires its first partition to be Closed and the remaining list to be Known.

**Definition 1.10 (Certificate).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.Certificate`

*Formalization.* `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.Certificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The certificate tree has a same-line clash with two positions, a columns leaf, a transversal with a row-to-column map and six subcertificates, a motif with three rows, three columns and one subcertificate, or reuse at a natural-number index.

**Definition 1.11 (check).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.check`

*Formalization.* `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.check` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Given a List Partition, the current Partition and a Certificate, return a Boolean. A clash tests two distinct cells on one line for equal symbols. A columns leaf tests for a symbol match for every row of each source column in each target column. A transversal tests the map for injectivity and checks all six pairwise merges. A motif tests distinct rows and columns and the first four equalities, then checks the merge for the fifth equality. Reuse tests for the exact current partition at the indicated list index.

**Theorem 1.12 (realizes_initial).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.realizes_initial`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.realizes_initial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Singleton partition classes constrain no distinct cells to have equal labels.

**Theorem 1.13 (known_of_mem).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.known_of_mem`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.known_of_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Retrieve the closure proposition for a partition found in the checked reuse list.

**Theorem 1.14 (sound).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.sound`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A successful check closes the given equality state. Transversal branches cover all six row pairs, clashes contradict row or column injectivity, and exact partition matches allow reuse. A motif branch splits on the fifth cell equality. A columns leaf supplies a match for each row in each pair of columns.

Certificate parts 1 through 17 supply the 319 checked inputs to this proof. Each check proves Boolean acceptance for its certificate, partition and reuse list. Soundness turns each accepted input and the earlier closures it uses into a closure for arbitrary realizing arrays. In part 17, check318 accepts certificate318 at the initial partition with thirteen previously closed states. MaLatin.orderFour applies the resulting initial_closed to the input array when it has no transversal.

## References

- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.Certificate`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.Closed`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.Known`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.Partition`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.Position`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.Realizes`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.check`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.initial`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.known_of_mem`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.merge`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.realizes_initial`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.sound`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.symbol`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFourChecker.value`
- Dependency: [D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LatinCore](LatinCore.md)
