# Ordered Balanced Coordinates

## Abstract

Descending genuine Hankel weights and the correspondingly permuted actual realization.

**Definition 1.1 (Descending permutation).**

Lean statement: `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.descendingPermutation`

*Formalization.* `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.descendingPermutation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Uses the library tuple sort on negative weights. Real spectral construction remains noncomputable.

**Theorem 1.2 (Descending values).**

Lean statement: `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.descendingPermutation_antitone`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.descendingPermutation_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The permuted weights are nonincreasing; equal weights are permitted.

**Definition 1.3 (Reindex actual coordinates).**

Lean statement: `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.reindexCoordinates`

*Formalization.* `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.reindexCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Permutes both inverse state maps and proves both inverse identities and Gramian congruences.

**Definition 1.4 (Ordered balancing output).**

Lean statement: `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.orderedCoordinates`

*Formalization.* `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.orderedCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sorts the actual balancing output, including its coordinate maps.

**Theorem 1.5 (Output weights are ordered).**

Lean statement: `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.ordered_weight_antitone`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.ordered_weight_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proves ordering of the weights stored in the transformed output.

**Theorem 1.6 (Largest-weight prefix).**

Lean statement: `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.retained_weight_ge_discarded`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.retained_weight_ge_discarded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every retained weight is at least every discarded weight, for the actual prefix cut.

**Theorem 1.7 (Preserved multiplicities).**

Lean statement: `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.ordered_weight_multiset`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.ordered_weight_multiset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sorting preserves the complete finite weight multiset including repetitions.

**Theorem 1.8 (Uniqueness of sorted values).**

Lean statement: `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.sorted_values_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.sorted_values_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All sorting permutations return identical values. No uniqueness of eigenvectors within repeated eigenspaces is claimed.

**Theorem 1.9 (Actual transition permutation).**

Lean statement: `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.balancedA_reindex`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.balancedA_reindex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The transformed transition is the row-and-column permutation of the previous transition.

**Theorem 1.10 (Actual input permutation).**

Lean statement: `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.balancedB_reindex`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.balancedB_reindex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The input rows use the same state permutation.

**Theorem 1.11 (Actual output permutation).**

Lean statement: `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.balancedC_reindex`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.balancedC_reindex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The output columns use the same state permutation.

## References

- Truth anchor: `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.balancedA_reindex`
- Truth anchor: `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.balancedB_reindex`
- Truth anchor: `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.balancedC_reindex`
- Truth anchor: `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.descendingPermutation`
- Truth anchor: `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.descendingPermutation_antitone`
- Truth anchor: `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.orderedCoordinates`
- Truth anchor: `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.ordered_weight_antitone`
- Truth anchor: `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.ordered_weight_multiset`
- Truth anchor: `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.reindexCoordinates`
- Truth anchor: `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.retained_weight_ge_discarded`
- Truth anchor: `D5/S3/Observer/Hankel/OrderedBalancedCoordinates.sorted_values_unique`
- Dependency: [D5/S3/Observer/Hankel/BalancedHankelSchmidt](BalancedHankelSchmidt.md)
- Dependency: [D5/S3/Observer/Hankel/BalancedRealizationTransport](BalancedRealizationTransport.md)
