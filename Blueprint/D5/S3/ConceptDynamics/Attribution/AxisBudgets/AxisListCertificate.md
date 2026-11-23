# List certificates for one-coordinate inclusion factors

## Abstract

The bounded lists specify the incidence of the factor certified by their degrees and charge.

**Definition 1.1 (An inclusion factor with specified incidence).**

Lean statement: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/AxisListCertificate.MaskedFactorWithRows`

*Formalization.* `D5/S3/ConceptDynamics/Attribution/AxisBudgets/AxisListCertificate.MaskedFactorWithRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a multiplier, a marked coordinate, a budget and a proposed relation on the two copies of its free-coordinate subsets, there must be a Boolean factor and one common Boolean choice for the marked edge. The full-subset loop is absent. The unselected mode requires a multiplier of at least three. The ordinary row and column degrees are odd and bounded by the multiplier. At each full-subset endpoint the degree is even with bound the multiplier minus one in selected mode, and odd with bound the multiplier minus two in unselected mode. Only the full-subset row may depart from inclusion. The cost is four times one plus the number of true entries from ordinary odd rows to odd columns, with the one inside the factor of four. The cost lies within budget. The true entries are exactly the pairs in the proposed relation.

**Definition 1.2 (Masks identify the subsets excluding coordinate zero).**

Lean statement: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/AxisListCertificate.maskEquiv`

*Formalization.* `D5/S3/ConceptDynamics/Attribution/AxisBudgets/AxisListCertificate.maskEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For n free coordinates, map each mask below two to the n to the set of its occupied coordinates with indices shifted by one. This is a bijection onto the subsets that omit zero.

**Theorem 1.3 (Mask weight is the rank of its subset).**

Lean statement: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/AxisListCertificate.mask_rank`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/AxisBudgets/AxisListCertificate.mask_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any mask in range, the number of occupied bits equals the cardinality of its corresponding subset.

**Theorem 1.4 (The all-ones mask is the full subset).**

Lean statement: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/AxisListCertificate.mask_top`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/AxisBudgets/AxisListCertificate.mask_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mask with value two to the n minus one represents the full subset of free coordinates.

**Theorem 1.5 (Equal-sized blocks partition a finite sum).**

Lean statement: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/AxisListCertificate.sum_blocks`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/AxisBudgets/AxisListCertificate.sum_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sum a natural-valued function over the indices below the product of two natural numbers. Equivalently sum over each block of the second size and each position within it. The index equals the block number times the block size plus the position.

**Theorem 1.6 (Bounded lists certify an exact factor table).**

Lean statement: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/AxisListCertificate.list_axis_factor`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/AxisBudgets/AxisListCertificate.list_axis_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n free coordinates, take two families of row and column lists indexed by masks below two to the n and a natural budget. Choose the top index with value two to the n minus one. Both list families have no duplicates, contain only masks in range and agree on every ordered pair. The top row excludes its own index. In each family the ordinary lengths are one or three, and the top length is zero or two. Every entry in an ordinary row contains all the bits of its source mask. Four times the sum of one and the number of entries of odd weight in ordinary odd-weight rows is within budget. These lists give an inclusion factor at multiplier three and coordinate zero in dimension n plus one. The budget bound and marked degree conditions hold, and a Boolean entry is true exactly when the decoded target mask occurs in the list indexed by the decoded source mask.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/AxisListCertificate.MaskedFactorWithRows`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/AxisListCertificate.list_axis_factor`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/AxisListCertificate.maskEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/AxisListCertificate.mask_rank`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/AxisListCertificate.mask_top`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/AxisListCertificate.sum_blocks`
- Dependency: [D5/S3/Combinatorics/ErdosUlam/SublatticeDefs](../../../Combinatorics/ErdosUlam/SublatticeDefs.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/ParitySeedAxisFactor](../ParitySeedAxisFactor.md)
