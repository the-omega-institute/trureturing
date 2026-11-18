# Binary codes and perfect restricted bases

## Abstract

Correctable binary error supports are unique bounded subset sums in a quotient group.

Let F2 be ZMod 2. A binary word is a function from Fin n to F2. A submodule C identifies words whose difference is a codeword. The coordinate vectors therefore define elements of the additive quotient group.

**Definition 1.1 (The binary coefficient field).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/BinaryCodePerfectRestrictedBasis.F2`

*Formalization.* `D5/S3/FiniteGroups/SubsetProducts/BinaryCodePerfectRestrictedBasis.F2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

F2 is ZMod 2, the field of two elements.

**Definition 1.2 (The Hamming weight).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/BinaryCodePerfectRestrictedBasis.weight`

*Formalization.* `D5/S3/FiniteGroups/SubsetProducts/BinaryCodePerfectRestrictedBasis.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural n and v : Fin n -> F2, weight v is the cardinality of the finset of coordinates i for which v i is nonzero.

**Definition 1.3 (The indicator word of a subset).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/BinaryCodePerfectRestrictedBasis.word`

*Formalization.* `D5/S3/FiniteGroups/SubsetProducts/BinaryCodePerfectRestrictedBasis.word` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural n and S : Finset (Fin n), word S : Fin n -> F2 has value one on S and zero outside S.

**Definition 1.4 (All bounded error supports).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/BinaryCodePerfectRestrictedBasis.subsets`

*Formalization.* `D5/S3/FiniteGroups/SubsetProducts/BinaryCodePerfectRestrictedBasis.subsets` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For naturals n and s, subsets n s is the full powerset of Fin n filtered by the condition that the subset cardinality is at most s. It includes the empty subset.

**Theorem 1.5 (Counting all bounded supports).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/BinaryCodePerfectRestrictedBasis.card_subsets`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/SubsetProducts/BinaryCodePerfectRestrictedBasis.card_subsets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all naturals n and s, the cardinality of subsets n s equals the sum of Nat.choose n k over k in Finset.range (s + 1), namely k = 0 through s. The subsets are partitioned by cardinality, and each layer has the corresponding binomial count.

**Theorem 1.6 (Minimum distance and sphere equality).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/BinaryCodePerfectRestrictedBasis.basis_of_minimum_weight`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/SubsetProducts/BinaryCodePerfectRestrictedBasis.basis_of_minimum_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For naturals n and s and C : Submodule F2 (Fin n -> F2), assume 1 <= s, every nonzero v in C satisfies 2*s < weight v, and Nat.card ((Fin n -> F2) / C) equals the cardinality of subsets n s. Then there exists a finset A of that quotient with A.card = n and IsPerfectRestrictedBasis s A. The predicate is the original one: every quotient element has exactly one representing subset T of A with T.card <= s and sum T equal to that element, including the empty sum. A difference between two admissible indicator words has support inside the union of the two subsets, of size at most 2*s. The minimum-weight hypothesis forces equal quotient sums to have equal supports. Singleton supports show that the coordinate classes are distinct. Equality of the finite cardinalities gives surjectivity; pulling every subset of A back to its full coordinate preimage transfers both existence and uniqueness.

## References

- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/BinaryCodePerfectRestrictedBasis.F2`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/BinaryCodePerfectRestrictedBasis.basis_of_minimum_weight`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/BinaryCodePerfectRestrictedBasis.card_subsets`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/BinaryCodePerfectRestrictedBasis.subsets`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/BinaryCodePerfectRestrictedBasis.weight`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/BinaryCodePerfectRestrictedBasis.word`
- Dependency: [D5/S3/FiniteGroups/BajnokBersonJustPerfectRestrictedBasis](../BajnokBersonJustPerfectRestrictedBasis.md)
