# Finite root indices and unique normalized reconstruction

## Abstract

Distinct root sequences reconstruct normalized singleton boards with a finite multinomial bound.

In the displayed formulas, Member(S) is the finite subtype of members of the Finset S, boardMap(m,z) is the map a to board(m,a) on indices(m,z), and sum(d) sums the entries over its finite index type. A subtype index a is read as its underlying root tuple when used by decode or compared with paddedRoots.

**Definition 1.1 (Integer heights).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookRootIndex.heights`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookRootIndex.heights` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At position i, heights(m,a,i)=mi-a(i) in the integers.

**Definition 1.2 (The exact admissibility filter).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookRootIndex.Admissible`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookRootIndex.Admissible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Require a(i)=0 at the first position, nonnegative heights, weakly increasing heights, and the original conditional RootFloorCriterion. When the length is positive, the first-position clause is a(0)=0. The empty tuple is also defined, although all registered common lengths are positive.

**Definition 1.3 (Distinct multiset sequences).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookRootIndex.rootPermutations`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookRootIndex.rootPermutations` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

List all permutations of the finite root list, deduplicate the lists as a Finset, and convert them back to fixed-length functions. Membership is equivalent to List.Perm of the root lists, hence equality of their integer multisets. Equal root entries receive no labels and create no extra indices.

**Definition 1.4 (The finite source index).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookRootIndex.indices`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookRootIndex.indices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Filter rootPermutations by Admissible. No original board-class search occurs in this definition.

**Definition 1.5 (Natural padded columns).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookRootIndex.decode`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookRootIndex.decode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the natural conversion of each integer height. Admissibility proves it is nonnegative, so conversion preserves the entire integer value.

**Definition 1.6 (The normalized representative).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookRootIndex.board`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookRootIndex.board` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Form the decoded weakly increasing column list and remove its zero prefix. The implementation filters zero entries; sortedness proves these entries form exactly a prefix. No positive column is removed or reordered. The empty positive-column list remains allowed.

**Definition 1.7 (Roots of the same reconstructed board).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookRootIndex.paddedRoots`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookRootIndex.paddedRoots` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Prepend zero columns to length N and subtract each resulting height from mi. The default-zero accessor makes the definition total; the reconstruction theorem proves the padded list has exactly the required length.

**Theorem 1.8 (Fixed-length representatives are distinct).**

$$\forall m \in Nat,\; \forall n \in Nat,\; \forall z \in \operatorname{Fin}\left(n\right) \to \mathbb{Z},\; \operatorname{Injective}\left(\operatorname{boardMap}\left(m, z\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/RookRootIndex.board_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Re-padding each reconstructed board recovers every decoded height, hence every original root. Equal normalized boards therefore give equal root sequences, including repeated roots and all-zero decoded tuples.

**Theorem 1.9 (Exact padding and geometric singleton law).**

$$\forall m \in Nat,\; 0 < m \Rightarrow \left(\forall n \in Nat,\; \forall z \in \operatorname{Fin}\left(n\right) \to \mathbb{Z},\; \forall a \in \operatorname{Member}\left(\operatorname{indices}\left(m, z\right)\right),\; \operatorname{pad}\left(n, \operatorname{board}\left(m, a\right)\right) = \operatorname{ofFn}\left(\operatorname{decode}\left(m, a\right)\right) \land (\operatorname{paddedRoots}\left(m, n, \operatorname{board}\left(m, a\right)\right) = a \land (\operatorname{SingletonColumns}\left(m, \operatorname{decode}\left(m, a\right)\right)))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/RookRootIndex.reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every positive m and every finite root seed z, each admissible index re-pads to its full decoded tuple, recovers its entire original root sequence, and satisfies the geometric singleton condition. For the seed of an input board, RookClassCandidate uses this reconstruction to recover each class member’s ordered level totals.

**Definition 1.10 (Root multiplicity factorials).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookRootIndex.multiplicityFactor`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookRootIndex.multiplicityFactor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply the factorial of each value's multiplicity over the distinct values of the root tuple. The empty product is one. A multiplicity counts positions with that value, without labeling the equal values.

**Theorem 1.11 (The simultaneous finite index specification).**

$$\forall m \in Nat,\; 0 < m \Rightarrow \left(\forall n \in Nat,\; \forall d \in \operatorname{Fin}\left(n\right) \to Nat,\; \operatorname{card}\left(\operatorname{indices}\left(m, \operatorname{root}\left(m, d\right)\right)\right) \le \frac{\operatorname{factorial}\left(n\right)}{\operatorname{multiplicityFactor}\left(\operatorname{root}\left(m, d\right)\right)} \land (\operatorname{Injective}\left(\operatorname{boardMap}\left(m, \operatorname{root}\left(m, d\right)\right)\right) \land (\forall a \in \operatorname{Member}\left(\operatorname{indices}\left(m, \operatorname{root}\left(m, d\right)\right)\right),\; \operatorname{pad}\left(n, \operatorname{board}\left(m, a\right)\right) = \operatorname{ofFn}\left(\operatorname{decode}\left(m, a\right)\right) \land (\operatorname{paddedRoots}\left(m, n, \operatorname{board}\left(m, a\right)\right) = a \land (\operatorname{SingletonColumns}\left(m, \operatorname{decode}\left(m, a\right)\right) \land (\operatorname{area}\left(\operatorname{board}\left(m, a\right)\right) = \operatorname{sum}\left(d\right))))))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/RookRootIndex.index_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any natural seed columns d, every admissible permutation reconstructs a board of exactly the sum of d. The same family has distinct normalized representatives, satisfies the exact padding and geometric singleton properties, and has cardinality at most N! divided by the product of the root multiplicity factorials. The bound reuses Mathlib's orbit-stabilizer theorem and DomMulAct.stabilizer_card', identifying the orbit with root-multiset sequences. Sum equality of roots proves area equality for the same reconstructed board. There is no singleton, positivity or sortedness restriction on the seed d; only the reconstructed columns are filtered. For a seed obtained from a normalized input board and a common length at least its area plus one, RookClassCandidate.universal_formula counts the native class by summing the sizes of these representatives’ ordered-level fibers.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/RookRootIndex.Admissible`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookRootIndex.board`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookRootIndex.board_injective`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookRootIndex.decode`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookRootIndex.heights`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookRootIndex.index_family`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookRootIndex.indices`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookRootIndex.multiplicityFactor`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookRootIndex.paddedRoots`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookRootIndex.reconstruction`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookRootIndex.rootPermutations`
- Dependency: [D5/S3/Combinatorics/Partitions/RookRootCriterion](RookRootCriterion.md)
