# Two-layer solid partitions with a second layer of size 3

## Abstract

The two-layer solid partitions whose first layer is a plane partition of n and whose second layer is a plane partition of 3 number 3(2 A000219(n) - A000990(n) - 2 A000041(n) + 1), with A000219 the plane partitions, A000990 the plane partitions with at most two rows and A000041 the partitions of n, as conjectured by W. Meeussen for OEIS A381265.

**Definition 1.1 (Plane partitions).**

$$\operatorname{planeCount}\left(n\right) = \left|\{I \mid \operatorname{IsSolidPartition}\left(n, I\right)\}\right|$$

*Formalization.* `D5/S3/Combinatorics/TwoLayerSolidPartitions.planeCount` (`✓ std3`).

*Citation.* Wouter Meeussen (2025). *OEIS A381265, solid partitions with two layers and second layer a plane partition of 3: formula conjecture*. URL: <https://oeis.org/A381265>.

*Commentary.*

A000219(n), the plane partitions of n read through their diagrams: the lower sets of n cells of the cube of the natural numbers (IsSolidPartition of SolidPartitionFirstColumn in dimension 3).

**Definition 1.2 (Plane partitions with at most two rows).**

$$\operatorname{twoRowCount}\left(n\right) = \left|\{I \mid \operatorname{IsSolidPartition}\left(n, I\right) \land \left(\forall c \in I,\; c_{0} \le 1\right)\}\right|$$

*Formalization.* `D5/S3/Combinatorics/TwoLayerSolidPartitions.twoRowCount` (`✓ std3`).

*Citation.* Wouter Meeussen (2025). *OEIS A381265, solid partitions with two layers and second layer a plane partition of 3: formula conjecture*. URL: <https://oeis.org/A381265>.

*Commentary.*

A000990(n), the plane partitions of n whose cells all have first coordinate (row index) at most 1.

**Definition 1.3 (The sequence A381265).**

$$\operatorname{a}\left(n\right) = \left|\{(P1, P2) \mid \left(\operatorname{IsSolidPartition}\left(n, P1\right) \land \operatorname{IsSolidPartition}\left(3, P2\right)\right) \land P2 \subseteq P1\}\right|$$

*Formalization.* `D5/S3/Combinatorics/TwoLayerSolidPartitions.a` (`✓ std3`).

*Citation.* Wouter Meeussen (2025). *OEIS A381265, solid partitions with two layers and second layer a plane partition of 3: formula conjecture*. URL: <https://oeis.org/A381265>.

*Commentary.*

The pairs of a plane partition P1 of n (the first layer) and a plane partition P2 of 3 (the second layer) with P2 contained in P1, which are the two-layer solid partitions counted by the entry, whose data start a(3) = 6.

**Definition 1.4 (Meeussen's conjecture).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = 3 \cdot (2 \cdot \operatorname{planeCount}\left(n\right) - \operatorname{twoRowCount}\left(n\right) - 2 \cdot \left|\operatorname{Partition}\left(n\right)\right| + 1))$$

*Formalization.* `D5/S3/Combinatorics/TwoLayerSolidPartitions.claim` (`✓ std3`).

*Citation.* Wouter Meeussen (2025). *OEIS A381265, solid partitions with two layers and second layer a plane partition of 3: formula conjecture*. URL: <https://oeis.org/A381265>.

*Commentary.*

For every n the count equals three times 2 A000219(n) - A000990(n) - 2 A000041(n) + 1, with A000041(n) the number of partitions of n; both sides vanish for n < 3.

**Theorem 1.5 (Proof of the conjecture).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TwoLayerSolidPartitions.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Wouter Meeussen (2025). *OEIS A381265, solid partitions with two layers and second layer a plane partition of 3: formula conjecture*. URL: <https://oeis.org/A381265>.

*Commentary.*

The plane partitions of 3 are six: the three lines {0, e_k, 2 e_k} and the three corners {0, e_i, e_j}. A plane partition of n contains the line in direction k exactly when some cell has k-th coordinate at least 2, so by the bijections that permute the coordinates the three lines are each contained in A000219(n) - A000990(n) plane partitions of n. It contains the corner {0, e_i, e_j} exactly when it contains e_i and e_j. The plane partitions of n without e_i lie in the coordinate plane x_i = 0 and are the lower sets of n cells of the square of the natural numbers, which are the Young diagrams of the partitions of n (row lengths); those without e_i and e_j lie on the remaining axis, one for each n. So each corner is contained in A000219(n) - 2 A000041(n) + 1 of them, and summing over the six second layers gives the formula.

## References

- Truth anchor: `D5/S3/Combinatorics/TwoLayerSolidPartitions.a`
- Truth anchor: `D5/S3/Combinatorics/TwoLayerSolidPartitions.claim`
- Truth anchor: `D5/S3/Combinatorics/TwoLayerSolidPartitions.planeCount`
- Truth anchor: `D5/S3/Combinatorics/TwoLayerSolidPartitions.result`
- Truth anchor: `D5/S3/Combinatorics/TwoLayerSolidPartitions.twoRowCount`
- Dependency: [D5/S1/Words/Compositions/ZeroPrependedFirstSumsOddParts](../../S1/Words/Compositions/ZeroPrependedFirstSumsOddParts.md)
- Dependency: [D5/S3/Combinatorics/SolidPartitionFirstColumn](SolidPartitionFirstColumn.md)
