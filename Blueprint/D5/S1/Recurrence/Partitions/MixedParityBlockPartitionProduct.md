# Mixed-Parity Blocks in Set Partitions

## Abstract

Parity restriction and gluing prove Hanna's mixed-block partition product.

An element x of Fin n represents x+1 in the set from 1 through n. Thus even zero-based indices represent odd entries, and odd zero-based indices represent even entries. Every slash below is natural-number division.

The counting argument restricts each partition to its odd and even entries. A mixed block yields one marked block on each side, and the two marked families are paired. Gluing paired blocks reverses this restriction.

**Definition 1.1 (Set partitions).**

$$\forall r \in N, SetPartition(r) = Finpartition(univ(Fin(r)))$$

*Formalization.* `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.SetPartition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Set partitions of the universal finite set with r elements.

**Definition 1.2 (Stirling numbers of the second kind).**

$$\forall r \in N, \forall i \in N, stirling2(r,i) = card(\{P : SetPartition(r) \mid card(parts(P)) = i\})$$

*Formalization.* `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.stirling2` (`✓ std3`).

*Citation.* Paul D. Hanna (2006). *OEIS A124418, Triangle read by rows: T(n,k) is the number of partitions of the set {1,2,...,n} having exactly k blocks that contain both odd and even entries*. URL: <https://oeis.org/A124418>.

*Commentary.*

This is the number of partitions of an r-element set into i blocks, the Stirling number named in the OEIS formula. The alternating-sum closed form for that number is not established here.

**Definition 1.3 (Partitions with marked blocks).**

$$\forall r \in N, \forall k \in N, MarkedPartition(r,k) = \Sigma P : SetPartition(r), \{M : Finset(parts(P)) \mid card(M) = k\}$$

*Formalization.* `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.MarkedPartition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A marked partition consists of a partition and a k-element family of its blocks.

**Definition 1.4 (Number of marked partitions).**

$$\forall r \in N, \forall k \in N, markedPartitions(r,k) = card(MarkedPartition(r,k))$$

*Formalization.* `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.markedPartitions` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cardinality of the marked-partition family.

**Definition 1.5 (The A049020 triangle).**

$$\forall r \in N, \forall k \in N, A049020(r,k) = \sum_{i \in range(r + 1)} stirling2(r,i) \cdot choose(i,k)$$

*Formalization.* `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.A049020` (`✓ std3`).

*Citation.* Paul D. Hanna (2006). *OEIS A124418, Triangle read by rows: T(n,k) is the number of partitions of the set {1,2,...,n} having exactly k blocks that contain both odd and even entries*. URL: <https://oeis.org/A124418>.

*Commentary.*

For each possible block count i, choose k of the i blocks and sum over i.

**Theorem 1.6 (Marked partitions realize A049020).**

$$\forall r \in N, \forall k \in N, markedPartitions(r,k) = A049020(r,k)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.markedPartitions_eq_A049020` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Decomposition by the number of blocks gives one binomial choice per fiber.

**Definition 1.7 (Odd and even index carriers).**

$$\forall n \in N, ParityIndex(n) = Sum(Fin(\lfloor(n + 1) / 2\rfloor),Fin(\lfloor n / 2\rfloor))$$

*Formalization.* `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.ParityIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The left summand has the odd entries and the right summand has the even entries.

**Definition 1.8 (Parity-split blocks).**

$$\forall n \in N, ParityBlock(n) = Finset(Fin(\lfloor(n + 1) / 2\rfloor)) \times Finset(Fin(\lfloor n / 2\rfloor))$$

*Formalization.* `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.ParityBlock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A block is represented by its odd restriction and its even restriction.

**Definition 1.9 (Parity-split partitions).**

$$\forall n \in N, ParityPartition(n) = Finpartition((univ(Fin(\lfloor(n + 1) / 2\rfloor)), univ(Fin(\lfloor n / 2\rfloor))))$$

*Formalization.* `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.ParityPartition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These are partitions of the product lattice of odd and even subsets.

**Definition 1.10 (Mixed parity blocks).**

$$\forall n \in N, \forall b \in ParityBlock(n),\; (IsMixedBlock(b)) \Leftrightarrow (Nonempty(b.1) \land Nonempty(b.2))$$

*Formalization.* `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.IsMixedBlock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A parity-split block is mixed exactly when both coordinates are nonempty.

**Definition 1.11 (Number of mixed blocks).**

$$\forall n \in N, \forall P \in ParityPartition(n),\; mixedBlockCount(P) = card(filter(IsMixedBlock,parts(P)))$$

*Formalization.* `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.mixedBlockCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Filter the block family by mixedness and take its cardinality.

**Definition 1.12 (Partitions with k mixed blocks).**

$$\forall n \in N, \forall k \in N, MixedParityPartition(n,k) = \{P : ParityPartition(n) \mid mixedBlockCount(P) = k\}$$

*Formalization.* `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.MixedParityPartition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The subtype whose mixed-block count is k.

**Definition 1.13 (The parity-split model).**

$$\forall n \in N, \forall k \in N, T(n,k) = card(MixedParityPartition(n,k))$$

*Formalization.* `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.T` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cardinality of the parity-split partition family with k mixed blocks.

**Definition 1.14 (Literal mixed blocks).**

$$\forall n \in N, \forall b \in Finset(Fin(n)),\; (IsMixedBlockFin(b)) \Leftrightarrow (\left(\exists x \in b,\; Odd(x.val + 1)\right) \land \left(\exists x \in b,\; Even(x.val + 1)\right))$$

*Formalization.* `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.IsMixedBlockFin` (`✓ std3`).

*Citation.* Paul D. Hanna (2006). *OEIS A124418, Triangle read by rows: T(n,k) is the number of partitions of the set {1,2,...,n} having exactly k blocks that contain both odd and even entries*. URL: <https://oeis.org/A124418>.

*Commentary.*

For x representing x+1, a block contains witnesses of both entry parities.

**Definition 1.15 (The literal set-partition count).**

$$\forall n \in N, \forall k \in N, Tfin(n,k) = card(\{P : Finpartition(univ(Fin(n))) \mid card(filter(IsMixedBlockFin,parts(P))) = k\})$$

*Formalization.* `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.Tfin` (`✓ std3`).

*Citation.* Paul D. Hanna (2006). *OEIS A124418, Triangle read by rows: T(n,k) is the number of partitions of the set {1,2,...,n} having exactly k blocks that contain both odd and even entries*. URL: <https://oeis.org/A124418>.

*Commentary.*

This directly counts partitions of the set from 1 through n having exactly k blocks that contain both odd and even entries.

**Theorem 1.16 (The model agrees with the literal count).**

$$\forall n \in N, \forall k \in N, T(n,k) = Tfin(n,k)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.T_eq_Tfin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Splitting Fin n by parity transports partitions bijectively and preserves the number of mixed blocks.

**Definition 1.17 (The marked block family).**

$$\forall r \in N, \forall k \in N, \forall P \in MarkedPartition(r,k),\; MarkedBlocks(P) = P.2.1$$

*Formalization.* `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.MarkedBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Project the selected blocks from a marked partition.

**Definition 1.18 (Restriction and pairing data).**

$$\forall n \in N, \forall k \in N, RestrictionPairingData(n,k) = \Sigma odd : MarkedPartition(\lfloor(n + 1) / 2\rfloor,k), \Sigma even : MarkedPartition(\lfloor n / 2\rfloor,k), MarkedBlocks(odd) \equiv MarkedBlocks(even)$$

*Formalization.* `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.RestrictionPairingData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The data consists of marked odd and even partitions and a bijection between their marked blocks.

**Definition 1.19 (Restriction-gluing equivalence).**

$$\forall n \in N, \forall k \in N, MixedParityPartition(n,k) \equiv RestrictionPairingData(n,k)$$

*Formalization.* `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.mixedRestrictionEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restriction marks the halves of mixed blocks and pairs them. Gluing paired halves and retaining one-sided blocks is its two-sided inverse.

**Theorem 1.20 (Hanna's product formula).**

$$\forall n \in N, \forall k \in N, k \le \lfloor n / 2\rfloor \Rightarrow T(n,k) = k! \cdot A049020(\lfloor n / 2\rfloor,k) \cdot A049020(\lfloor(n + 1) / 2\rfloor,k)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.hanna_a124418` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a124418-mixed-parity-block-partition-product` (proved) by `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.hanna_a124418`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a124418-mixed-parity-block-partition-product","declaration_gid":"D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.hanna_a124418","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2006). *OEIS A124418, Triangle read by rows: T(n,k) is the number of partitions of the set {1,2,...,n} having exactly k blocks that contain both odd and even entries*. URL: <https://oeis.org/A124418>.

*Commentary.*

For k at most the integer quotient n/2, restriction produces two marked partitions and a bijection of their k marked blocks. The bijection contributes k factorial, while the marked families contribute the two A049020 factors.

## References

- Truth anchor: `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.A049020`
- Truth anchor: `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.IsMixedBlock`
- Truth anchor: `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.IsMixedBlockFin`
- Truth anchor: `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.MarkedBlocks`
- Truth anchor: `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.MarkedPartition`
- Truth anchor: `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.MixedParityPartition`
- Truth anchor: `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.ParityBlock`
- Truth anchor: `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.ParityIndex`
- Truth anchor: `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.ParityPartition`
- Truth anchor: `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.RestrictionPairingData`
- Truth anchor: `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.SetPartition`
- Truth anchor: `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.T`
- Truth anchor: `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.T_eq_Tfin`
- Truth anchor: `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.Tfin`
- Truth anchor: `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.hanna_a124418`
- Truth anchor: `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.markedPartitions`
- Truth anchor: `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.markedPartitions_eq_A049020`
- Truth anchor: `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.mixedBlockCount`
- Truth anchor: `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.mixedRestrictionEquiv`
- Truth anchor: `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.stirling2`
