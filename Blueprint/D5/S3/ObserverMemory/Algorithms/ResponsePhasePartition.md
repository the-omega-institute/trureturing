# Native Response Phase Partitions

## Abstract

Bounded monotone ranks construct maximal native phases and one coherent final phase.

The coordinate type A is finite and may be empty. Replies have arbitrary universe and need no order. An explicit injective map into Fin(q+1) reflects equality; each installed coordinate is monotone in this rank. Write Adj(b) for IsChain of b with relation left.snd unequal to right.snd, and CoordinateMonotone(rank,obs) for monotonicity of the ranked reply at every coordinate, over all natural epochs.

**Definition 1.1 (Potential of the entire installed field).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/ResponsePhasePartition.potential`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/ResponsePhasePartition.potential` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For finite A, arbitrary R, natural q, rank from R to Fin(q+1), observation field obs from natural epochs to A to R, and epoch j, potential(rank,obs,j) is the sum over all a in A of rank(obs(j,a)).val. It lies between zero and q times card A. Coordinate monotonicity makes this sum nondecreasing. On two comparable epochs, a changed response vector has a changed coordinate; injectivity and the finite sum strict comparison charge at least one unit to that change.

**Theorem 1.2 (Finite native phases with sharp charge).**

$$\forall A, R: \operatorname{Type},\ [\operatorname{Fintype}(A)], \forall q\in \mathbb{N},\ \forall f: \mathbb{N} \to A \to R, k: R \to \operatorname{Fin}(q + 1),\ \operatorname{Injective}(k) \land \operatorname{CoordinateMonotone}(k, f) \implies\ \forall N\in \mathbb{N}, \forall J\in \mathbb{N}, N \leq J \implies\ \exists b: \operatorname{List}(\mathbb{N} \times (A \to R)),\ \operatorname{Partition}(f, N, J + 1, b) \land \operatorname{Adj}(b) \land\ \operatorname{length}(b) + \operatorname{potential}(k, f, N) \leq \operatorname{potential}(k, f, J) + 1$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/ResponsePhasePartition.finite_response_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every N at most J, the original native Partition covers [N,J+1) with nonempty intervals, strictly increasing delimiters and exact terminal delimiter J+1. Adjacent replies differ, so these are maximal constant-response intervals within [N,J]. The sharper bound is length plus potential at N at most potential at J plus one. It implies at most q times card A plus one phases. No change is required after J.

Construct the partition by backward interval-length induction. A singleton epoch has its observation as reply. For the suffix starting at N+1, its first nonempty guard identifies its reply with obs(N+1). If obs(N) agrees, extend that guard to N. Otherwise prepend the singleton epoch and charge its extra block to the strict potential increase. The guard and delimiter invariants are carried by this same construction.

When A is empty or q is zero the count is one. N equals J gives the one-epoch partition. Duplicate installed addresses and simultaneous coordinate changes do not add separate phases.

**Theorem 1.3 (One prefix for every cutoff).**

$$\forall A, R: \operatorname{Type},\ [\operatorname{Fintype}(A)], \forall q\in \mathbb{N},\ \forall f: \mathbb{N} \to A \to R, k: R \to \operatorname{Fin}(q + 1),\ \operatorname{Injective}(k) \land \operatorname{CoordinateMonotone}(k, f) \implies\ \forall N\in \mathbb{N},  \exists b: \operatorname{List}(\mathbb{N} \times (A \to R)), s\in \mathbb{N}, z: A \to R,\ N \leq s \land (\forall J\in \mathbb{N}, s \leq J \implies f(J) = z) \land\ \operatorname{Adj}(b ++ [(s + 1, z)]) \land \operatorname{length}(b) + 1 \leq q \times \operatorname{card}(A) + 1 \land\ \forall J\in \mathbb{N}, s \leq J \implies \operatorname{Partition}(f, N, J + 1, b ++ [(J + 1, z)])$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/ResponsePhasePartition.half_line_response_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each N choose one finite prefix b, start s and reply z before quantifying over cutoffs. The field equals z at every epoch from s. The prefix followed by z has distinct adjacent replies and at most q times card A plus one blocks. Every J at least s has exactly the native partition b appended with [(J+1,z)]. Thus all cutoffs share the same prefix and final guard; an empty prefix starts that guard at N.

Apply the finite-order monotone-chain condition to the entire rank vector. Rank injectivity reflects its stabilized equality to the observation field. Take a stable epoch T at least N and the finite native partition through T. Split off its last block and retain that block's actual start s. Its old finite guard and the stable tail prove constancy from s. Replacing only the last delimiter works also when s is at most J and J is less than T. Appending an extra equal-response tail would lose maximality.

This is an existential coherent phase decomposition. It supplies no computable last-change detector or bound on s, phase duration, reads, instructions or updates. Changes can be arbitrarily delayed.

For the uniform descriptor task, A is ALL installed read-state occurrences E_R, including unvisited states and occurrences installing duplicate literals. Fix one common descriptor tuple and one original source u. At coordinate e, obs(j,e) is the read of its fixed installed literal p(delta_e) on U iterated j times applied to u. Every phase uses this same source and tuple. In the native program Q=E, a read state e reads that occurrence's installed literal. The vector in the proof adds no simultaneous-response access port.

UDB.5 gives rank monotonicity after reach. Reach persistence and the least absent rank supply the remaining comparable epochs, yielding UDB.6 coordinate by coordinate. The injective rank hypothesis remains explicit. The source says finite ordered alphabet without explicitly saying linear; StrictMono.injective requires a LinearOrder domain. An order interpretation establishing equality reflection is therefore a separate source condition. No unconditional theorem for arbitrary partial reply orders follows.

The native guards can be combined with guarded_phase_execution for the same program and observation field. Effective shared-source guard formulas, rank and descriptor synthesis, and their full uniform composition remain separate obligations. This component is a repository-derived construction using the pinned finite-sum and monotone-chain results; no literature novelty is asserted.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/ResponsePhasePartition.finite_response_partition`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/ResponsePhasePartition.half_line_response_partition`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/ResponsePhasePartition.potential`
- Dependency: [D5/S3/ObserverMemory/Algorithms/GuardedPhaseExecution](GuardedPhaseExecution.md)
