# Ternary mode orbits and partition counting

## Abstract

Nonzero ternary modes modulo sign are classified by their anchored equality partitions, for any index type and any choice of opposite-pair representatives.

Akella, Iizuka and Miyata, arXiv:2607.06050v2, Section 6, ask whether a counting argument analogous to their n=2 Coxeter argument exists at n=3. The theorem below is consumed by TernaryPartitionCounting, whose generic merger transport and arbitrary-weight result feed the structural partition-counting proof in StabilizerMultiEntropyCollapse for the n=3 four-party relation. Surjective mergers induce quotient colourings, normalization at the chosen target anchor removes translation, and representative selection transports arbitrary weighted sums. This does not identify a Coxeter group or settle other party or replica counts.

Akella and Gadde, Rényi multi-entropy of graph states and the n → 1 limit, arXiv:2610.27080v1 (19 October 2026), Section II Eqs. (7)–(9) and Appendix A, prove an odd-replica rank formula whose n=3 specialization also implies the four-party collapse. At n=3 the three nonzero F₄ labels give an invertible diagonal rescaling to the equality-partition separation matrix. Restoring the factor n^{−(q−2)} explicitly omitted in their Eq. (2) gives the normalization used here. This delivery supplies a structural formal proof and reusable partition library for an existing conclusion; it makes no new unique-solve or global-priority claim. The Section 6 quotation above records the source-text question, not a current certification that no other proof exists.

**Definition 1.1 (Equality of induced partitions).**

Lean statement: `D5/S3/Combinatorics/Partitions/TernaryPartitionOrbit.SamePartition`

*Formalization.* `D5/S3/Combinatorics/Partitions/TernaryPartitionOrbit.SamePartition` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

Two colourings have the same partition when every pair of indices has equal colours in one colouring exactly when it has equal colours in the other. The index type may be infinite or empty.

**Definition 1.2 (Fixing an additional colour at zero).**

Lean statement: `D5/S3/Combinatorics/Partitions/TernaryPartitionOrbit.anchored`

*Formalization.* `D5/S3/Combinatorics/Partitions/TernaryPartitionOrbit.anchored` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

anchored(u) assigns zero to none and assigns u(i) to some(i). A nonzero u therefore produces a nonconstant anchored colouring, including when some of its entries are zero.

**Theorem 1.3 (Opposite-pair representatives classify every anchored ternary partition).**

Lean statement: `D5/S3/Combinatorics/Partitions/TernaryPartitionOrbit.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/TernaryPartitionOrbit.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

The representative set P may be any set of ternary modes that contains exactly one of u and -u for each nonzero u. For every nonzero mode u there is exactly one member v of P with the same anchored equality partition. These are partitions with two or three blocks that are realized by anchored ternary colourings; the all-constant partition and partitions with four or more blocks are outside the conclusion. No finiteness or choice of coordinates is assumed. The proof first constructs the unique affine permutation between nonconstant ternary colourings with the same equality partition: two distinct colours determine the slope and intercept, and a third distinct colour is minus the other two. Fixing the anchor at zero forces the intercept to vanish, so the only remaining slopes are 1 and -1.

## The thirteen four-party patterns

For three free coordinates and the fourth party anchored at zero, select the first nonzero coordinate to be 1. The 26 nonzero ternary modes form thirteen opposite pairs, giving the thirteen modes listed below. Their partitions have two or three blocks; the one-block and four-block partitions do not occur. The theorem explains why these rows are distinct partition patterns. A merger contributes exactly when its two labels lie in the same block; the number of such mergers is the sum of choose(block size,2).

mode 001: ABD:C; 3 compatible pair mergers; signed coefficient 1-3+2=0.

mode 010: ACD:B; 3 compatible pair mergers; signed coefficient 1-3+2=0.

mode 011: AD:BC; 2 compatible pair mergers; signed coefficient 1-2+1=0.

mode 012: AD:B:C; 1 compatible pair merger; signed coefficient 1-1=0.

mode 100: A:BCD; 3 compatible pair mergers; signed coefficient 1-3+2=0.

mode 101: AC:BD; 2 compatible pair mergers; signed coefficient 1-2+1=0.

mode 102: A:BD:C; 1 compatible pair merger; signed coefficient 1-1=0.

mode 110: AB:CD; 2 compatible pair mergers; signed coefficient 1-2+1=0.

mode 111: ABC:D; 3 compatible pair mergers; signed coefficient 1-3+2=0.

mode 112: AB:C:D; 1 compatible pair merger; signed coefficient 1-1=0.

mode 120: A:B:CD; 1 compatible pair merger; signed coefficient 1-1=0.

mode 121: AC:B:D; 1 compatible pair merger; signed coefficient 1-1=0.

mode 122: A:BC:D; 1 compatible pair merger; signed coefficient 1-1=0.

Thus the 2+1+1 patterns cancel against one merger, the 2+2 patterns require one bipartite correction, and the 3+1 patterns require twice the singleton-cut correction. Multiplying each row by an arbitrary coefficient f of its equality partition yields the signed-incidence relation used by StabilizerMultiEntropyCollapse.partition_count. The production partition_count proof now uses the orbit theorem through a merger-to-partition bijection and a finite partition-coefficient cancellation, rather than only interpreting the existing identity. This foundation module adds no independent finite enumeration theorem or new entropy-collapse statement.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/TernaryPartitionOrbit.SamePartition`
- Truth anchor: `D5/S3/Combinatorics/Partitions/TernaryPartitionOrbit.anchored`
- Truth anchor: `D5/S3/Combinatorics/Partitions/TernaryPartitionOrbit.result`
