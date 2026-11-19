# Unit transfers and local simplex layers

## Abstract

Actual integer-partition unit transfers determine finite clique maxima and exact local layers.

Nat denotes the nonnegative integers. Partition(n) is the multiset of positive parts with sum n. Every occurrence is retained. A unit transfer removes one unit from one part occurrence and adds it to a distinct occurrence or to a virtual zero row; zero remainders disappear. The resulting partition must differ from the original. YoungDiagram.ofPartition sorts the parts and draws each row as an initial interval of cells. All cliques, maxima and layer cardinalities below use the actual finite partition carrier.

**Definition 1.1 (All finite cliques).**

$$\forall n \in Nat,\; \forall s \in \operatorname{Finset}\left(\operatorname{Partition}\left(n\right)\right),\; s \in \operatorname{cliques}\left(n\right) \Leftrightarrow \operatorname{IsClique}\left(\operatorname{graph}\left(n\right), s\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.cliques` (`✓ std3`).

*Citation.* Fedor B. Lyudogovskiy (2026). *Simplex Stratification and Phase Boundaries in the Partition Graph*. URL: <https://arxiv.org/html/2603.23228v1>.

*Commentary.*

The collection includes singletons and the empty clique.

**Definition 1.2 (The largest clique through a vertex).**

$$\forall n \in Nat,\; \forall p \in \operatorname{Partition}\left(n\right),\; \operatorname{localDimension}\left(p\right) = \operatorname{max}\left(\operatorname{cliqueDimensionsContaining}\left(n, p\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.localDimension` (`✓ std3`).

*Citation.* Fedor B. Lyudogovskiy (2026). *Simplex Stratification and Phase Boundaries in the Partition Graph*. URL: <https://arxiv.org/html/2603.23228v1>.

*Commentary.*

cliqueDimensionsContaining(n,p) contains card(s)-1 for every clique s containing p. The singleton clique ensures this collection is nonempty.

**Definition 1.3 (An exact level).**

$$\forall r \in Nat,\; \forall n \in Nat,\; \forall p \in \operatorname{Partition}\left(n\right),\; p \in \operatorname{layer}\left(r, n\right) \Leftrightarrow \operatorname{localDimension}\left(p\right) = r$$

*Formalization.* `D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.layer` (`✓ std3`).

*Citation.* Fedor B. Lyudogovskiy (2026). *Simplex Stratification and Phase Boundaries in the Partition Graph*. URL: <https://arxiv.org/html/2603.23228v1>.

*Commentary.*

An exact level.

**Definition 1.4 (Maximum local dimension).**

$$\forall n \in Nat,\; \operatorname{maxDimension}\left(n\right) = \operatorname{max}\left(\operatorname{localDimensions}\left(n\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.maxDimension` (`✓ std3`).

*Citation.* Fedor B. Lyudogovskiy (2026). *Simplex Stratification and Phase Boundaries in the Partition Graph*. URL: <https://arxiv.org/html/2603.23228v1>.

*Commentary.*

localDimensions(n) is the finite collection of localDimension(p) over all integer partitions p of n. Every n has a partition, so this maximum is attained.

**Definition 1.5 (Least positive occurrence).**

$$\forall r \in Nat,\; \operatorname{threshold}\left(r\right) = \operatorname{sInf}\left(\operatorname{positiveNonemptyLevels}\left(r\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.threshold` (`✓ std3`).

*Citation.* Fedor B. Lyudogovskiy (2026). *Simplex Stratification and Phase Boundaries in the Partition Graph*. URL: <https://arxiv.org/html/2603.23228v1>.

*Commentary.*

positiveNonemptyLevels(r) contains precisely the positive n with a nonempty exact layer(r,n). The natural-number infimum is zero when this set is empty; the full threshold claim explicitly requires existence and leastness.

**Definition 1.6 (Triangular sizes).**

$$\forall r \in Nat,\; \operatorname{triangular}\left(r\right) = \operatorname{natDiv}\left(r \cdot \left(r + 1\right), 2\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.triangular` (`✓ std3`).

*Citation.* Fedor B. Lyudogovskiy (2026). *Simplex Stratification and Phase Boundaries in the Partition Graph*. URL: <https://arxiv.org/html/2603.23228v1>.

*Commentary.*

Triangular sizes.

**Definition 1.7 (The staircase ideal).**

$$\forall r \in Nat,\; \forall i \in Nat,\; \forall j \in Nat,\; \operatorname{pair}\left(i, j\right) \in \operatorname{staircase}\left(r\right) \Leftrightarrow i + j < r$$

*Formalization.* `D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.staircase` (`✓ std3`).

*Citation.* Fedor B. Lyudogovskiy (2026). *Simplex Stratification and Phase Boundaries in the Partition Graph*. URL: <https://arxiv.org/html/2603.23228v1>.

*Commentary.*

The ideal is empty at r=0 and has row lengths r,r-1,...,1 for positive r.

**Definition 1.8 (All addable one-cell extensions).**

$$\forall r \in Nat,\; \forall n \in Nat,\; \forall p \in \operatorname{Partition}\left(n\right),\; p \in \operatorname{firstFamily}\left(r, n\right) \Leftrightarrow \left(\operatorname{subset}\left(\operatorname{cells}\left(\operatorname{staircase}\left(r\right)\right), \operatorname{cells}\left(\operatorname{ofPartition}\left(p\right)\right)\right) \land \operatorname{card}\left(\operatorname{sdiff}\left(\operatorname{cells}\left(\operatorname{ofPartition}\left(p\right)\right), \operatorname{cells}\left(\operatorname{staircase}\left(r\right)\right)\right)\right) = 1\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.firstFamily` (`✓ std3`).

*Citation.* Fedor B. Lyudogovskiy (2026). *Simplex Stratification and Phase Boundaries in the Partition Graph*. URL: <https://arxiv.org/html/2603.23228v1>.

*Commentary.*

All addable one-cell extensions.

**Definition 1.9 (The full threshold question).**

$$\operatorname{ThresholdClaim}\left(\right) \Leftrightarrow \left(\left(\forall r \in Nat,\; \operatorname{threshold}\left(r\right) = \operatorname{triangular}\left(r\right) + 1 \land \operatorname{IsLeast}\left(\operatorname{positiveNonemptyLevels}\left(r\right), \operatorname{triangular}\left(r\right) + 1\right)\right) \land \left(\forall n \in Nat,\; 0 < n \Rightarrow \operatorname{maxDimension}\left(n\right) = \operatorname{max}\left(\operatorname{triangularRanksBelow}\left(n\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.ThresholdClaim` (`✓ std3`).

*Citation.* Fedor B. Lyudogovskiy (2026). *Simplex Stratification and Phase Boundaries in the Partition Graph*. URL: <https://arxiv.org/html/2603.23228v1>.

*Commentary.*

triangularRanksBelow(n) is the finite set of r<=n for which triangular(r)+1<=n. The cutoff omits no feasible natural rank: r<=triangular(r), so triangular(r)+1<=n implies r<n. This proposition specifies the entire threshold and maximum problem; its definition supplies no proof of that proposition.

**Definition 1.10 (The full first-family question).**

$$\operatorname{FirstOccurrenceClaim}\left(\right) \Leftrightarrow \left(\forall r \in Nat,\; 2 \le r \Rightarrow \left(\operatorname{layer}\left(r, \operatorname{threshold}\left(r\right)\right) = \operatorname{firstFamily}\left(r, \operatorname{threshold}\left(r\right)\right) \land \left(\operatorname{layer}\left(r, \operatorname{triangular}\left(r\right) + 1\right) = \operatorname{firstFamily}\left(r, \operatorname{triangular}\left(r\right) + 1\right) \land \operatorname{card}\left(\operatorname{firstFamily}\left(r, \operatorname{threshold}\left(r\right)\right)\right) = r + 1\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.FirstOccurrenceClaim` (`✓ std3`).

*Citation.* Fedor B. Lyudogovskiy (2026). *Simplex Stratification and Phase Boundaries in the Partition Graph*. URL: <https://arxiv.org/html/2603.23228v1>.

*Commentary.*

Both equalities concern full finite vertex sets. The cardinality requires r+1 distinct members. This proposition includes r=2 and has no upper bound on r; its definition supplies no proof.

**Theorem 1.11 (The complete threshold formula).**

$$\left(\forall r \in Nat,\; \operatorname{threshold}\left(r\right) = \operatorname{triangular}\left(r\right) + 1 \land \operatorname{IsLeast}\left(\operatorname{positiveNonemptyLevels}\left(r\right), \operatorname{triangular}\left(r\right) + 1\right)\right) \land \left(\forall n \in Nat,\; 0 < n \Rightarrow \operatorname{maxDimension}\left(n\right) = \operatorname{max}\left(\operatorname{triangularRanksBelow}\left(n\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.threshold_result` (`✓ std3`). ∎

*Resolves.* `Problems/lyudogovskiy-2026-simplex-threshold` (proved) by `D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.threshold_result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lyudogovskiy-2026-simplex-threshold","declaration_gid":"D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.threshold_result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Fedor B. Lyudogovskiy (2026). *Simplex Stratification and Phase Boundaries in the Partition Graph*. URL: <https://arxiv.org/html/2603.23228v1>.

*Commentary.*

For every r, the positive size triangular(r)+1 has a nonempty exact layer and is its least positive occurrence. Separately, every positive n has the displayed maximum. The proof bounds every actual clique through the star/top alternatives, constructs r+1 genuine extensions of an enlarged staircase at every feasible size, and uses finite attainment. No assumption that the local-dimension spectrum is contiguous is used.

**Theorem 1.12 (The entire first-occurrence family).**

$$\forall r \in Nat,\; 2 \le r \Rightarrow \left(\operatorname{layer}\left(r, \operatorname{threshold}\left(r\right)\right) = \operatorname{firstFamily}\left(r, \operatorname{threshold}\left(r\right)\right) \land \left(\operatorname{layer}\left(r, \operatorname{triangular}\left(r\right) + 1\right) = \operatorname{firstFamily}\left(r, \operatorname{triangular}\left(r\right) + 1\right) \land \operatorname{card}\left(\operatorname{firstFamily}\left(r, \operatorname{threshold}\left(r\right)\right)\right) = r + 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.first_occurrence_result` (`✓ std3`). ∎

*Resolves.* `Problems/lyudogovskiy-2026-first-occurrence-family` (proved) by `D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.first_occurrence_result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lyudogovskiy-2026-first-occurrence-family","declaration_gid":"D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.first_occurrence_result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Fedor B. Lyudogovskiy (2026). *Simplex Stratification and Phase Boundaries in the Partition Graph*. URL: <https://arxiv.org/html/2603.23228v1>.

*Commentary.*

For every r at least two, a clique of dimension r at the first size cannot be a top: its containing diagram would require triangular(r+1) cells but has only triangular(r)+2. A star predecessor contains the size-triangular(r) staircase and therefore equals it. Conversely every addable staircase extension lies in the full r+1-member star; the sharp maximum forces exact local dimension r. Distinct addable cells give distinct partitions. The threshold identity connects this full set equality to the literal threshold argument.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.FirstOccurrenceClaim`
- Truth anchor: `D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.ThresholdClaim`
- Truth anchor: `D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.cliques`
- Truth anchor: `D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.firstFamily`
- Truth anchor: `D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.first_occurrence_result`
- Truth anchor: `D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.layer`
- Truth anchor: `D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.localDimension`
- Truth anchor: `D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.maxDimension`
- Truth anchor: `D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.staircase`
- Truth anchor: `D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.threshold`
- Truth anchor: `D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.threshold_result`
- Truth anchor: `D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.triangular`
- Dependency: [D5/S3/Combinatorics/Partitions/LyudogovskiyTransfers](LyudogovskiyTransfers.md)
