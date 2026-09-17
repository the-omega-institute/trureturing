# A nonheavy partition below a heavy rectangle

## Abstract

The PNim heavy-interval conjecture fails at a = 8, b = 7.

**Definition 1.1 (Row lengths).**

$$Position = \operatorname{List}\left(\mathrm{Nat}\right)$$

*Formalization.* `D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.Position` (`✓ std3`).

*Citation.* Eric Gottlieb; Matjaž Krnc; Peter Muršič (2025). *Nim on Integer Partitions and Hyperrectangles*. DOI: [10.48550/arXiv.2506.04991](https://doi.org/10.48550/arXiv.2506.04991). URL: <https://arxiv.org/abs/2506.04991>.

*Commentary.*

Positions are lists of natural row lengths. The predicate IsPartition restricts them to nonincreasing positive lists, including the empty list.

**Definition 1.2 (Deleting diagram columns).**

$$\forall p \in Position,\; \forall deleted \in Position,\; \operatorname{deleteColumns}\left(p, deleted\right) = List.filter\left((\lambda n \mapsto n \ne 0), List.map\left((\lambda n \mapsto n - List.length\left(List.filter\left((\lambda j \mapsto j < n), deleted\right)\right)), p\right)\right)$$

*Formalization.* `D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.deleteColumns` (`✓ std3`).

*Citation.* Eric Gottlieb; Matjaž Krnc; Peter Muršič (2025). *Nim on Integer Partitions and Hyperrectangles*. DOI: [10.48550/arXiv.2506.04991](https://doi.org/10.48550/arXiv.2506.04991). URL: <https://arxiv.org/abs/2506.04991>.

*Commentary.*

Columns are numbered from zero. Each row n loses precisely the deleted indices j smaller than n; rows reduced to zero are omitted. Remaining columns merge. The filter tests are Boolean comparisons. The deleted list is generated without repetition from the first-row column range.

**Definition 1.3 (Deleting nonempty row subsets).**

$$\forall p \in Position,\; \operatorname{rowMoves}\left(p\right) = List.filter\left((\lambda q \mapsto \operatorname{length}\left(q\right) < \operatorname{length}\left(p\right)), List.sublists\left(p\right)\right)$$

*Formalization.* `D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.rowMoves` (`✓ std3`).

*Citation.* Eric Gottlieb; Matjaž Krnc; Peter Muršič (2025). *Nim on Integer Partitions and Hyperrectangles*. DOI: [10.48550/arXiv.2506.04991](https://doi.org/10.48550/arXiv.2506.04991). URL: <https://arxiv.org/abs/2506.04991>.

*Commentary.*

List.sublists enumerates all retained row subsequences. Strictly smaller length selects exactly deletions of at least one row; the empty subsequence deletes every row.

**Definition 1.4 (Deleting nonempty column subsets).**

$$\forall p \in Position,\; \operatorname{columnMoves}\left(p\right) = List.map\left((\lambda deleted \mapsto \operatorname{deleteColumns}\left(p, deleted\right)), List.filter\left((\lambda deleted \mapsto deleted \ne []), List.sublists\left(List.range\left(\operatorname{headD}\left(p, 0\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.columnMoves` (`✓ std3`).

*Citation.* Eric Gottlieb; Matjaž Krnc; Peter Muršič (2025). *Nim on Integer Partitions and Hyperrectangles*. DOI: [10.48550/arXiv.2506.04991](https://doi.org/10.48550/arXiv.2506.04991). URL: <https://arxiv.org/abs/2506.04991>.

*Commentary.*

The first row supplies every diagram column of a partition. All nonempty subsets of its zero-based range are deleted by deleteColumns. headD(p,0) is the first row, with default zero for the empty list.

**Definition 1.5 (All PNim followers).**

$$\forall p \in Position,\; \operatorname{moves}\left(p\right) = List.filter\left((\lambda q \mapsto \operatorname{sum}\left(q\right) < \operatorname{sum}\left(p\right)), List.append\left(\operatorname{rowMoves}\left(p\right), \operatorname{columnMoves}\left(p\right)\right)\right)$$

*Formalization.* `D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.moves` (`✓ std3`).

*Citation.* Eric Gottlieb; Matjaž Krnc; Peter Muršič (2025). *Nim on Integer Partitions and Hyperrectangles*. DOI: [10.48550/arXiv.2506.04991](https://doi.org/10.48550/arXiv.2506.04991). URL: <https://arxiv.org/abs/2506.04991>.

*Commentary.*

The row and column options are concatenated, then restricted to strictly smaller cell count. This last filter changes no move of a positive nonincreasing partition. It extends termination to arbitrary natural lists. Repeated followers do not affect the finite set used by mex.

**Definition 1.6 (The least excluded natural number).**

$$\forall s \in \operatorname{Finset}\left(\mathrm{Nat}\right),\; \operatorname{mex}\left(s\right)$$

*Formalization.* `D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.mex` (`✓ std3`).

*Citation.* Eric Gottlieb; Matjaž Krnc; Peter Muršič (2025). *Nim on Integer Partitions and Hyperrectangles*. DOI: [10.48550/arXiv.2506.04991](https://doi.org/10.48550/arXiv.2506.04991). URL: <https://arxiv.org/abs/2506.04991>.

*Commentary.*

mex(s) denotes the least natural number that is absent from s. The finite minimum over range(card(s)+1) minus s computes this value; the finite-set cardinality argument guarantees that the missing set is nonempty.

**Definition 1.7 (Grundy evaluation by cell count).**

$$\forall p \in Position,\; \operatorname{grundy}\left(p\right) = \operatorname{mex}\left(\left\{\operatorname{grundy}\left(q\right) \mid q \in \operatorname{moves}\left(p\right)\right\}\right)$$

*Formalization.* `D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.grundy` (`✓ std3`).

*Citation.* Eric Gottlieb; Matjaž Krnc; Peter Muršič (2025). *Nim on Integer Partitions and Hyperrectangles*. DOI: [10.48550/arXiv.2506.04991](https://doi.org/10.48550/arXiv.2506.04991). URL: <https://arxiv.org/abs/2506.04991>.

*Commentary.*

The Lean definition uses well-founded recursion on cell count. Its private proof-carrying lemmas move_decreases and missing_nonempty establish termination and finite-minimum existence, but are not part of the mathematical statement. The terminal empty list has value zero.

**Definition 1.8 (Positive nonincreasing partitions).**

$$\forall p \in Position,\; (\operatorname{IsPartition}\left(p\right)) \Leftrightarrow ((List.Pairwise\left((\lambda x \mapsto (\lambda y \mapsto x \ge y)), p\right)) \land (List.all\left((\lambda n \mapsto n > 0), p\right) = true))$$

*Formalization.* `D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.IsPartition` (`✓ std3`).

*Citation.* Eric Gottlieb; Matjaž Krnc; Peter Muršič (2025). *Nim on Integer Partitions and Hyperrectangles*. DOI: [10.48550/arXiv.2506.04991](https://doi.org/10.48550/arXiv.2506.04991). URL: <https://arxiv.org/abs/2506.04991>.

*Commentary.*

Pairwise requires each earlier row to be at least each later row. The Boolean all test requires every row length to be positive.

**Definition 1.9 (Young's-lattice order).**

$$\forall p \in Position,\; \forall q \in Position,\; (\operatorname{youngLE}\left(p, q\right)) \Leftrightarrow ((\operatorname{length}\left(p\right) \le \operatorname{length}\left(q\right)) \land (List.all\left((\lambda pair \mapsto \operatorname{fst}\left(pair\right) \le \operatorname{snd}\left(pair\right)), List.zip\left(p, q\right)\right) = true))$$

*Formalization.* `D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.youngLE` (`✓ std3`).

*Citation.* Eric Gottlieb; Matjaž Krnc; Peter Muršič (2025). *Nim on Integer Partitions and Hyperrectangles*. DOI: [10.48550/arXiv.2506.04991](https://doi.org/10.48550/arXiv.2506.04991). URL: <https://arxiv.org/abs/2506.04991>.

*Commentary.*

The lower list must be no longer than the upper list, and each aligned pair must satisfy first component at most second component. zip therefore checks every lower row. fst and snd denote pair projections.

**Definition 1.10 (The upper rectangle).**

$$\forall a \in \mathrm{Nat},\; \forall b \in \mathrm{Nat},\; \operatorname{rectangle}\left(a, b\right) = List.replicate\left(b + 1, a + 1\right)$$

*Formalization.* `D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.rectangle` (`✓ std3`).

*Citation.* Eric Gottlieb; Matjaž Krnc; Peter Muršič (2025). *Nim on Integer Partitions and Hyperrectangles*. DOI: [10.48550/arXiv.2506.04991](https://doi.org/10.48550/arXiv.2506.04991). URL: <https://arxiv.org/abs/2506.04991>.

*Commentary.*

The rectangle contains b+1 copies of a+1, exactly the upper endpoint in printed Conjecture 2.

**Definition 1.11 (The lower staircase).**

$$\forall a \in \mathrm{Nat},\; \forall b \in \mathrm{Nat},\; \operatorname{staircase}\left(a, b\right) = List.map\left((\lambda i \mapsto a + 1 - i), List.range\left(b + 1\right)\right)$$

*Formalization.* `D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.staircase` (`✓ std3`).

*Citation.* Eric Gottlieb; Matjaž Krnc; Peter Muršič (2025). *Nim on Integer Partitions and Hyperrectangles*. DOI: [10.48550/arXiv.2506.04991](https://doi.org/10.48550/arXiv.2506.04991). URL: <https://arxiv.org/abs/2506.04991>.

*Commentary.*

Mapping i to a+1-i over range(b+1) gives [a+1,a,...,a-b+1]. Subtraction is natural subtraction; b at most a makes all parts positive.

**Definition 1.12 (Heaviness and longest play).**

$$\forall p \in Position,\; (\operatorname{heavy}\left(p\right)) \Leftrightarrow ((p \ne []) \land (\operatorname{grundy}\left(p\right) = \operatorname{headD}\left(p, 0\right) + \operatorname{length}\left(p\right) - 1))$$

*Formalization.* `D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.heavy` (`✓ std3`).

*Citation.* Eric Gottlieb; Matjaž Krnc; Peter Muršič (2025). *Nim on Integer Partitions and Hyperrectangles*. DOI: [10.48550/arXiv.2506.04991](https://doi.org/10.48550/arXiv.2506.04991). URL: <https://arxiv.org/abs/2506.04991>.

*Commentary.*

A nonempty partition is heavy when its Grundy value equals its first row plus its row count minus one. Proposition 2 gives exactly this longest-play length. All arithmetic here is on natural numbers.

**Definition 1.13 (Conjecture 2 as printed).**

$$(claim) \Leftrightarrow (\forall a \in \mathrm{Nat},\; \forall b \in \mathrm{Nat},\; (b \le a) \Rightarrow ((\operatorname{heavy}\left(\operatorname{rectangle}\left(a, b\right)\right)) \Rightarrow (\forall p \in Position,\; (\operatorname{IsPartition}\left(p\right)) \Rightarrow ((\operatorname{youngLE}\left(\operatorname{staircase}\left(a, b\right), p\right)) \Rightarrow ((\operatorname{youngLE}\left(p, \operatorname{rectangle}\left(a, b\right)\right)) \Rightarrow (\operatorname{heavy}\left(p\right)))))))$$

*Formalization.* `D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.claim` (`✓ std3`).

*Citation.* Eric Gottlieb; Matjaž Krnc; Peter Muršič (2025). *Nim on Integer Partitions and Hyperrectangles*. DOI: [10.48550/arXiv.2506.04991](https://doi.org/10.48550/arXiv.2506.04991). URL: <https://arxiv.org/abs/2506.04991>.

*Commentary.*

Natural a,b with b at most a encode exactly the integer parameters for which both endpoints are partitions. For every partition p in the closed Young interval, the conjecture predicts heaviness whenever the upper rectangle is heavy.

**Theorem 1.14 (The printed heavy-interval conjecture is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric Gottlieb; Matjaž Krnc; Peter Muršič (2025). *Nim on Integer Partitions and Hyperrectangles*. DOI: [10.48550/arXiv.2506.04991](https://doi.org/10.48550/arXiv.2506.04991). URL: <https://arxiv.org/abs/2506.04991>.

*Commentary.*

At a=8 and b=7 the rectangle is [9,9,9,9,9,9,9,9], with Grundy value 16 and longest-play length 16. The partition [9,9,8,8,8,5,5,5] lies above [9,8,7,6,5,4,3,2] and below that rectangle, but its Grundy value is 3 rather than 16.

A finite table contains the partition and all its descendants. At every entry, the kernel verifies that all followers are present, the assigned value is absent from their values, and every smaller natural occurs. Induction on cell count equates the table with the recursive Grundy function. A second table establishes the rectangle premise. Only printed Conjecture 2 is refuted; no priority or corrected formula is asserted.

## References

- Truth anchor: `D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.IsPartition`
- Truth anchor: `D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.Position`
- Truth anchor: `D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.claim`
- Truth anchor: `D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.columnMoves`
- Truth anchor: `D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.deleteColumns`
- Truth anchor: `D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.grundy`
- Truth anchor: `D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.heavy`
- Truth anchor: `D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.mex`
- Truth anchor: `D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.moves`
- Truth anchor: `D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.rectangle`
- Truth anchor: `D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.result`
- Truth anchor: `D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.rowMoves`
- Truth anchor: `D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.staircase`
- Truth anchor: `D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.youngLE`
