# Threshold counts in overpartitions

## Abstract

A finite identity relates the full threshold statistic on native overpartitions to total and nonoverlined part counts.

Nat denotes the nonnegative integers and Int the integers. An ordinary partition is a multiset of positive integers with sum n. Its support contains its distinct part sizes. Each subset S of that support selects the sizes whose first occurrence is overlined, independently, so every legal marking pattern occurs exactly once. The functions parts and marks below select these two components; indicator is one when its proposition holds and zero otherwise. Every displayed sum and cardinal is finite.

**Definition 1.1 (The native marked carrier).**

$$\forall n \in Nat,\; \forall p \in \operatorname{Partition}\left(n\right),\; \forall S \in \operatorname{Finset}\left(Nat\right),\; \operatorname{pair}\left(p, S\right) \in \operatorname{Overpartition}\left(n\right) \Leftrightarrow \operatorname{subset}\left(S, \operatorname{support}\left(p\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/OverpartitionThreshold.Overpartition` (`✓ std3`).

*Citation.* Subhash Chand Bhoria, Pramod Eyyunni, Subhrangsu Santra (2026). *On the number of missing integers in partitions*. DOI: [10.48550/arXiv.2604.12557](https://doi.org/10.48550/arXiv.2604.12557). URL: <https://arxiv.org/abs/2604.12557v1>.

*Commentary.*

Membership of a pair is shorthand for the dependent pair of an ordinary partition and a subset of its support. There are no additional marking constraints.

**Definition 1.2 (Multiplicity includes the mark).**

$$\forall n \in Nat,\; \forall o \in \operatorname{Overpartition}\left(n\right),\; \forall r \in Nat,\; \operatorname{multiplicity}\left(o, r\right) = \operatorname{count}\left(r, \operatorname{parts}\left(o\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/OverpartitionThreshold.multiplicity` (`✓ std3`).

*Citation.* Subhash Chand Bhoria, Pramod Eyyunni, Subhrangsu Santra (2026). *On the number of missing integers in partitions*. DOI: [10.48550/arXiv.2604.12557](https://doi.org/10.48550/arXiv.2604.12557). URL: <https://arxiv.org/abs/2604.12557v1>.

*Commentary.*

count counts all occurrences in the underlying multiset. Overlining changes none of these counts.

**Definition 1.3 (Largest part).**

$$\forall n \in Nat,\; \forall o \in \operatorname{Overpartition}\left(n\right),\; \operatorname{largest}\left(o\right) = \operatorname{sup}\left(\operatorname{support}\left(\operatorname{parts}\left(o\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/OverpartitionThreshold.largest` (`✓ std3`).

*Citation.* Subhash Chand Bhoria, Pramod Eyyunni, Subhrangsu Santra (2026). *On the number of missing integers in partitions*. DOI: [10.48550/arXiv.2604.12557](https://doi.org/10.48550/arXiv.2604.12557). URL: <https://arxiv.org/abs/2604.12557v1>.

*Commentary.*

sup is the maximum of the finite support, with value zero on the empty support.

**Definition 1.4 (The full threshold statistic).**

$$\forall k \in Nat,\; \forall n \in Nat,\; \operatorname{U}\left(k, n\right) = \sum_{o \in \operatorname{Overpartition}\left(n\right)}(\sum_{r \in \operatorname{Icc}\left(1, \operatorname{largest}\left(o\right)\right)}(\operatorname{indicator}\left(\operatorname{multiplicity}\left(o, r\right) < k\right)))$$

*Formalization.* `D5/S3/Combinatorics/Partitions/OverpartitionThreshold.U` (`✓ std3`).

*Citation.* Subhash Chand Bhoria, Pramod Eyyunni, Subhrangsu Santra (2026). *On the number of missing integers in partitions*. DOI: [10.48550/arXiv.2604.12557](https://doi.org/10.48550/arXiv.2604.12557). URL: <https://arxiv.org/abs/2604.12557v1>.

*Commentary.*

The interval is closed and begins at one. Missing sizes have multiplicity zero, so they are counted whenever k is positive. For n equal to zero the interval is empty.

**Definition 1.5 (Total parts).**

$$\forall n \in Nat,\; \operatorname{T}\left(n\right) = \sum_{o \in \operatorname{Overpartition}\left(n\right)}(\operatorname{card}\left(\operatorname{parts}\left(o\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Partitions/OverpartitionThreshold.T` (`✓ std3`).

*Citation.* Hartosh Singh Bal, Gaurav Bhatnagar (2021). *Stanley–Elder–Fine theorems for colored partitions*. DOI: [10.48550/arXiv.2102.03486](https://doi.org/10.48550/arXiv.2102.03486). URL: <https://arxiv.org/abs/2102.03486v2>.

*Commentary.*

card(parts(o)) is the number of all occurrences, including marked ones; equivalently it is the sum of their multiplicities over positive sizes.

**Definition 1.6 (Nonoverlined occurrences).**

$$\forall j \in Nat,\; \forall n \in Nat,\; \operatorname{N}\left(j, n\right) = \sum_{o \in \operatorname{Overpartition}\left(n\right)}(\operatorname{multiplicity}\left(o, j\right) - \operatorname{indicator}\left(j \in \operatorname{marks}\left(o\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Partitions/OverpartitionThreshold.N` (`✓ std3`).

*Citation.* Hartosh Singh Bal, Gaurav Bhatnagar (2021). *Stanley–Elder–Fine theorems for colored partitions*. DOI: [10.48550/arXiv.2102.03486](https://doi.org/10.48550/arXiv.2102.03486). URL: <https://arxiv.org/abs/2102.03486v2>.

*Commentary.*

A selected size contributes exactly one overlined occurrence. Subtracting its indicator leaves the actual nonoverlined occurrences.

**Theorem 1.7 (The uniform finite identity).**

$$\forall k \in Nat,\; \forall n \in Nat,\; 1 \le k \Rightarrow \operatorname{U}\left(k, n\right) = \operatorname{T}\left(n\right) - 2 \cdot \sum_{j \in \operatorname{Icc}\left(k, n\right)}((-1)^{j - k} \cdot \operatorname{N}\left(j, n\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/OverpartitionThreshold.result` (`✓ std3`). ∎

*Resolves.* `Problems/bhoria-eyyunni-santra-2026-overpartition-threshold-identity` (proved) by `D5/S3/Combinatorics/Partitions/OverpartitionThreshold.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bhoria-eyyunni-santra-2026-overpartition-threshold-identity","declaration_gid":"D5/S3/Combinatorics/Partitions/OverpartitionThreshold.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Subhash Chand Bhoria, Pramod Eyyunni, Subhrangsu Santra (2026). *On the number of missing integers in partitions*. DOI: [10.48550/arXiv.2604.12557](https://doi.org/10.48550/arXiv.2604.12557). URL: <https://arxiv.org/abs/2604.12557v1>.

*Acknowledgement.* Joselyne Aniceto, Cristina Ballantine (2026). *Identities involving the number of missing integers in partitions - combinatorial proofs*. DOI: [10.48550/arXiv.2608.00278](https://doi.org/10.48550/arXiv.2608.00278). URL: <https://arxiv.org/abs/2608.00278v1>.

*Acknowledgement.* Hartosh Singh Bal, Gaurav Bhatnagar (2021). *Stanley–Elder–Fine theorems for colored partitions*. DOI: [10.48550/arXiv.2102.03486](https://doi.org/10.48550/arXiv.2102.03486). URL: <https://arxiv.org/abs/2102.03486v2>.

*Commentary.*

For every positive k and every nonnegative n the equality is in Int. The alternating sum is empty for k greater than n. Ordinary Ferrers conjugation preserves the number of distinct sizes, so its reindexing preserves the number of marking subsets and exchanges the largest-part total with the total number of parts. Removing k copies of one positive size gives the threshold recurrence. Toggling the optional mark and removing a nonoverlined occurrence give the frequency recurrence; finite alternating cancellation and the pointwise complementary count yield the displayed equality. The overpartition decomposition, nonoverlined frequency formula and threshold-one and threshold-three ingredients have earlier literature precedents. The cited Question 3 asks for a concise analogue, and the later Conclusion retains that question; neither source asserts this particular formula.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/OverpartitionThreshold.N`
- Truth anchor: `D5/S3/Combinatorics/Partitions/OverpartitionThreshold.Overpartition`
- Truth anchor: `D5/S3/Combinatorics/Partitions/OverpartitionThreshold.T`
- Truth anchor: `D5/S3/Combinatorics/Partitions/OverpartitionThreshold.U`
- Truth anchor: `D5/S3/Combinatorics/Partitions/OverpartitionThreshold.largest`
- Truth anchor: `D5/S3/Combinatorics/Partitions/OverpartitionThreshold.multiplicity`
- Truth anchor: `D5/S3/Combinatorics/Partitions/OverpartitionThreshold.result`
- Dependency: [D5/S1/Words/Compositions/StrictFirstSumsGapfreeOddParts](../../../S1/Words/Compositions/StrictFirstSumsGapfreeOddParts.md)
