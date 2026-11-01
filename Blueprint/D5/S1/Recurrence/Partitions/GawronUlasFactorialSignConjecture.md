# Factorial Partition Signs: Conjecture 4.4 is False

## Abstract

Factorial partition signs fail on an unbounded even progression.

**Definition 1.1 (A partition with prescribed multiplicities).**

$$\forall n \in \mathrm{Nat},\; \forall y \in \mathrm{Nat},\; \forall z \in \mathrm{Nat},\; \forall (h: 2 \cdot y + 6 \cdot z \le n), (\operatorname{partition126}\left(n, y, z, h\right) = \operatorname{Nat}.\operatorname{Partition}.\operatorname{ofSums}\left(n, \operatorname{Multiset}.\operatorname{replicate}\left(n - 2 \cdot y - 6 \cdot z, 1\right) + \operatorname{Multiset}.\operatorname{replicate}\left(y, 2\right) + \operatorname{Multiset}.\operatorname{replicate}\left(z, 6\right)\right))$$

*Formalization.* `D5/S1/Recurrence/Partitions/GawronUlasFactorialSignConjecture.partition126` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural n, y and z with 2y+6z ≤ n, partition126 uses n−2y−6z ones, y twos and z sixes, whose total is n; the proof argument h supplies this inequality and the sum proof passed to ofSums is omitted from the formula.

**Lemma 1.2 (Parts of the prescribed partition).**

$$\forall n \in \mathrm{Nat},\; \forall y \in \mathrm{Nat},\; \forall z \in \mathrm{Nat},\; \forall (h: 2 \cdot y + 6 \cdot z \le n), (\operatorname{Nat}.\operatorname{Partition}.\operatorname{parts}\left(\operatorname{partition126}\left(n, y, z, h\right)\right) = \operatorname{Multiset}.\operatorname{replicate}\left(n - 2 \cdot y - 6 \cdot z, 1\right) + \operatorname{Multiset}.\operatorname{replicate}\left(y, 2\right) + \operatorname{Multiset}.\operatorname{replicate}\left(z, 6\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/GawronUlasFactorialSignConjecture.partition126_parts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every admissible proof argument h, the parts of partition126 are exactly the prescribed multiset of ones, twos and sixes.

The statements are from arXiv:2202.05221v1. The integers n and k are nonnegative. Nat.Partition n represents unordered partitions into positive parts, including the empty partition of zero. The integer power at exponent zero is one, including 0^0. Nat.div denotes natural-number division, so Nat.div(n+1,2) is the floor of (n+1)/2. Each threshold N may depend on m and k.

**Definition 1.3 (Partitions with a specified number of parts).**

$$\forall A \in \operatorname{Set}\left(\mathrm{Nat}\right),\; \forall i \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; \operatorname{c}\left(A, i, n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((p:\operatorname{Nat}.\operatorname{Partition}\left(n\right) \mapsto (\forall a \in \mathrm{Nat},\; (a \in \operatorname{Nat}.\operatorname{Partition}.\operatorname{parts}\left(p\right)) \Rightarrow (a \in A)) \land (\operatorname{Multiset}.\operatorname{card}\left(\operatorname{Nat}.\operatorname{Partition}.\operatorname{parts}\left(p\right)\right) = i)), (\operatorname{Finset}.\operatorname{univ}:\operatorname{Finset}\left(\operatorname{Nat}.\operatorname{Partition}\left(n\right)\right))\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Partitions/GawronUlasFactorialSignConjecture.c` (`✓ std3`).

*Citation.* Filip Gawron and Maciej Ulas (2022). *Signs behaviour of sums of weighted numbers of partitions*. DOI: [10.1007/s11139-022-00602-3](https://doi.org/10.1007/s11139-022-00602-3). URL: <https://arxiv.org/abs/2202.05221v1>.

*Commentary.*

Pages 1–2: "Let A ⊂ N+ be given and take n ∈ N. By an A-partition λ = (λ_1, . . . , λ_k) with parts in A, of a non-negative integer n, we mean a representation of n in the form n = λ_1 + . . . + λ_k, where λ_i ∈ A. The representations of n differing only in order of the terms are counted as one." "c_A(i, n) is the number of A-partitions of n with exactly i parts." The filter tests membership of every part in A and equality of the part count with i. Allowing zero in the carrier of A changes no partition, because every part of Nat.Partition n is positive.

**Definition 1.4 (The signed weighted partition sum).**

$$\forall A \in \operatorname{Set}\left(\mathrm{Nat}\right),\; \forall k \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; \operatorname{S}\left(A, k, n\right) = \sum_{i \in \operatorname{Finset}.\operatorname{range}\left(n + 1\right)}((-1:\mathbb{Z})^{i} \cdot (i:\mathbb{Z})^{k} \cdot (\operatorname{c}\left(A, i, n\right):\mathbb{Z}))$$

*Formalization.* `D5/S1/Recurrence/Partitions/GawronUlasFactorialSignConjecture.S` (`✓ std3`).

*Citation.* Filip Gawron and Maciej Ulas (2022). *Signs behaviour of sums of weighted numbers of partitions*. DOI: [10.1007/s11139-022-00602-3](https://doi.org/10.1007/s11139-022-00602-3). URL: <https://arxiv.org/abs/2202.05221v1>.

*Commentary.*

Page 2: "S_{A,k}(n) = Σ_{i=0}^{n} (−1)^i i^k c_A(i, n)". The range includes both endpoints 0 and n. The powers and products are in the integers; the counts are cast from the natural numbers.

**Definition 1.5 (The factorial part set).**

$$\forall m \in \mathrm{Nat},\; \operatorname{U}\left(m\right) = \{a:\mathrm{Nat}|\exists i \in \mathrm{Nat},\; (1 \le i) \land ((i \le m) \land (a = \operatorname{Nat}.\operatorname{factorial}\left(i\right)))\}$$

*Formalization.* `D5/S1/Recurrence/Partitions/GawronUlasFactorialSignConjecture.U` (`✓ std3`).

*Citation.* Filip Gawron and Maciej Ulas (2022). *Signs behaviour of sums of weighted numbers of partitions*. DOI: [10.1007/s11139-022-00602-3](https://doi.org/10.1007/s11139-022-00602-3). URL: <https://arxiv.org/abs/2202.05221v1>.

*Commentary.*

Page 11: "Let m ∈ N≥2 and take U_m = {i! : i = 1, . . . , m}." Set membership identifies repeated values. In particular U 3 is {1,2,6}.

**Definition 1.6 (Both assertions of Conjecture 4.4).**

$$claim \Leftrightarrow (\forall m \in \mathrm{Nat},\; (2 \le m) \Rightarrow ((\forall k \in \mathrm{Nat},\; (k \le m - 2) \Rightarrow (\exists N \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; (N \le n) \Rightarrow (0 \le (-1:\mathbb{Z})^{\operatorname{Nat}.\operatorname{div}\left(n + 1, 2\right)} \cdot \operatorname{S}\left(\operatorname{U}\left(m\right), k, n\right)))) \land (\forall k \in \mathrm{Nat},\; (m - 1 \le k) \Rightarrow (\exists N \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; (N \le n) \Rightarrow (0 \le (-1:\mathbb{Z})^{n} \cdot \operatorname{S}\left(\operatorname{U}\left(m\right), k, n\right))))))$$

*Formalization.* `D5/S1/Recurrence/Partitions/GawronUlasFactorialSignConjecture.claim` (`✓ std3`).

*Citation.* Filip Gawron and Maciej Ulas (2022). *Signs behaviour of sums of weighted numbers of partitions*. DOI: [10.1007/s11139-022-00602-3](https://doi.org/10.1007/s11139-022-00602-3). URL: <https://arxiv.org/abs/2202.05221v1>.

*Commentary.*

Conjecture 4.4 (p. 11): "Let m ∈ N≥2 and take U_m = {i! : i = 1, . . . , m}. Then, for each k ∈ {0, . . . , m − 2}, (−1)^⌊(n+1)/2⌋ S_{U_m,k}(n) ≥ 0 for n ≫ 0, i.e., the sequence of signs of the sequence (S_{U_m,k}(n))_{n∈N} is eventually periodic of period 4. Moreover, if k ≥ m − 1 then (−1)^n S_{U_m,k}(n) ≥ 0 for n ≫ 0." The two assertions are conjoined. The expression n ≫ 0 means that there exists a threshold N such that every n ≥ N satisfies the inequality. The floor in the first assertion is Nat.div.

**Theorem 1.7 (The eventual alternating sign fails).**

$$\neg (\forall m \in \mathrm{Nat},\; (2 \le m) \Rightarrow ((\forall k \in \mathrm{Nat},\; (k \le m - 2) \Rightarrow (\exists N \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; (N \le n) \Rightarrow (0 \le (-1:\mathbb{Z})^{\operatorname{Nat}.\operatorname{div}\left(n + 1, 2\right)} \cdot \operatorname{S}\left(\operatorname{U}\left(m\right), k, n\right)))) \land (\forall k \in \mathrm{Nat},\; (m - 1 \le k) \Rightarrow (\exists N \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; (N \le n) \Rightarrow (0 \le (-1:\mathbb{Z})^{n} \cdot \operatorname{S}\left(\operatorname{U}\left(m\right), k, n\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/GawronUlasFactorialSignConjecture.result` (`✓ std3`). ∎

*Resolves.* `Problems/gawron-ulas-2022-factorial-sign-conjecture-4-4` (refuted) by `D5/S1/Recurrence/Partitions/GawronUlasFactorialSignConjecture.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gawron-ulas-2022-factorial-sign-conjecture-4-4","declaration_gid":"D5/S1/Recurrence/Partitions/GawronUlasFactorialSignConjecture.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Filip Gawron and Maciej Ulas (2022). *Signs behaviour of sums of weighted numbers of partitions*. DOI: [10.1007/s11139-022-00602-3](https://doi.org/10.1007/s11139-022-00602-3). URL: <https://arxiv.org/abs/2202.05221v1>.

*Commentary.*

For U 3 = {1,2,6} and k=2, multiplicities of 2 and 6 parametrize the partitions. Alternating quadratic sums and the ordinary power-sum formula give 3 S(U 3,2,12r+2) = −52r³+69r²+82r+9 for every natural r. Taking r=s+3 gives S(U 3,2,12s+38)<0 for every natural s. These arguments are even and exceed any proposed threshold, contradicting the second assertion. The first assertion and the signs for other k are not decided here.

## References

- Truth anchor: `D5/S1/Recurrence/Partitions/GawronUlasFactorialSignConjecture.S`
- Truth anchor: `D5/S1/Recurrence/Partitions/GawronUlasFactorialSignConjecture.U`
- Truth anchor: `D5/S1/Recurrence/Partitions/GawronUlasFactorialSignConjecture.c`
- Truth anchor: `D5/S1/Recurrence/Partitions/GawronUlasFactorialSignConjecture.claim`
- Truth anchor: `D5/S1/Recurrence/Partitions/GawronUlasFactorialSignConjecture.partition126`
- Truth anchor: `D5/S1/Recurrence/Partitions/GawronUlasFactorialSignConjecture.partition126_parts`
- Truth anchor: `D5/S1/Recurrence/Partitions/GawronUlasFactorialSignConjecture.result`
