# Kurkov's Alternating Binary Run Count

## Abstract

Alternating overlapping binary one-block counts give Kurkov's A329320 identity.

The symbols n, k, i, and j are natural numbers, including zero. The operator size(n) is the length of the binary expansion, equal to floor(log_2(n))+1 for positive n and zero at n=0. The Boolean testBit(n,i) is true exactly when bit i is one, with the least significant bit at i=0 and zero bits beyond size(n). The function cn(n,k) counts occurrences of the block of k ones; overlapping occurrences have distinct starting indices and all count. The operator v_2(m) is the exponent of two dividing positive m, and Odd(r) means r=2q+1 for some natural q. The function b(n) counts suffixes whose shifted value plus one has odd v_2. Vertical bars denote finite-set cardinality. The operator div is natural-number floor division, and (x:Z) is the natural-to-integer coercion. Indices, valuations, and exponents are natural; the alternating sum and both subtractions in the theorem are integer operations. Only Kurkov's October 13, 2021 formula in A239907 is settled here, using the cited valuation interpretation of A329320.

**Definition 1.1 (Overlapping occurrences of a block of ones).**

$$\forall n \in \mathbb{N}, k \in \mathbb{N},\; \operatorname{cn}\left(n, k\right) = \left|\left\{i \in \mathbb{N} \mid (i < \operatorname{size}\left(n\right)) \land (\forall j \in \mathbb{N},\; (j < k) \Rightarrow (\operatorname{testBit}\left(n, i + j\right) = \operatorname{true}))\right\}\right|$$

*Formalization.* `D5/S1/Digit/KurkovRunAlternatingCount.cn` (`✓ std3`).

*Citation.* N. J. A. Sloane; Mikhail Kurkov (2021). *OEIS A239907, alternating count of runs of ones, with Kurkov's A329320 identity*. URL: <https://oeis.org/A239907>.

*Commentary.*

For positive k the predicate tests every bit in the block beginning at i. Reversing the binary word preserves occurrences of a block of ones. For example cn(7,2)=2, which gives the overlapping reading required by A239907. The value cn(n,0)=size(n) is a totalization excluded from the alternating sum.

**Definition 1.2 (A329320 in valuation coordinates).**

$$\forall n \in \mathbb{N},\; \operatorname{b}\left(n\right) = \left|\left\{i \in \mathbb{N} \mid (i < \operatorname{size}\left(n\right)) \land (\operatorname{Odd}\left(\left(\operatorname{v}_{2}\right)\left(\operatorname{div}\left(n, 2^{i}\right) + 1\right)\right))\right\}\right|$$

*Formalization.* `D5/S1/Digit/KurkovRunAlternatingCount.b` (`✓ std3`).

*Citation.* N. J. A. Sloane; Mikhail Kurkov (2021). *OEIS A239907, alternating count of runs of ones, with Kurkov's A329320 identity*. URL: <https://oeis.org/A239907>.

*Commentary.*

For positive m the cited characterization is 1-A035263(m)=[v_2(m) odd], where brackets denote the zero-or-one indicator. Thus this cardinality is the sum in the NAME of A329320. Every argument div(n,2^i)+1 is positive. The range is empty at zero, so b(0)=0. The morphic definition of A035263 is not separately formalized by this statement.

**Theorem 1.3 (Kurkov's identity).**

$$\forall n \in \mathbb{N},\; (n: \mathbb{Z}) - \sum_{k = 1}^{\operatorname{size}\left(n\right)} (-1: \mathbb{Z})^{k + 1} \cdot (\operatorname{cn}\left(n, k\right): \mathbb{Z}) = (n: \mathbb{Z}) - (\operatorname{b}\left(n\right): \mathbb{Z})$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/KurkovRunAlternatingCount.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a239907-kurkov-run-alternating-count` (proved) by `D5/S1/Digit/KurkovRunAlternatingCount.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a239907-kurkov-run-alternating-count","declaration_gid":"D5/S1/Digit/KurkovRunAlternatingCount.result","resolution_kind":"proved"} -->

*Citation.* N. J. A. Sloane; Mikhail Kurkov (2021). *OEIS A239907, alternating count of runs of ones, with Kurkov's A329320 identity*. URL: <https://oeis.org/A239907>.

*Commentary.*

A block of k ones starting at i exists exactly when 2^k divides div(n,2^i)+1, equivalently when k is at most its v_2. This valuation is at most size(n) for each counted start. Interchanging the two finite sums reduces the alternating count at that start to one for an odd valuation and zero for an even valuation. Their sum is b(n). Both ranges are empty at n=0, and the equality then reads 0=0.

## References

- Truth anchor: `D5/S1/Digit/KurkovRunAlternatingCount.b`
- Truth anchor: `D5/S1/Digit/KurkovRunAlternatingCount.cn`
- Truth anchor: `D5/S1/Digit/KurkovRunAlternatingCount.result`
