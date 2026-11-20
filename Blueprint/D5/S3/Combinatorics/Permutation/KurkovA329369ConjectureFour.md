# OEIS A329369 Conjecture 4

## Abstract

Kurkov's signed factorial-power formula for the exact strict-excedance count.

**Definition 1.1 (The prescribed excedance set).**

$$\forall w, n \in \mathbb{N}, \operatorname{binaryExcedances}\left(w, n\right) = \{ j: \operatorname{Fin}\left(w+1\right) \mid \operatorname{val}\left(j\right) < w \land \operatorname{testBit}\left(n, w-1-\operatorname{val}\left(j\right)\right) = \mathrm{true} \}$$

*Formalization.* `D5/S3/Combinatorics/Permutation/KurkovA329369ConjectureFour.binaryExcedances` (`✓ std3`).

*Citation.* OEIS Foundation Inc.; Mikhail Kurkov (2024). *OEIS A329369 sixth conjectured sum over the A373183 rows*. URL: <https://oeis.org/A329369>.

*Commentary.*

The width w counts binary positions. There are w+1 permutation positions, numbered from zero. For j below w, bit w−1−j fixes whether j is a strict excedance. In the one-based OEIS wording, M=w+1 and j+1=M−i, so this is bit i−1. The final position cannot be a strict excedance.

**Definition 1.2 (The number of actual permutations).**

$$\forall w, n \in \mathbb{N}, \operatorname{paddedCount}\left(w, n\right) = \left\lvert\{ p: \operatorname{Perm}\left(\operatorname{Fin}\left(w+1\right)\right) \mid \forall j: \operatorname{Fin}\left(w+1\right), j < \operatorname{p}\left(j\right) \iff j \in \operatorname{binaryExcedances}\left(w, n\right) \}\right\rvert$$

*Formalization.* `D5/S3/Combinatorics/Permutation/KurkovA329369ConjectureFour.paddedCount` (`✓ std3`).

*Citation.* OEIS Foundation Inc.; Mikhail Kurkov (2024). *OEIS A329369 sixth conjectured sum over the A373183 rows*. URL: <https://oeis.org/A329369>.

*Commentary.*

The count is the finite cardinality of the permutations whose complete strict excedance set is the prescribed set. The width is admissible when n<2^w.

**Theorem 1.3 (The signed factorial-power identity).**

$$\forall m, k, w \in \mathbb{N}, 2^{m} \cdot (2 \cdot k+1) < 2^{w} \implies (\operatorname{paddedCount}\left(w, 2^{m} \cdot (2 \cdot k+1)\right): \mathbb{Q}) = \sum_{{1 \le i \le \operatorname{wt}\left(k\right)+2}} (i!: \mathbb{Q}) \cdot (i: \mathbb{Q})^{m} \cdot \operatorname{T}\left(k, i\right) \cdot (-1)^{(\operatorname{wt}\left(k\right): \mathbb{Z})-(i: \mathbb{Z})}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/KurkovA329369ConjectureFour.conjecture4` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a329369-conjecture-four` (proved) by `D5/S3/Combinatorics/Permutation/KurkovA329369ConjectureFour.conjecture4`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a329369-conjecture-four","declaration_gid":"D5/S3/Combinatorics/Permutation/KurkovA329369ConjectureFour.conjecture4","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc.; Mikhail Kurkov (2024). *OEIS A329369 sixth conjectured sum over the A373183 rows*. URL: <https://oeis.org/A329369>.

*Acknowledgement.* Mikhail Kurkov (2024). *OEIS A358612: extended Stirling numbers from binary row indices*. URL: <https://oeis.org/A358612>.

*Acknowledgement.* Richard Ehrenborg; Einar Steingrímsson (2000). *The Excedance Set of a Permutation*. DOI: [10.1006/aama.1999.0671](https://doi.org/10.1006/aama.1999.0671). URL: <https://doi.org/10.1006/aama.1999.0671>.

*Commentary.*

Here wt is the binary popcount and T is the literal rational array A358612, revision 52. Equality is over the rationals and the sign exponent is an integer. The source uses exponent wt(k)−i in A329369 revision 239 and adds two in A358612. These exponents give the same sign, including at the two highest columns.

A prepended zero forces the first position and value to agree, so deleting both preserves the cardinality. The all-zero word consequently has the identity as its unique permutation. A trailing one forces the greatest value at the penultimate position, which gives the odd step by deletion. For a positive even step, apply Ehrenborg and Steingrímsson's adjacent swap and two deletion identity at the lowest one and the next zero. If r is the two-adic valuation of n, the three terms for 2n have indices 2n−2^r, n and n−2^r. Their widths are respectively w+1, w and w when 2n uses width w+1. The guard on each recursive call follows from these indices. Strong induction identifies the count with the row polynomial evaluated at one for every admissible width. The bracket identities are Proposition 2.1 and Lemma 2.3 of The excedance set of a permutation, DOI 10.1006/aama.1999.0671.

The literal A358612 coefficient theorem gives the ascending Pochhammer coordinates of x R(k,x), including the initial row. The index 2k+1 starts at this polynomial. Each doubling multiplies its coordinate in degree i by i, and evaluation at one gives i factorial. The zero-fold iteration covers m=0, and the initial row gives the two terms at k=0.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/KurkovA329369ConjectureFour.binaryExcedances`
- Truth anchor: `D5/S3/Combinatorics/Permutation/KurkovA329369ConjectureFour.conjecture4`
- Truth anchor: `D5/S3/Combinatorics/Permutation/KurkovA329369ConjectureFour.paddedCount`
- Dependency: [D5/S1/Recurrence/Parity/DyadicPochhammerCoefficient](../../../S1/Recurrence/Parity/DyadicPochhammerCoefficient.md)
- Dependency: [D5/S1/Recurrence/Parity/DyadicPowerRowClosedForm](../../../S1/Recurrence/Parity/DyadicPowerRowClosedForm.md)
- Dependency: [D5/S3/Combinatorics/Permutation/AdjacentExcedanceSet](AdjacentExcedanceSet.md)
