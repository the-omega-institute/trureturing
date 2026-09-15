# Barry's A105595 row-sum conjecture

## Abstract

Every row sum of the A105594 triangle is odd.

**Definition 1.1 (The A105594 triangle entry).**

$$\forall n \in \mathbb{N}, k \in \mathbb{N},\; \operatorname{rowEntry}\left(n, k\right) = (\sum_{j = 0}^{n} \left|\mu(\operatorname{binomial}\left(n, j\right))\right| \cdot (\operatorname{binomial}\left(j, k\right) \bmod 2)) \bmod 2$$

*Formalization.* `D5/S3/ArithSums/BarryTriangleRowSumsOdd.rowEntry` (`✓ std3`).

*Citation.* Paul Barry (2005). *OEIS A105595, Row sums of number triangle A105594*. URL: <https://oeis.org/A105595>.

*Commentary.*

For fixed n and k, sum over j from zero through n the absolute Moebius value of binomial(n,j), multiplied by the parity of binomial(j,k), and reduce the resulting inner sum modulo two.

**Definition 1.2 (The A105595 row sum).**

$$\forall n \in \mathbb{N},\; \operatorname{rowSum}\left(n\right) = \sum_{k = 0}^{n} \operatorname{rowEntry}\left(n, k\right)$$

*Formalization.* `D5/S3/ArithSums/BarryTriangleRowSumsOdd.rowSum` (`✓ std3`).

*Citation.* Paul Barry (2005). *OEIS A105595, Row sums of number triangle A105594*. URL: <https://oeis.org/A105595>.

*Commentary.*

The nth term is the sum of rowEntry(n,k) over k from zero through n.

**Theorem 1.3 (Every row sum is odd).**

$$\forall n \in \mathbb{N},\; \operatorname{Odd}\left(\operatorname{rowSum}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/BarryTriangleRowSumsOdd.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a105595-barry-triangle-row-sums-odd` (proved) by `D5/S3/ArithSums/BarryTriangleRowSumsOdd.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a105595-barry-triangle-row-sums-odd","declaration_gid":"D5/S3/ArithSums/BarryTriangleRowSumsOdd.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul Barry (2005). *OEIS A105595, Row sums of number triangle A105594*. URL: <https://oeis.org/A105595>.

*Commentary.*

Each already reduced inner sum is first cast into integers modulo two, where reduction modulo two preserves its value, and the finite sums may then be interchanged. For a fixed j, the binomial row through n equals two to the power j because terms with k greater than j vanish. Modulo two only j=0 remains, and its coefficient is the absolute Moebius value at one, which equals one.

## References

- Truth anchor: `D5/S3/ArithSums/BarryTriangleRowSumsOdd.result`
- Truth anchor: `D5/S3/ArithSums/BarryTriangleRowSumsOdd.rowEntry`
- Truth anchor: `D5/S3/ArithSums/BarryTriangleRowSumsOdd.rowSum`
