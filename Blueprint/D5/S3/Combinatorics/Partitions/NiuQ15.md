# Niu Question 15 for Rectangular Tableaux

## Abstract

Exact uniform first-descent probabilities and the limiting law for every rectangular row count at least two.

**Definition 1.1 (Uniform event probability).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuQ15.eventProbability`

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15.eventProbability` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

The probability of an event on the finite sample is the number of tableaux in the event divided by the number of tableaux in the sample.

**Definition 1.2 (Rectangle descent).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuQ15.rectangleDescent`

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15.rectangleDescent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

The rectangle has K = k + 2 rows. For positive width the descent is the one-based second-row first entry minus one. At width zero the descent is extended by zero.

**Definition 1.3 (Survival probability).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuQ15.rectangleTailProbability`

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15.rectangleTailProbability` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

At k, n and r, the uniform event is that the rectangle descent is at least r.

**Definition 1.4 (Point probability).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuQ15.rectanglePointProbability`

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15.rectanglePointProbability` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

At k, n and r, the uniform event is that the rectangle descent equals r.

**Definition 1.5 (Odd-entry probability).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuQ15.rectangleOddEntryProbability`

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15.rectangleOddEntryProbability` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

At positive width, the event is that the one-based entry in row two and column one is odd, equivalently that the descent is even.

**Theorem 1.6 (Straight-shape cardinality).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuQ15.card_standardTableau_eq_shiftedCount`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15.card_standardTableau_eq_shiftedCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

For any weakly decreasing profile with at least two row slots, the rational cast of the tableau count equals the shifted Vandermonde formula. Both counts equal one at size zero. At positive size, they sum over the same removable row ends with the same shortened profiles. Strong induction on the number of cells gives equality.

**Definition 1.7 (Rectangle and shortened-shape count identity).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuQ15.ExactRectangleTailCount`

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15.ExactRectangleTailCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

For K = k + 2, positive width n and r at most n, the shortened-shape count times the descending factorial of K n of length r equals the rectangle count times choose(r + K - 1, K - 1) times the descending factorial of n of length r.

**Theorem 1.8 (Exact rectangle tail count).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuQ15.exactRectangleTailCount`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15.exactRectangleTailCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

The identity holds for every k. In the shifted Vandermonde product the upper-row factors are common. The factors involving the last row change from the integers 1 through K - 1 to the integers r + 1 through r + K - 1. Their ratio is the binomial coefficient. The size and last-row factorials give the two descending factorials.

**Theorem 1.9 (Exact survival probability).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuQ15.rectangleTailProbability_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15.rectangleTailProbability_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

At every positive width, the survival probability equals the finite survival function. For r at most n this follows from the count ratio and the prefix rotation. For r above n the event is empty.

**Theorem 1.10 (Exact point probability).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuQ15.rectanglePointProbability_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15.rectanglePointProbability_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

At positive width, the point probability for r at most n is the survival probability times (K - 1) r (n + 1) / ((r + 1)(K n - r)). Above the width the point probability is zero.

**Theorem 1.11 (First-descent law and odd-entry limit).**

Lean statement: `D5/S3/Combinatorics/Partitions/NiuQ15.rectangleQuestion15`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15.rectangleQuestion15` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

For every K = k + 2 and each natural r, the survival probability tends to choose(r + K - 1, K - 1)/K^r and the point probability tends to r choose(r + K - 1, K - 2)/K^(r + 1). The limiting point masses sum to one. The probability of an odd second-row first entry tends to (K/(K + 1))^K. Prefix rotation and the count identity give the finite tails, and subtraction of adjacent tails gives the masses. Pairing adjacent tails and applying the common summable bound gives the parity limit.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15.ExactRectangleTailCount`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15.card_standardTableau_eq_shiftedCount`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15.eventProbability`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15.exactRectangleTailCount`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15.rectangleDescent`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15.rectangleOddEntryProbability`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15.rectanglePointProbability`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15.rectanglePointProbability_eq`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15.rectangleQuestion15`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15.rectangleTailProbability`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15.rectangleTailProbability_eq`
- Dependency: [D5/S3/Combinatorics/Partitions/NiuQ15Analytic](NiuQ15Analytic.md)
- Dependency: [D5/S3/Combinatorics/Partitions/NiuQ15Tableaux](NiuQ15Tableaux.md)
- Dependency: [D5/S3/Combinatorics/Partitions/NiuTableauCount](NiuTableauCount.md)
