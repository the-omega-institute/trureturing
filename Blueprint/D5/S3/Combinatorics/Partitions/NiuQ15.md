# Niu Question 15 for Rectangular Tableaux

## Abstract

Exact uniform first-descent probabilities and the limiting law for every rectangular row count at least two.

**Definition 1.1 (Uniform event probability).**

$$\operatorname{eventProbability}\left(event\right) = \frac{\operatorname{cast}\left(\operatorname{Nat}.\operatorname{card}\left(\left\{t:\alpha \mid event\left(t\right)\right\}\right)\right)}{\operatorname{cast}\left(\operatorname{Fintype}.\operatorname{card}\left(\alpha\right)\right)}$$

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15.eventProbability` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

Here α is any finite type and event is a predicate on α. The casts take the two cardinalities to the real numbers.

**Definition 1.2 (Rectangle descent).**

$$\operatorname{rectangleDescent}\left(k, n, t\right) = if hn: 0 < n then \operatorname{firstDescent}\left(hn, t\right) else 0$$

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15.rectangleDescent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

The shape has k + 2 rows and n columns. The positive-width branch supplies the proof hn of 0 < n. Its value is the one-based second-row first entry minus one.

**Definition 1.3 (Survival probability).**

$$\operatorname{rectangleTailProbability}\left(k, n, r\right) = \operatorname{eventProbability}\left((t: \operatorname{StandardTableau}\left(\operatorname{rectangle}\left(k + 1, n\right)\right) \mapsto r \le \operatorname{rectangleDescent}\left(k, n, t\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15.rectangleTailProbability` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

The event is taken in the uniform sample of tableaux of the rectangle.

**Definition 1.4 (Point probability).**

$$\operatorname{rectanglePointProbability}\left(k, n, r\right) = \operatorname{eventProbability}\left((t: \operatorname{StandardTableau}\left(\operatorname{rectangle}\left(k + 1, n\right)\right) \mapsto \operatorname{rectangleDescent}\left(k, n, t\right) = r)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15.rectanglePointProbability` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

The event fixes the descent at r.

**Definition 1.5 (Odd-entry probability).**

$$\operatorname{rectangleOddEntryProbability}\left(k, n\right) = \operatorname{eventProbability}\left((t: \operatorname{StandardTableau}\left(\operatorname{rectangle}\left(k + 1, n\right)\right) \mapsto \operatorname{Odd}\left(\operatorname{rectangleDescent}\left(k, n, t\right) + 1\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15.rectangleOddEntryProbability` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

At positive width the event is that the one-based entry in row two and column one is odd.

**Theorem 1.6 (Straight-shape cardinality).**

$$\forall k \in \mathbb{N},\; \forall shape \in \operatorname{RowShape}\left(k\right),\; 2 \le k \Rightarrow (\operatorname{cast}\left(\operatorname{Fintype}.\operatorname{card}\left(\operatorname{StandardTableau}\left(shape\right)\right)\right): \mathbb{Q}) = \operatorname{shiftedCount}\left(shape.rows\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15.card_standardTableau_eq_shiftedCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

Both counts equal one at size zero. At positive size they sum over the same removable row ends. Strong induction on the number of cells gives equality.

**Definition 1.7 (Rectangle and shortened-shape count identity).**

$$\forall k \in \mathbb{N},\; \operatorname{ExactRectangleTailCount}\left(k\right) \Leftrightarrow (\forall n \in \mathbb{N},\; \forall r \in \mathbb{N},\; 0 < n \Rightarrow \left(r \le n \Rightarrow \operatorname{Fintype}.\operatorname{card}\left(\operatorname{StandardTableau}\left(\operatorname{rotatedShape}\left(k + 1, n, r\right)\right)\right) \cdot \operatorname{descFactorial}\left((k + 2) \cdot n, r\right) = \operatorname{Fintype}.\operatorname{card}\left(\operatorname{StandardTableau}\left(\operatorname{rectangle}\left(k + 1, n\right)\right)\right) \cdot \operatorname{tailCoefficient}\left(k + 2, r\right) \cdot \operatorname{descFactorial}\left(n, r\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15.ExactRectangleTailCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

Both counts and descending factorials are natural numbers.

**Theorem 1.8 (Exact rectangle tail count).**

$$\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall r \in \mathbb{N},\; 0 < n \Rightarrow \left(r \le n \Rightarrow \operatorname{Fintype}.\operatorname{card}\left(\operatorname{StandardTableau}\left(\operatorname{rotatedShape}\left(k + 1, n, r\right)\right)\right) \cdot \operatorname{descFactorial}\left((k + 2) \cdot n, r\right) = \operatorname{Fintype}.\operatorname{card}\left(\operatorname{StandardTableau}\left(\operatorname{rectangle}\left(k + 1, n\right)\right)\right) \cdot \operatorname{tailCoefficient}\left(k + 2, r\right) \cdot \operatorname{descFactorial}\left(n, r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15.exactRectangleTailCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

The factors involving the bottom row change from 1 through k + 1 to r + 1 through r + k + 1. Their ratio is the binomial coefficient. The size and bottom-row factorials give the two descending factorials.

**Definition 1.9 (The closed Question 15 proposition).**

$$Question15 \Leftrightarrow (\forall k \in \mathbb{N},\; (\forall r \in \mathbb{N},\; \operatorname{Tendsto}\left((n: \mathbb{N} \mapsto \operatorname{rectangleTailProbability}\left(k, n, r\right)), atTop, \operatorname{nhds}\left(\operatorname{limitTail}\left(k + 2, r\right)\right)\right)) \land (\forall r \in \mathbb{N},\; \operatorname{Tendsto}\left((n: \mathbb{N} \mapsto \operatorname{rectanglePointProbability}\left(k, n, r\right)), atTop, \operatorname{nhds}\left(\operatorname{limitMass}\left(k + 2, r\right)\right)\right)) \land (\operatorname{HasSum}\left(\operatorname{limitMass}\left(k + 2\right), 1\right)) \land (\operatorname{Tendsto}\left(\operatorname{rectangleOddEntryProbability}\left(k\right), atTop, \operatorname{nhds}\left((\frac{\operatorname{cast}\left(k\right) + 2}{\operatorname{cast}\left(k\right) + 3})^{k + 2}\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15.Question15` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

The two distribution clauses quantify independently over natural thresholds. At r = 0 the limiting point mass is zero, so summing over all natural r gives the same normalization as summing over positive r.

**Theorem 1.10 (First-descent law and odd-entry limit).**

$$\forall k \in \mathbb{N},\; (\forall r \in \mathbb{N},\; \operatorname{Tendsto}\left((n: \mathbb{N} \mapsto \operatorname{rectangleTailProbability}\left(k, n, r\right)), atTop, \operatorname{nhds}\left(\operatorname{limitTail}\left(k + 2, r\right)\right)\right)) \land (\forall r \in \mathbb{N},\; \operatorname{Tendsto}\left((n: \mathbb{N} \mapsto \operatorname{rectanglePointProbability}\left(k, n, r\right)), atTop, \operatorname{nhds}\left(\operatorname{limitMass}\left(k + 2, r\right)\right)\right)) \land (\operatorname{HasSum}\left(\operatorname{limitMass}\left(k + 2\right), 1\right)) \land (\operatorname{Tendsto}\left(\operatorname{rectangleOddEntryProbability}\left(k\right), atTop, \operatorname{nhds}\left((\frac{\operatorname{cast}\left(k\right) + 2}{\operatorname{cast}\left(k\right) + 3})^{k + 2}\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15.rectangleQuestion15` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tong Niu (2026). *The first descent in a standard Young tableau of shape (n,n,n)*. DOI: [10.48550/arXiv.2610.03038](https://doi.org/10.48550/arXiv.2610.03038). URL: <https://arxiv.org/abs/2610.03038v1>.

*Commentary.*

For K = k + 2 the survival limit is choose(r + K − 1, K − 1)/K^r, and the point limit is r choose(r + K − 1, K − 2)/K^(r + 1). The masses sum to one. Prefix rotation and the count identity give the finite tails. Their adjacent differences give the masses. A common summable bound permits the limit in the alternating parity sum.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15.ExactRectangleTailCount`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15.Question15`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15.card_standardTableau_eq_shiftedCount`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15.eventProbability`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15.exactRectangleTailCount`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15.rectangleDescent`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15.rectangleOddEntryProbability`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15.rectanglePointProbability`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15.rectangleQuestion15`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15.rectangleTailProbability`
- Dependency: [D5/S3/Combinatorics/Partitions/NiuQ15Analytic](NiuQ15Analytic.md)
- Dependency: [D5/S3/Combinatorics/Partitions/NiuQ15Tableaux](NiuQ15Tableaux.md)
- Dependency: [D5/S3/Combinatorics/Partitions/NiuTableauCount](NiuTableauCount.md)
