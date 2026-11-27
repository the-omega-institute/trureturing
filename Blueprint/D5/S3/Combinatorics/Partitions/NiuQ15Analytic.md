# Limits of the Rectangle Tail and Point Laws

## Abstract

Finite tails, normalized point limits and alternating sums for rectangular tableaux.

**Definition 1.1 (Binomial coefficient).**

$$\operatorname{tailCoefficient}\left(k, r\right) = \operatorname{choose}\left(r + (k - 1), k - 1\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.tailCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inputs and both subtractions are in the natural numbers.

**Definition 1.2 (Finite survival function).**

$$\operatorname{finiteTail}\left(k, n, r\right) = \operatorname{ite}\left(r \le n, \operatorname{cast}\left(\operatorname{tailCoefficient}\left(k, r\right)\right) \cdot \prod_{j \in \operatorname{range}\left(r\right)} \frac{\operatorname{cast}\left(n\right) - \operatorname{cast}\left(j\right)}{\operatorname{cast}\left(k\right) \cdot \operatorname{cast}\left(n\right) - \operatorname{cast}\left(j\right)}, 0\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.finiteTail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product is over j from zero through r − 1, and is one for r = 0. The ratios are in the real numbers.

**Definition 1.3 (Limiting survival function).**

$$\operatorname{limitTail}\left(k, r\right) = \frac{\operatorname{cast}\left(\operatorname{tailCoefficient}\left(k, r\right)\right)}{\operatorname{cast}\left(k\right)^{r}}$$

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.limitTail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the defining product of the cast coefficient and the rth power of the reciprocal of k. Division is the total real division used in Lean.

**Definition 1.4 (Limiting point mass).**

$$\operatorname{limitMass}\left(k, r\right) = \frac{\operatorname{cast}\left(r\right) \cdot \operatorname{cast}\left(\operatorname{choose}\left(r + (k - 1), k - 2\right)\right)}{\operatorname{cast}\left(k\right)^{r + 1}}$$

*Formalization.* `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.limitMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The binomial coefficient is evaluated in the naturals before casting it to the reals.

**Theorem 1.5 (Survival above the width).**

$$\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall r \in \mathbb{N},\; n < r \Rightarrow \operatorname{finiteTail}\left(k, n, r\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.finiteTail_above` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The guard selects the zero branch of finiteTail.

**Theorem 1.6 (Finite survival as a factorial ratio).**

$$\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall r \in \mathbb{N},\; 2 \le k \Rightarrow \left(r \le n \Rightarrow \operatorname{finiteTail}\left(k, n, r\right) = \operatorname{cast}\left(\operatorname{tailCoefficient}\left(k, r\right)\right) \cdot \frac{\operatorname{cast}\left(\operatorname{descFactorial}\left(n, r\right)\right)}{\operatorname{cast}\left(\operatorname{descFactorial}\left(k \cdot n, r\right)\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.finiteTail_eq_descFactorial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both descending factorials are formed in the naturals and then cast to the reals. The formula includes zero width with r = 0.

**Theorem 1.7 (Pointwise convergence of survival probabilities).**

$$\forall k \in \mathbb{N},\; 2 \le k \Rightarrow \left(\forall r \in \mathbb{N},\; \operatorname{Tendsto}\left((n: \mathbb{N} \mapsto \operatorname{finiteTail}\left(k, n, r\right)), atTop, \operatorname{nhds}\left(\operatorname{limitTail}\left(k, r\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.tendsto_finiteTail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For fixed threshold the finite product contains a fixed number of factors, each tending to the reciprocal of k.

**Theorem 1.8 (Convergence of the point masses).**

$$\forall k \in \mathbb{N},\; 2 \le k \Rightarrow \left(\forall point \in \mathbb{N} \to \left(\mathbb{N} \to \mathbb{R}\right),\; (\forall n \in \mathbb{N},\; 0 < n \Rightarrow \left(\forall r \in \mathbb{N},\; \operatorname{finiteTail}\left(k, n, r\right) = point\left(n, r\right) + \operatorname{finiteTail}\left(k, n, r + 1\right)\right)) \Rightarrow \left(\forall r \in \mathbb{N},\; \operatorname{Tendsto}\left((n: \mathbb{N} \mapsto point\left(n, r\right)), atTop, \operatorname{nhds}\left(\operatorname{limitMass}\left(k, r\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.tendsto_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hypothesis supplies the tail partition at each positive width. Subtract adjacent tails, take their limits, and simplify the binomial difference.

**Theorem 1.9 (Normalization of the point masses).**

$$\forall k \in \mathbb{N},\; 2 \le k \Rightarrow \operatorname{HasSum}\left(\operatorname{limitMass}\left(k\right), 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.hasSum_limitMass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adjacent limiting tails telescope from one to zero.

**Theorem 1.10 (Even indices as an alternating tail sum).**

$$\forall k \in \mathbb{N},\; \forall point \in \mathbb{N} \to \left(\mathbb{N} \to \mathbb{R}\right),\; (\forall n \in \mathbb{N},\; 0 < n \Rightarrow \left(\forall r \in \mathbb{N},\; \operatorname{finiteTail}\left(k, n, r\right) = point\left(n, r\right) + \operatorname{finiteTail}\left(k, n, r + 1\right)\right)) \Rightarrow \left(\forall n \in \mathbb{N},\; 0 < n \Rightarrow \sum_{r \in \operatorname{range}\left(n + 1\right)} \operatorname{ite}\left(\operatorname{Even}\left(r\right), point\left(n, r\right), 0\right) = \operatorname{tsum}\left((r: \mathbb{N} \mapsto (-1)^{r} \cdot \operatorname{finiteTail}\left(k, n, r\right))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.sum_even_point_eq_alternating` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pair a tail at each even threshold with the following tail. All tails beyond the width vanish.

**Theorem 1.11 (Limit of the alternating tail sum).**

$$\forall k \in \mathbb{N},\; 2 \le k \Rightarrow \operatorname{Tendsto}\left((n: \mathbb{N} \mapsto \operatorname{tsum}\left((r: \mathbb{N} \mapsto (-1)^{r} \cdot \operatorname{finiteTail}\left(k, n, r\right))\right)), atTop, \operatorname{nhds}\left((\frac{\operatorname{cast}\left(k\right)}{\operatorname{cast}\left(k\right) + 1})^{k}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.tendsto_alternating_finiteTail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A geometric bound independent of k and n gives dominated convergence. The alternating binomial series at −1/k evaluates the limit.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.finiteTail`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.finiteTail_above`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.finiteTail_eq_descFactorial`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.hasSum_limitMass`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.limitMass`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.limitTail`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.sum_even_point_eq_alternating`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.tailCoefficient`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.tendsto_alternating_finiteTail`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.tendsto_finiteTail`
- Truth anchor: `D5/S3/Combinatorics/Partitions/NiuQ15Analytic.tendsto_point`
