# Reflected intervals and tail positivity

## Abstract

Central Catalan-power convolution intervals increase under balancing.

All sums are finite. The coefficient a(n,t) is the rising-factorial quotient, and b(j) is its derivative at zero. Natural subtraction occurs only under the stated finite bounds. The boundary filter also handles empty signed intervals without assigning a spurious term to index zero.

**Definition 1.1 (The uncancelled left boundary).**

$$\forall (m: \mathbb{N}), \forall (q: \mathbb{N}), \forall (j: \mathbb{N}), \operatorname{R}\left(m, q, j\right) = \operatorname{Finset.filter}\left((\lambda (i: \mathbb{N}) \mapsto \left(q \le i + j \land i + j \le m - q\right) \land i < q), \operatorname{Finset.range}\left(m - j + 1\right)\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangCatalanPower/Interval.R` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

R contains exactly the nonnegative integers in [max(0,q-j), min(q-1,m-q-j)], where the upper endpoint is an integer. Its filter presentation retains the condition i+j≤m-q, so the set is empty when the signed upper endpoint is negative.

**Definition 1.2 (The central convolution interval).**

$$\forall (m: \mathbb{N}), \forall (q: \mathbb{N}), \forall (u: \mathbb{R}), \forall (v: \mathbb{R}), \operatorname{Z}\left(m, q, u, v\right) = \sum_{k \in \operatorname{Finset.Icc}\left(q, m - q\right)} (\operatorname{a}\left(k, u\right) \cdot \operatorname{a}\left(m - k, v\right))$$

*Formalization.* `D5/S3/Analytic/KarpZhangCatalanPower/Interval.Z` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Z(m,q,u,v) sums a(k,u)a(m-k,v) for q≤k≤m-q. The two endpoints are included, including a singleton central interval.

**Definition 1.3 (The reflected determinant sum).**

$$\forall (m: \mathbb{N}), \forall (q: \mathbb{N}), \forall (u: \mathbb{R}), \forall (v: \mathbb{R}), \operatorname{sliceDerivative}\left(m, q, u, v\right) = \sum_{j \in \operatorname{Finset.Icc}\left(1, m\right)} (\operatorname{b}\left(j\right) \cdot \sum_{i \in \operatorname{R}\left(m, q, j\right)} (\operatorname{a}\left(i, u\right) \cdot \operatorname{a}\left(m - j - i, v\right) - \operatorname{a}\left(m - j - i, u\right) \cdot \operatorname{a}\left(i, v\right)))$$

*Formalization.* `D5/S3/Analytic/KarpZhangCatalanPower/Interval.sliceDerivative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each j from one through m, multiply b(j) by the sum over R(m,q,j) of the degree-parameter determinants with total degree m-j. This is the derivative of Z along a constant-sum line.

**Theorem 1.4 (Cancellation of two reflected intervals).**

$$\forall (m: \mathbb{N}), \forall (q: \mathbb{N}), \forall (j: \mathbb{N}), (2 \cdot q \le m) \Rightarrow ((j \le m) \Rightarrow (\forall (w: \mathbb{N} \to \mathbb{R}), \sum_{i \in \operatorname{Finset.filter}\left((\lambda (i: \mathbb{N}) \mapsto q \le i + j \land i + j \le m - q), \operatorname{Finset.range}\left(m - j + 1\right)\right)} (\operatorname{w}\left(i\right)) - \sum_{i \in \operatorname{Finset.filter}\left((\lambda (i: \mathbb{N}) \mapsto q \le i \land i \le m - q), \operatorname{Finset.range}\left(m - j + 1\right)\right)} (\operatorname{w}\left(i\right)) = \sum_{i \in \operatorname{R}\left(m, q, j\right)} (\operatorname{w}\left(i\right) - \operatorname{w}\left(m - j - i\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Interval.reflected_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Restrict both intervals to 0≤i≤m-j. Reflection i↦m-j-i exchanges them. The common part cancels, and the remaining terms pair over R. The identity holds for every real-valued weight w, with no sign assumption.

**Theorem 1.5 (The constant-sum slice derivative).**

$$\forall (m: \mathbb{N}), \forall (q: \mathbb{N}), (2 \cdot q \le m) \Rightarrow (\forall (S: \mathbb{R}), \forall (r: \mathbb{R}), (0 < r) \Rightarrow ((0 < S - r) \Rightarrow (\operatorname{HasDerivAt}\left((\lambda (x: \mathbb{R}) \mapsto \operatorname{Z}\left(m, q, x, S - x\right)), \operatorname{sliceDerivative}\left(m, q, r, S - r\right), r\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Interval.hasDerivAt_slice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiate every finite summand. The coefficient derivative identity expands each factor into a lower-degree convolution. Two explicit triangular bijections collect terms with the same j. Reflection then converts their difference into the determinant sum.

**Theorem 1.6 (Reflection symmetry of the interval convolution).**

$$\forall (m: \mathbb{N}), \forall (q: \mathbb{N}), (2 \cdot q \le m) \Rightarrow (\forall (u: \mathbb{R}), \forall (v: \mathbb{R}), \operatorname{Z}\left(m, q, u, v\right) = \operatorname{Z}\left(m, q, v, u\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Interval.Z_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The map k↦m-k permutes the closed central interval and exchanges the two coefficient factors. Balancing can therefore choose the smaller parameter as the first coordinate.

**Theorem 1.7 (Strict increase toward the midpoint).**

$$\forall (m: \mathbb{N}), \forall (q: \mathbb{N}), (1 \le q) \Rightarrow ((2 \cdot q \le m) \Rightarrow (\forall (S: \mathbb{R}), (0 < S) \Rightarrow (\operatorname{StrictMonoOn}\left((\lambda (x: \mathbb{R}) \mapsto \operatorname{Z}\left(m, q, x, S - x\right)), \operatorname{Set.Ioc}\left(0, \frac{S}{2}\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Interval.slice_strictMonoOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the open left half of a positive constant-sum slice, every determinant is positive whenever its boundary set is nonempty. Every b(j) is positive. The j=1 boundary contains q-1, and its two degrees are strictly ordered, so the derivative is strictly positive. The mean-value theorem gives strict increase on (0,S/2], including comparisons with the midpoint.

**Theorem 1.8 (Every shifted central tail is nonnegative).**

$$\forall (m: \mathbb{N}), \forall (q: \mathbb{N}), (2 \cdot q \le m) \Rightarrow (\forall (mu: \mathbb{R}), \forall (alpha: \mathbb{R}), \forall (beta: \mathbb{R}), (0 \le mu) \Rightarrow ((0 \le alpha) \Rightarrow ((0 \le beta) \Rightarrow (0 \le \sum_{k \in \operatorname{Finset.Icc}\left(q, m - q\right)} (\operatorname{a}\left(k, mu + alpha\right) \cdot \operatorname{a}\left(m - k, mu + beta\right) - \operatorname{a}\left(k, mu\right) \cdot \operatorname{a}\left(m - k, mu + alpha + beta\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Interval.tail_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The case q=0 is the full convolution: both products have the same total parameter, so the index law makes their difference zero. For q positive and mu positive, keep S=2mu+alpha+beta fixed and compare mu with mu+min(alpha,beta) on (0,S/2]. Symmetry supplies the correct ordering of the two shifted parameters. If q is positive and mu=0, every index in the tail is positive, so a(k,0)=0 and the remaining product is nonnegative. No limiting argument or additional positivity hypothesis on mu is required.

## References

- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Interval.R`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Interval.Z`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Interval.Z_symm`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Interval.hasDerivAt_slice`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Interval.reflected_interval`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Interval.sliceDerivative`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Interval.slice_strictMonoOn`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Interval.tail_nonneg`
- Dependency: [D5/S3/Analytic/KarpZhangCatalanPower/Coeff](Coeff.md)
