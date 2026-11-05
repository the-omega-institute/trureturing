# Catalan powers preserve the two sequence classes

## Abstract

Both coefficient signs of Karp and Zhang's Conjecture 4.2.

## Catalan power coefficients

**Definition 1.1 (The coefficient in formula (15)).**

$$\forall (n: \mathbb{N}), \forall (t: \mathbb{R}), \operatorname{a}\left(n, t\right) = \frac{\operatorname{Polynomial.eval}\left(t, \operatorname{ascPochhammer}\left(\mathbb{R}, 2 \cdot n\right)\right)}{\operatorname{Polynomial.eval}\left(t + 1, \operatorname{ascPochhammer}\left(\mathbb{R}, n\right)\right) \cdot (n)!}$$

*Formalization.* `D5/S3/Analytic/KarpZhangCatalanPower/Result.a` (`✓ std3`).

*Citation.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

Formula (15), printed page 8: “We consider the series” h(µ; x) := ∑ hₖ (µ)₂ₖ / ((µ+1)ₖ k!) xᵏ. The coefficient is the literal quotient (t) at rising order 2n divided by (t+1) at rising order n and n factorial. Real division is total. Its polynomial continuation agrees with this quotient whenever t is greater than minus one, including every nonnegative parameter.

**Definition 1.2 (The polynomial continuation).**

$$\operatorname{coeffPoly}\left(0\right) = 1,\quad\forall (n: \mathbb{N}), \operatorname{coeffPoly}\left(n + 1\right) = \operatorname{C}\left((n + 1)!^{-1}\right) \times X \times \operatorname{Polynomial.comp}\left(\operatorname{ascPochhammer}\left(\mathbb{R}, n\right), (X + \operatorname{C}\left(n + 2\right))\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangCatalanPower/Result.coeffPoly` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The degree-zero polynomial is one. At degree n+1 the polynomial is X times the rising Pochhammer polynomial of order n evaluated at X+n+2, divided by (n+1) factorial.

**Theorem 1.3 (Evaluation of the continuation).**

$$\forall (n: \mathbb{N}), \forall (t: \mathbb{R}), \operatorname{Polynomial.eval}\left(t, \operatorname{coeffPoly}\left(n + 1\right)\right) = \frac{t \cdot \operatorname{Polynomial.eval}\left(t + n + 2, \operatorname{ascPochhammer}\left(\mathbb{R}, n\right)\right)}{(n + 1)!}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Result.coeffPoly_succ_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Polynomial evaluation gives the product t times the rising factorial at t+n+2. This form is used to cancel the denominator of the original quotient.

**Theorem 1.4 (Cancellation away from the poles).**

$$\forall (n: \mathbb{N}), \forall (t: \mathbb{R}), (-1 < t) \Rightarrow (\operatorname{a}\left(n, t\right) = \operatorname{Polynomial.eval}\left(t, \operatorname{coeffPoly}\left(n\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Result.a_eq_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For t greater than minus one, all factors of (t+1) at rising order n are positive. Pochhammer multiplication splits off these factors and cancels them, including t=0.

**Theorem 1.5 (Positivity).**

$$\forall (n: \mathbb{N}), \forall (t: \mathbb{R}), (0 < t) \Rightarrow (0 < \operatorname{a}\left(n, t\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Result.a_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The numerator rising factorial and both denominator factors are positive at a positive parameter, by ascPochhammer_pos and factorial positivity.

**Theorem 1.6 (The zero parameter).**

$$\forall (n: \mathbb{N}), (0 < n) \Rightarrow (\operatorname{a}\left(n, 0\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Result.a_zero_parameter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At parameter zero every positive-degree coefficient vanishes. This supplies the boundary case of the interval tail inequality.

**Theorem 1.7 (Nonnegative parameters).**

$$\forall (n: \mathbb{N}), \forall (t: \mathbb{R}), (0 \le t) \Rightarrow (0 \le \operatorname{a}\left(n, t\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Result.a_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive-parameter result and the value at zero show nonnegativity on the entire closed nonnegative half-line.

**Theorem 1.8 (Adjacent coefficient ratios).**

$$\forall (n: \mathbb{N}), \forall (t: \mathbb{R}), (0 < t) \Rightarrow (\operatorname{a}\left(n + 1, t\right) = \operatorname{a}\left(n, t\right) \cdot \frac{\left(t + 2 \cdot n\right) \cdot \left(t + 2 \cdot n + 1\right)}{\left(t + n + 1\right) \cdot \left(n + 1\right)})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Result.adjacent_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ratio a(n+1,t)/a(n,t), multiplied by n+1, is (t+2n)(t+2n+1)/(t+n+1), including n=0. Cross multiplication at two positive parameters shows that this ratio strictly increases with the parameter.

**Theorem 1.9 (Strict total positivity of order two).**

$$\forall (u: \mathbb{R}), \forall (v: \mathbb{R}), \forall (i: \mathbb{N}), \forall (l: \mathbb{N}), (0 < u) \Rightarrow ((u < v) \Rightarrow ((i < l) \Rightarrow (\operatorname{a}\left(l, u\right) \cdot \operatorname{a}\left(i, v\right) < \operatorname{a}\left(i, u\right) \cdot \operatorname{a}\left(l, v\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Result.tp2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If i is less than l and 0<u<v, the cross product a(i,u)a(l,v) exceeds a(l,u)a(i,v). The adjacent ratio comparison extends through every degree gap by strictMono_nat_of_lt_succ applied to a(n,v)/a(n,u). The interval derivative uses this strict sign after reflection.

**Theorem 1.10 (The weak cross-product order).**

$$\forall (u: \mathbb{R}), \forall (v: \mathbb{R}), \forall (i: \mathbb{N}), \forall (l: \mathbb{N}), (0 < u) \Rightarrow ((u \le v) \Rightarrow ((i < l) \Rightarrow (\operatorname{a}\left(l, u\right) \cdot \operatorname{a}\left(i, v\right) \le \operatorname{a}\left(i, u\right) \cdot \operatorname{a}\left(l, v\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Result.tp2_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<u≤v the same determinant is nonnegative. At equal parameters it is zero; otherwise strict total positivity applies.

### Convolution and differentiation of Catalan-power coefficients

Polynomial.eval t (coeffPoly n) evaluates the coefficient polynomial at t. The coefficient a(n,t) is the literal rising-factorial quotient in formula (15). The two agree for t greater than minus one. The generator b(j) is the derivative of a(j,t) at t=0. All sums are finite; natural subtraction occurs only with the subtracted index bounded by the degree.

**Theorem 1.11 (The polynomial convolution law).**

$$\forall (s: \mathbb{R}), \forall (t: \mathbb{R}), \forall (m: \mathbb{N}), \sum_{k\in\operatorname{Finset.range}\left((m + 1)\right)} \operatorname{Polynomial.eval}\left((s), \operatorname{coeffPoly}\left(k\right)\right) \cdot \operatorname{Polynomial.eval}\left((t), \operatorname{coeffPoly}\left(m - k\right)\right) = \operatorname{Polynomial.eval}\left((s + t), \operatorname{coeffPoly}\left(m\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Result.index_polynomial` (`✓ std3`). ∎

*Citation.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

Lemma 4.1(2), printed page 8, states “Index law” λ(α; x)λ(β; x) = λ(α+β; x), attributed to [17, Lemma 7]. Here the coefficient law is expressed using polynomial continuation. The identity holds for arbitrary real s and t, including the roots of denominator factors in the original quotient. The existing Catalan Lagrange coefficient transform identifies evaluation of coeffPoly n at a natural t with the coefficient of C to the natural power t. Multiplication of natural powers supplies convolution on the natural grid. Polynomial uniqueness extends first in s and then in t. The supplied Lagrange transform is reused directly; no real formal power is assumed.

**Theorem 1.12 (The index law for the original coefficients).**

$$\forall (s: \mathbb{R}), \forall (t: \mathbb{R}), \forall (m: \mathbb{N}), (0 \le s) \Rightarrow ((0 \le t) \Rightarrow (\sum_{k\in\operatorname{Finset.range}\left((m + 1)\right)} \operatorname{a}\left(k, s\right) \cdot \operatorname{a}\left(m - k, t\right) = \operatorname{a}\left(m, s + t\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Result.index_law` (`✓ std3`). ∎

*Citation.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

Lemma 4.1(2), printed page 8: “Index law” λ(α; x)λ(β; x) = λ(α+β; x). The lemma is attributed to [17, Lemma 7]. For nonnegative s and t, every denominator factor in formula (15) is positive. Substitution of the polynomial form into the all-real polynomial convolution proves the index law. Both zero parameters are included. The literal totalized quotient is not asserted to satisfy the law at negative poles.

**Definition 1.13 (The infinitesimal generator).**

$$\forall (j: \mathbb{N}), \operatorname{b}\left(j\right) = \operatorname{deriv}\left(\operatorname{a}\left(j\right), 0\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangCatalanPower/Result.b` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The generator coefficient is the derivative at zero of the original coefficient function. Its polynomial representation is valid on a neighborhood of zero.

**Theorem 1.14 (The generator in closed form).**

$$\forall (j: \mathbb{N}), (1 \le j) \Rightarrow (\operatorname{b}\left(j\right) = \frac{\operatorname{Nat.choose}\left((2 \cdot j), j\right)}{2 \cdot j})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Result.b_eq_centralBinom` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive natural j, differentiation at zero leaves the product from j+1 through 2j-1 divided by j factorial. Rising-factorial and binomial identities convert it to Nat.choose (2j) j divided by 2j. The division is real division and 2j is positive.

**Theorem 1.15 (Every positive-degree generator coefficient is positive).**

$$\forall (j: \mathbb{N}), (1 \le j) \Rightarrow (0 < \operatorname{b}\left(j\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Result.b_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The central binomial coefficient and the denominator 2j are positive. This positivity weights each reflected determinant in the interval-slice derivative.

**Theorem 1.16 (Differentiation is convolution with the generator).**

$$\forall (n: \mathbb{N}), \forall (t: \mathbb{R}), (0 \le t) \Rightarrow (\operatorname{HasDerivAt}\left(\operatorname{a}\left(n\right), \sum_{j\in\operatorname{Finset.Icc}\left(1, n\right)} \operatorname{b}\left(j\right) \cdot \operatorname{a}\left(n - j, t\right), t\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Result.hasDerivAt_a` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every nonnegative t, the derivative of a(n,t) is the sum of b(j)a(n-j,t), with j from one through n. Differentiate the polynomial index law in its first parameter at zero. The derivative of the degree-zero polynomial is zero, so that summand drops out. Equality with the literal quotient on the open interval t greater than minus one supplies a two-sided derivative, also at t=0. The degree-zero sum is empty.

## Reflected intervals and tail positivity

All sums are finite. The coefficient a(n,t) is the rising-factorial quotient, and b(j) is its derivative at zero. Natural subtraction occurs only under the stated finite bounds. The boundary filter also handles empty signed intervals without assigning a spurious term to index zero.

**Definition 1.17 (The uncancelled left boundary).**

$$\forall (m: \mathbb{N}), \forall (q: \mathbb{N}), \forall (j: \mathbb{N}), \operatorname{R}\left(m, q, j\right) = \operatorname{Finset.filter}\left((\lambda (i: \mathbb{N}) \mapsto \left(q \le i + j \land i + j \le m - q\right) \land i < q), \operatorname{Finset.range}\left(m - j + 1\right)\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangCatalanPower/Result.R` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

R contains exactly the nonnegative integers in [max(0,q-j), min(q-1,m-q-j)], where the upper endpoint is an integer. Its filter presentation retains the condition i+j≤m-q, so the set is empty when the signed upper endpoint is negative.

**Definition 1.18 (The central convolution interval).**

$$\forall (m: \mathbb{N}), \forall (q: \mathbb{N}), \forall (u: \mathbb{R}), \forall (v: \mathbb{R}), \operatorname{Z}\left(m, q, u, v\right) = \sum_{k \in \operatorname{Finset.Icc}\left(q, m - q\right)} (\operatorname{a}\left(k, u\right) \cdot \operatorname{a}\left(m - k, v\right))$$

*Formalization.* `D5/S3/Analytic/KarpZhangCatalanPower/Result.Z` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Z(m,q,u,v) sums a(k,u)a(m-k,v) for q≤k≤m-q. The two endpoints are included, including a singleton central interval.

**Definition 1.19 (The reflected determinant sum).**

$$\forall (m: \mathbb{N}), \forall (q: \mathbb{N}), \forall (u: \mathbb{R}), \forall (v: \mathbb{R}), \operatorname{sliceDerivative}\left(m, q, u, v\right) = \sum_{j \in \operatorname{Finset.Icc}\left(1, m\right)} (\operatorname{b}\left(j\right) \cdot \sum_{i \in \operatorname{R}\left(m, q, j\right)} (\operatorname{a}\left(i, u\right) \cdot \operatorname{a}\left(m - j - i, v\right) - \operatorname{a}\left(m - j - i, u\right) \cdot \operatorname{a}\left(i, v\right)))$$

*Formalization.* `D5/S3/Analytic/KarpZhangCatalanPower/Result.sliceDerivative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each j from one through m, multiply b(j) by the sum over R(m,q,j) of the degree-parameter determinants with total degree m-j. This is the derivative of Z along a constant-sum line.

**Theorem 1.20 (Cancellation of two reflected intervals).**

$$\forall (m: \mathbb{N}), \forall (q: \mathbb{N}), \forall (j: \mathbb{N}), (2 \cdot q \le m) \Rightarrow ((j \le m) \Rightarrow (\forall (w: \mathbb{N} \to \mathbb{R}), \sum_{i \in \operatorname{Finset.filter}\left((\lambda (i: \mathbb{N}) \mapsto q \le i + j \land i + j \le m - q), \operatorname{Finset.range}\left(m - j + 1\right)\right)} (\operatorname{w}\left(i\right)) - \sum_{i \in \operatorname{Finset.filter}\left((\lambda (i: \mathbb{N}) \mapsto q \le i \land i \le m - q), \operatorname{Finset.range}\left(m - j + 1\right)\right)} (\operatorname{w}\left(i\right)) = \sum_{i \in \operatorname{R}\left(m, q, j\right)} (\operatorname{w}\left(i\right) - \operatorname{w}\left(m - j - i\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Result.reflected_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Restrict both intervals to 0≤i≤m-j. Reflection i↦m-j-i exchanges them. The common part cancels, and the remaining terms pair over R. The identity holds for every real-valued weight w, with no sign assumption.

**Theorem 1.21 (The constant-sum slice derivative).**

$$\forall (m: \mathbb{N}), \forall (q: \mathbb{N}), (2 \cdot q \le m) \Rightarrow (\forall (S: \mathbb{R}), \forall (r: \mathbb{R}), (0 < r) \Rightarrow ((0 < S - r) \Rightarrow (\operatorname{HasDerivAt}\left((\lambda (x: \mathbb{R}) \mapsto \operatorname{Z}\left(m, q, x, S - x\right)), \operatorname{sliceDerivative}\left(m, q, r, S - r\right), r\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Result.hasDerivAt_slice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiate every finite summand. The coefficient derivative identity expands each factor into a lower-degree convolution. Two explicit triangular bijections collect terms with the same j. Reflection then converts their difference into the determinant sum.

**Theorem 1.22 (Reflection symmetry of the interval convolution).**

$$\forall (m: \mathbb{N}), \forall (q: \mathbb{N}), (2 \cdot q \le m) \Rightarrow (\forall (u: \mathbb{R}), \forall (v: \mathbb{R}), \operatorname{Z}\left(m, q, u, v\right) = \operatorname{Z}\left(m, q, v, u\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Result.Z_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The map k↦m-k permutes the closed central interval and exchanges the two coefficient factors. Balancing can therefore choose the smaller parameter as the first coordinate.

**Theorem 1.23 (Strict increase toward the midpoint).**

$$\forall (m: \mathbb{N}), \forall (q: \mathbb{N}), (1 \le q) \Rightarrow ((2 \cdot q \le m) \Rightarrow (\forall (S: \mathbb{R}), (0 < S) \Rightarrow (\operatorname{StrictMonoOn}\left((\lambda (x: \mathbb{R}) \mapsto \operatorname{Z}\left(m, q, x, S - x\right)), \operatorname{Set.Ioc}\left(0, \frac{S}{2}\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Result.slice_strictMonoOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the open left half of a positive constant-sum slice, every determinant is positive whenever its boundary set is nonempty. Every b(j) is positive. The j=1 boundary contains q-1, and its two degrees are strictly ordered, so the derivative is strictly positive. The mean-value theorem gives strict increase on (0,S/2], including comparisons with the midpoint.

**Theorem 1.24 (Every shifted central tail is nonnegative).**

$$\forall (m: \mathbb{N}), \forall (q: \mathbb{N}), (2 \cdot q \le m) \Rightarrow (\forall (mu: \mathbb{R}), \forall (alpha: \mathbb{R}), \forall (beta: \mathbb{R}), (0 \le mu) \Rightarrow ((0 \le alpha) \Rightarrow ((0 \le beta) \Rightarrow (0 \le \sum_{k \in \operatorname{Finset.Icc}\left(q, m - q\right)} (\operatorname{a}\left(k, mu + alpha\right) \cdot \operatorname{a}\left(m - k, mu + beta\right) - \operatorname{a}\left(k, mu\right) \cdot \operatorname{a}\left(m - k, mu + alpha + beta\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Result.tail_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The case q=0 is the full convolution: both products have the same total parameter, so the index law makes their difference zero. For q positive and mu positive, keep S=2mu+alpha+beta fixed and compare mu with mu+min(alpha,beta) on (0,S/2]. Symmetry supplies the correct ordering of the two shifted parameters. If q is positive and mu=0, every index in the tail is positive, so a(k,0)=0 and the remaining product is nonnegative. No limiting argument or additional positivity hypothesis on mu is required.

**Definition 1.25 (Log-convex sequences).**

$$\forall h \in Nat \to Real,\; IsLogConvex\left(h\right) \Leftrightarrow \left(\left(\forall k \in Nat,\; 0 \le h\left(k\right)\right) \land \left(\left(\exists k \in Nat,\; h\left(k\right) \ne 0\right) \land \left(\forall k \in Nat,\; 1 \le k \Rightarrow h\left(k\right)^{2} \le h\left(k - 1\right) \cdot h\left(k + 1\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangCatalanPower/Result.IsLogConvex` (`✓ std3`).

*Citation.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

Definition 1.1, page 2: “Let {fₖ}ₖ₌₀∞ be a non-negative nontrivial real sequence.” The log-convex clause reads: “If fₖ² ≤ fₖ₋₁fₖ₊₁ for all k ∈ ℕ, the sequence is called log-convex (this inequality implies that a nontrivial sequence is strictly positive).”

Here the natural indices in the inequality start at one. The predicate keeps nonnegativity and nontriviality and imposes no interval-support condition. The literal inequalities also admit a sequence supported on {0}; that endpoint case is included. The log-concave class is the existing KarpZhangReciprocal.Result.IsLogConcave, including its interval-support condition.

**Definition 1.26 (The finite Turanian coefficient).**

$$\forall h \in Nat \to Real,\; \forall mu \in Real,\; \forall alpha \in Real,\; \forall beta \in Real,\; \forall m \in Nat,\; delta\left(h, mu, alpha, beta, m\right) = \sum_{k \in \operatorname{Finset}.\operatorname{range}\left(m + 1\right)} h\left(k\right) \cdot h\left(m - k\right) \cdot \left(\operatorname{Coeff}.\operatorname{a}\left(k, mu + alpha\right) \cdot \operatorname{Coeff}.\operatorname{a}\left(m - k, mu + beta\right) - \operatorname{Coeff}.\operatorname{a}\left(k, mu\right) \cdot \operatorname{Coeff}.\operatorname{a}\left(m - k, mu + alpha + beta\right)\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangCatalanPower/Result.delta` (`✓ std3`).

*Citation.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

Printed page 8: “Forming the generalized Turánian”

$$
\Delta_{h}(\alpha, \beta; x) = h(\mu + \alpha; x) \cdot h(\mu + \beta; x) - h(\mu; x) \cdot h(\mu + \alpha + \beta; x)=\sum_{m=2}^{\infty} \delta_{m} x^{m}
$$

“we will have”

$$
\delta_{m} = \sum_{k=0}^{m} h_{k} h_{m - k} M_{k}
$$

$$
M_{k} = \frac{1}{k! \cdot (m - k)!} \cdot [\frac{(\mu + \alpha)_{2 \cdot k} \cdot (\mu + \beta)_{2 \cdot \left(m - k\right)}}{(\mu + \alpha + 1)_{k} \cdot (\mu + \beta + 1)_{m - k}} - \frac{(\mu)_{2 \cdot k} \cdot (\mu + \alpha + \beta)_{2 \cdot \left(m - k\right)}}{(\mu + 1)_{k} \cdot (\mu + \alpha + \beta + 1)_{m - k}}]
$$

The coefficient a is Coeff.a, the literal quotient (t) rising factorial 2k divided by (t+1) rising factorial k times k factorial. Expanding the displayed M_k distributes 1/(k!(m-k)!) over its two products; each product is exactly Coeff.a k at its first shifted parameter times Coeff.a (m-k) at its second shifted parameter. Multiplication by h(k)h(m-k) and summation for k=0,...,m gives the Lean range (m+1) sum, with the same subtraction order. The source series starts at m=2; the finite definition also includes the vanishing degrees zero and one. Neither convergence nor growth assumptions on h are needed.

**Definition 1.27 (Conjecture 4.2).**

$$claim \Leftrightarrow \left(\forall h \in Nat \to Real,\; \forall mu \in Real,\; \forall alpha \in Real,\; \forall beta \in Real,\; \forall m \in Nat,\; 0 \le mu \Rightarrow \left(0 \le alpha \Rightarrow \left(0 \le beta \Rightarrow \left(\left(\operatorname{KarpZhangReciprocal}.\operatorname{Result}.\operatorname{IsLogConcave}\left(h\right) \Rightarrow 0 \le delta\left(h, mu, alpha, beta, m\right)\right) \land \left(IsLogConvex\left(h\right) \Rightarrow delta\left(h, mu, alpha, beta, m\right) \le 0\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangCatalanPower/Result.claim` (`✓ std3`).

*Citation.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

Conjecture 4.2, page 8: Assume that {hₖ}ₖ₌₀∞ is log-concave (log-convex ) and independent of µ. Then the function µ → h(µ; x) defined in (15) is coefficient-wise log-concave (log-convex ).

For every sequence h, nonnegative real mu, alpha and beta, and every natural coefficient degree, delta is nonnegative for the source's log-concave class and nonpositive for its log-convex class. The sequence is independent of the parameters because a single h is fixed before they are quantified.

**Theorem 1.28 (Both signs hold in every degree).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/karp-zhang-2023-conjecture-4-2` (proved) by `D5/S3/Analytic/KarpZhangCatalanPower/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"karp-zhang-2023-conjecture-4-2","declaration_gid":"D5/S3/Analytic/KarpZhangCatalanPower/Result.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

The index law makes the full kernel sum zero. The positive derivative generator and reflected-interval cancellation give nonnegative central tails, including mu=0. The generic Abel identity KarpZhangReciprocal.Result.abel_layers writes delta as the increments of h(k)h(m-k) times these tails.

For log-concavity, KarpZhangReciprocal.Result.balanced_step makes the increments nonnegative. For log-convexity, a zero at index one propagates to every positive index. Otherwise all entries are positive, the adjacent inequalities make successive ratios increase, and the balanced products decrease. The increments for q ≥ 1 are nonpositive; the q = 0 contribution vanishes because the full tail is zero. This includes finite and singleton log-concave supports and the log-convex sequence supported only at zero. The central term is counted once and the degrees zero and one require no special assumption.

## References

- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Result.IsLogConvex`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Result.R`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Result.Z`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Result.Z_symm`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Result.a`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Result.a_eq_polynomial`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Result.a_nonneg`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Result.a_pos`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Result.a_zero_parameter`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Result.adjacent_ratio`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Result.b`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Result.b_eq_centralBinom`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Result.b_pos`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Result.claim`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Result.coeffPoly`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Result.coeffPoly_succ_eval`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Result.delta`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Result.hasDerivAt_a`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Result.hasDerivAt_slice`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Result.index_law`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Result.index_polynomial`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Result.reflected_interval`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Result.result`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Result.sliceDerivative`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Result.slice_strictMonoOn`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Result.tail_nonneg`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Result.tp2`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Result.tp2_le`
- Dependency: [D5/S3/Analytic/KarpZhangReciprocal/Result](../KarpZhangReciprocal/Result.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge](../../Combinatorics/Nonnesting/CatalanLagrangeBridge.md)
