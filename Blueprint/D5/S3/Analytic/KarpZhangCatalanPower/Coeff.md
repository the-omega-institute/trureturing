# Catalan power coefficients

## Abstract

Rising-factorial coefficients of Catalan powers and their degree-parameter ordering.

**Definition 1.1 (The coefficient in formula (15)).**

$$\forall (n: \mathbb{N}), \forall (t: \mathbb{R}), \operatorname{a}\left(n, t\right) = \frac{\operatorname{Polynomial.eval}\left(t, \operatorname{ascPochhammer}\left(\mathbb{R}, 2 \cdot n\right)\right)}{\operatorname{Polynomial.eval}\left(t + 1, \operatorname{ascPochhammer}\left(\mathbb{R}, n\right)\right) \cdot (n)!}$$

*Formalization.* `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient is the literal quotient (t) at rising order 2n divided by (t+1) at rising order n and n factorial. Real division is total. Its polynomial continuation agrees with this quotient whenever t is greater than minus one, including every nonnegative parameter.

**Definition 1.2 (The polynomial continuation).**

$$\operatorname{coeffPoly}\left(0\right) = 1,\quad\forall (n: \mathbb{N}), \operatorname{coeffPoly}\left(n + 1\right) = \operatorname{C}\left((n + 1)!^{-1}\right) \times X \times \operatorname{Polynomial.comp}\left(\operatorname{ascPochhammer}\left(\mathbb{R}, n\right), (X + \operatorname{C}\left(n + 2\right))\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.coeffPoly` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The degree-zero polynomial is one. At degree n+1 the polynomial is X times the rising Pochhammer polynomial of order n evaluated at X+n+2, divided by (n+1) factorial.

**Theorem 1.3 (Evaluation of the continuation).**

$$\forall (n: \mathbb{N}), \forall (t: \mathbb{R}), \operatorname{Polynomial.eval}\left(t, \operatorname{coeffPoly}\left(n + 1\right)\right) = \frac{t \cdot \operatorname{Polynomial.eval}\left(t + n + 2, \operatorname{ascPochhammer}\left(\mathbb{R}, n\right)\right)}{(n + 1)!}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.coeffPoly_succ_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Polynomial evaluation gives the product t times the rising factorial at t+n+2. This form is used to cancel the denominator of the original quotient.

**Theorem 1.4 (Cancellation away from the poles).**

$$\forall (n: \mathbb{N}), \forall (t: \mathbb{R}), (-1 < t) \Rightarrow (\operatorname{a}\left(n, t\right) = \operatorname{Polynomial.eval}\left(t, \operatorname{coeffPoly}\left(n\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.a_eq_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For t greater than minus one, all factors of (t+1) at rising order n are positive. Pochhammer multiplication splits off these factors and cancels them, including t=0.

**Theorem 1.5 (The finite product).**

$$\forall (n: \mathbb{N}), \forall (t: \mathbb{R}), (1 \le n) \Rightarrow ((-1 < t) \Rightarrow (\operatorname{a}\left(n, t\right) = \frac{t}{(n)!} \cdot \prod_{r\in\operatorname{Finset.Ico}\left(n + 1, 2 \cdot n\right)} (t + r)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.a_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least one the remaining product runs from n+1 through 2n-1. Finset.Ico excludes its upper endpoint. This representation proves positivity.

**Theorem 1.6 (Positivity).**

$$\forall (n: \mathbb{N}), \forall (t: \mathbb{R}), (0 < t) \Rightarrow (0 < \operatorname{a}\left(n, t\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.a_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every coefficient is positive at a positive parameter. Degree zero is one; in positive degree each factor in the finite product is positive.

**Theorem 1.7 (The zero parameter).**

$$\forall (n: \mathbb{N}), (0 < n) \Rightarrow (\operatorname{a}\left(n, 0\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.a_zero_parameter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At parameter zero every positive-degree coefficient vanishes. This supplies the boundary case of the interval tail inequality.

**Theorem 1.8 (Nonnegative parameters).**

$$\forall (n: \mathbb{N}), \forall (t: \mathbb{R}), (0 \le t) \Rightarrow (0 \le \operatorname{a}\left(n, t\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.a_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive-parameter result and the value at zero show nonnegativity on the entire closed nonnegative half-line.

**Theorem 1.9 (Adjacent coefficient ratios).**

$$\forall (n: \mathbb{N}), \forall (t: \mathbb{R}), (0 < t) \Rightarrow (\operatorname{a}\left(n + 1, t\right) = \operatorname{a}\left(n, t\right) \cdot \frac{\left(t + 2 \cdot n\right) \cdot \left(t + 2 \cdot n + 1\right)}{\left(t + n + 1\right) \cdot \left(n + 1\right)})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.adjacent_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ratio a(n+1,t)/a(n,t), multiplied by n+1, is (t+2n)(t+2n+1)/(t+n+1), including n=0. Cross multiplication at two positive parameters shows that this ratio strictly increases with the parameter.

**Theorem 1.10 (Strict total positivity of order two).**

$$\forall (u: \mathbb{R}), \forall (v: \mathbb{R}), \forall (i: \mathbb{N}), \forall (l: \mathbb{N}), (0 < u) \Rightarrow ((u < v) \Rightarrow ((i < l) \Rightarrow (\operatorname{a}\left(l, u\right) \cdot \operatorname{a}\left(i, v\right) < \operatorname{a}\left(i, u\right) \cdot \operatorname{a}\left(l, v\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.tp2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If i is less than l and 0<u<v, the cross product a(i,u)a(l,v) exceeds a(l,u)a(i,v). The adjacent ratio comparison propagates by induction through every degree gap. The interval derivative uses this strict sign after reflection.

**Theorem 1.11 (The weak cross-product order).**

$$\forall (u: \mathbb{R}), \forall (v: \mathbb{R}), \forall (i: \mathbb{N}), \forall (l: \mathbb{N}), (0 < u) \Rightarrow ((u \le v) \Rightarrow ((i < l) \Rightarrow (\operatorname{a}\left(l, u\right) \cdot \operatorname{a}\left(i, v\right) \le \operatorname{a}\left(i, u\right) \cdot \operatorname{a}\left(l, v\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.tp2_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<u≤v the same determinant is nonnegative. At equal parameters it is zero; otherwise strict total positivity applies.

## Convolution and differentiation of Catalan-power coefficients

Polynomial.eval t (coeffPoly n) evaluates the coefficient polynomial at t. The coefficient a(n,t) is the literal rising-factorial quotient in formula (15). The two agree for t greater than minus one. The generator b(j) is the derivative of a(j,t) at t=0. All sums are finite; natural subtraction occurs only with the subtracted index bounded by the degree.

**Theorem 1.12 (The polynomial convolution law).**

$$\forall (s: \mathbb{R}), \forall (t: \mathbb{R}), \forall (m: \mathbb{N}), \sum_{k\in\operatorname{Finset.range}\left((m + 1)\right)} \operatorname{Polynomial.eval}\left((s), \operatorname{coeffPoly}\left(k\right)\right) \cdot \operatorname{Polynomial.eval}\left((t), \operatorname{coeffPoly}\left(m - k\right)\right) = \operatorname{Polynomial.eval}\left((s + t), \operatorname{coeffPoly}\left(m\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.index_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity holds for arbitrary real s and t, including the roots of denominator factors in the original quotient. The existing Catalan Lagrange coefficient transform identifies evaluation of coeffPoly n at a natural t with the coefficient of C to the natural power t. Multiplication of natural powers supplies convolution on the natural grid. Polynomial uniqueness extends first in s and then in t. The supplied Lagrange transform is reused directly; no real formal power is assumed.

**Theorem 1.13 (The index law for the original coefficients).**

$$\forall (s: \mathbb{R}), \forall (t: \mathbb{R}), \forall (m: \mathbb{N}), (0 \le s) \Rightarrow ((0 \le t) \Rightarrow (\sum_{k\in\operatorname{Finset.range}\left((m + 1)\right)} \operatorname{a}\left(k, s\right) \cdot \operatorname{a}\left(m - k, t\right) = \operatorname{a}\left(m, s + t\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.index_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative s and t, every denominator factor in formula (15) is positive. Substitution of the polynomial form into the all-real polynomial convolution proves the index law. Both zero parameters are included. The literal totalized quotient is not asserted to satisfy the law at negative poles.

**Definition 1.14 (The infinitesimal generator).**

$$\forall (j: \mathbb{N}), \operatorname{b}\left(j\right) = \operatorname{deriv}\left(\operatorname{a}\left(j\right), 0\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.b` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The generator coefficient is the derivative at zero of the original coefficient function. Its polynomial representation is valid on a neighborhood of zero.

**Theorem 1.15 (The generator in closed form).**

$$\forall (j: \mathbb{N}), (1 \le j) \Rightarrow (\operatorname{b}\left(j\right) = \frac{\operatorname{Nat.choose}\left((2 \cdot j), j\right)}{2 \cdot j})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.b_eq_centralBinom` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive natural j, differentiation at zero leaves the product from j+1 through 2j-1 divided by j factorial. Rising-factorial and binomial identities convert it to Nat.choose (2j) j divided by 2j. The division is real division and 2j is positive.

**Theorem 1.16 (Every positive-degree generator coefficient is positive).**

$$\forall (j: \mathbb{N}), (1 \le j) \Rightarrow (0 < \operatorname{b}\left(j\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.b_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The central binomial coefficient and the denominator 2j are positive. This positivity weights each reflected determinant in the interval-slice derivative.

**Theorem 1.17 (Differentiation is convolution with the generator).**

$$\forall (n: \mathbb{N}), \forall (t: \mathbb{R}), (0 \le t) \Rightarrow (\operatorname{HasDerivAt}\left(\operatorname{a}\left(n\right), \sum_{j\in\operatorname{Finset.Icc}\left(1, n\right)} \operatorname{b}\left(j\right) \cdot \operatorname{a}\left(n - j, t\right), t\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.hasDerivAt_a` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every nonnegative t, the derivative of a(n,t) is the sum of b(j)a(n-j,t), with j from one through n. Differentiate the polynomial index law in its first parameter at zero. The derivative of the degree-zero polynomial is zero, so that summand drops out. Equality with the literal quotient on the open interval t greater than minus one supplies a two-sided derivative, also at t=0. The degree-zero sum is empty.

## References

- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.a`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.a_eq_polynomial`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.a_nonneg`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.a_pos`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.a_product`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.a_zero_parameter`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.adjacent_ratio`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.b`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.b_eq_centralBinom`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.b_pos`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.coeffPoly`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.coeffPoly_succ_eval`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.hasDerivAt_a`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.index_law`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.index_polynomial`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.tp2`
- Truth anchor: `D5/S3/Analytic/KarpZhangCatalanPower/Coeff.tp2_le`
- Dependency: [D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge](../../Combinatorics/Nonnesting/CatalanLagrangeBridge.md)
