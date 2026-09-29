# Normalized Cardinal-Spline Recurrences

## Abstract

One normalized finite positive-part spline representation satisfies knot-safe differentiation, the unit-window recurrence, and the centered reflected recurrence.

All objects in this document use the same finite positive-part sum T. There is no second recursive spline definition: D and C are exponent specializations of T, while s and Q package the shifted comparison used by the strict-curvature induction.

**Definition 1.1 (The normalized finite positive-part spline).**

$$\begin{aligned}\forall m, q \in \mathbb{N}, x \in \mathbb{R},\\\operatorname{T}\left(m, q, x\right) = \frac{\sum_{0 \leq k \leq m} \left(-1\right)^{k} \times \operatorname{binom}\left(m, k\right) \times \operatorname{max}\left(x - k, 0\right)^{q}}{q!}\end{aligned}$$

*Formalization.* `D5/S3/Analytic/Curvature/CardinalSplineRecurrence.T` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural m and q and real x, T(m,q,x) is the alternating binomial sum over k=0,...,m of max(x-k,0)^q, divided by q!. The normalization is part of the definition and is retained by every later identity.

**Definition 1.2 (The first-derivative specialization).**

$$\operatorname{D}\left(m, x\right) = \operatorname{T}\left(m, m - 2, x\right)$$

*Formalization.* `D5/S3/Analytic/Curvature/CardinalSplineRecurrence.D` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D_m is T at exponent m-2. It is represented directly by the same finite sum; the definition does not invoke the noncomputable deriv operator.

**Definition 1.3 (The curvature specialization).**

$$\operatorname{C}\left(m, x\right) = \operatorname{T}\left(m, m - 3, x\right)$$

*Formalization.* `D5/S3/Analytic/Curvature/CardinalSplineRecurrence.C` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

C_m is T at exponent m-3. The knot-safe derivative theorem identifies it as the derivative of D_m in the orders used later.

**Definition 1.4 (The shifted center).**

$$\operatorname{s}\left(m\right) = \frac{m}{2} - \frac{2}{3}$$

*Formalization.* `D5/S3/Analytic/Curvature/CardinalSplineRecurrence.s` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The point s_m=m/2-2/3 is the left endpoint of the closed core. Its half-unit increment under m -> m+1 aligns the box recurrence with the reflected difference.

**Definition 1.5 (The global reflected difference).**

$$\operatorname{Q}\left(m, u\right) = \operatorname{D}\left(m, \operatorname{s}\left(m\right) - u\right) - \operatorname{D}\left(m, \operatorname{s}\left(m\right) + u\right)$$

*Formalization.* `D5/S3/Analytic/Curvature/CardinalSplineRecurrence.Q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Q_m(u) compares D_m at equal offsets on the two sides of s_m. It is defined for every real u; the strict-curvature proof maintains nonnegativity for all u>=0, including offsets beyond the spline support.

**Theorem 1.6 (Knot-safe differentiation).**

$$\begin{aligned}\forall m, q \in \mathbb{N}, x \in \mathbb{R},\\1 \le q \implies \operatorname{HasDerivAt}\left(y \mapsto \operatorname{T}\left(m, q + 1, y\right), \operatorname{T}\left(m, q, x\right), x\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Curvature/CardinalSplineRecurrence.T_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For q>=1, T(m,q+1) has derivative T(m,q) at every real x, including integral knots where a positive-part summand changes branch. The only locally ported fact is the derivative of max(x-c,0)^(r+2). It is attributed to Zhi Kai Pong's Physlib source at commit 50ac243729e00925f91224e3916cce74bb971edf under Apache 2.0; the port changes namespace, imports, and pinned-toolchain adaptation only. It is to be retired when the repository's pinned Mathlib supplies an equivalent declaration. The full applicable license is retained at docs/reports/inoutbalance/physlib-LICENSE.txt.

**Theorem 1.7 (The unit-window recurrence).**

$$\begin{aligned}\forall m \in \mathbb{N}, 3 \le m, x \in \mathbb{R},\\\operatorname{D}\left(m + 1, x\right) = \operatorname{integral}\left(x - 1, x, t, \operatorname{D}\left(m, t\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Curvature/CardinalSplineRecurrence.D_succ_eq_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m>=3, raising the spline order averages D_m over [x-1,x]. The proof applies Mathlib's Pascal summation identity Finset.sum_choose_succ_mul directly, identifies the finite-difference antiderivative, and invokes the interval fundamental theorem of calculus. No standalone Pascal wrapper is added.

**Theorem 1.8 (The centered reflected recurrence).**

$$\begin{aligned}\forall m \in \mathbb{N}, 3 \le m, u \in \mathbb{R},\\\operatorname{Q}\left(m + 1, u\right) = \operatorname{integral}\left(u - \frac{1}{2}, u + \frac{1}{2}, t, \operatorname{Q}\left(m, t\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Curvature/CardinalSplineRecurrence.Q_succ_eq_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substituting the unit-window recurrence at the two reflected points, using s_(m+1)=s_m+1/2, and changing variables gives the exact centered moving window. This identity is global in u and therefore carries support-tail information into the induction rather than asserting only a local core fact.

## References

- Truth anchor: `D5/S3/Analytic/Curvature/CardinalSplineRecurrence.C`
- Truth anchor: `D5/S3/Analytic/Curvature/CardinalSplineRecurrence.D`
- Truth anchor: `D5/S3/Analytic/Curvature/CardinalSplineRecurrence.D_succ_eq_integral`
- Truth anchor: `D5/S3/Analytic/Curvature/CardinalSplineRecurrence.Q`
- Truth anchor: `D5/S3/Analytic/Curvature/CardinalSplineRecurrence.Q_succ_eq_integral`
- Truth anchor: `D5/S3/Analytic/Curvature/CardinalSplineRecurrence.T`
- Truth anchor: `D5/S3/Analytic/Curvature/CardinalSplineRecurrence.T_hasDerivAt`
- Truth anchor: `D5/S3/Analytic/Curvature/CardinalSplineRecurrence.s`
