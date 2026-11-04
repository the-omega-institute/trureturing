# A descending chain for polynomial log-functions

## Abstract

Signed derivative regions of polynomial log-functions form a descending chain with completely monotone intersection.

**Definition 1.1 (A polynomial in the logarithm divided by its argument).**

$$\forall (p: \operatorname{Polynomial}\left(\mathbb{R}\right)), (\forall (x: \mathbb{R}), (\operatorname{D5.S3.Analytic.LogFunctionMonotoneChain.logFunction}\left(p, x\right) = \frac{\operatorname{Polynomial.eval}\left(\operatorname{Real.log}\left(x\right), p\right)}{x}))$$

*Formalization.* `D5/S3/Analytic/LogFunctionMonotoneChain.logFunction` (`✓ std3`).

*Citation.* Rourou Ma; Julian Weigert (2025). *Complete monotonicity of log-functions*. DOI: [10.1007/s13324-025-01136-9](https://doi.org/10.1007/s13324-025-01136-9). URL: <https://arxiv.org/abs/2505.04225v2>.

*Commentary.*

For a real polynomial p, the associated function is p(log x)/x. This is the univariate case of the class in Intro.tex, lines 20–23. The formula defines a function on all real arguments, while every derivative sign condition below concerns only x > 0.

**Definition 1.2 (The region determined by one signed derivative).**

$$\forall (n: \mathbb{N}), (\forall (k: \mathbb{N}), (\operatorname{D5.S3.Analytic.LogFunctionMonotoneChain.derivativeRegion}\left(n, k\right) = \{(p: \operatorname{Polynomial}\left(\mathbb{R}\right)) \mid (\operatorname{Polynomial.natDegree}\left(p\right) \le n) \land (\forall (x: \mathbb{R}), (((0: \mathbb{R}) < x) \to ((0: \mathbb{R}) \le (((-1: \mathbb{R}))^{k}) \cdot (\operatorname{iteratedDeriv}\left(k, \operatorname{D5.S3.Analytic.LogFunctionMonotoneChain.logFunction}\left(p\right), x\right)))))\}))$$

*Formalization.* `D5/S3/Analytic/LogFunctionMonotoneChain.derivativeRegion` (`✓ std3`).

*Citation.* Rourou Ma; Julian Weigert (2025). *Complete monotonicity of log-functions*. DOI: [10.1007/s13324-025-01136-9](https://doi.org/10.1007/s13324-025-01136-9). URL: <https://arxiv.org/abs/2505.04225v2>.

*Commentary.*

The region consists of real polynomials of natural degree at most n whose associated log-function has nonnegative signed kth derivative at every positive argument. The natural degree of the zero polynomial is zero. These are the polynomial parameters of the function regions in infiniteOrderDeriv.tex, lines 154–159. The positive domain is the one specified in Intro.tex, line 22, and in the preceding example, infiniteOrderDeriv.tex, line 150.

**Definition 1.3 (All signed derivative inequalities on the positive half-line).**

$$\forall (f: (\mathbb{R}) \to (\mathbb{R})), ((\operatorname{D5.S3.Analytic.LogFunctionMonotoneChain.completelyMonotone}\left(f\right)) \Leftrightarrow (\forall (k: \mathbb{N}), (\forall (x: \mathbb{R}), (((0: \mathbb{R}) < x) \to ((0: \mathbb{R}) \le (((-1: \mathbb{R}))^{k}) \cdot (\operatorname{iteratedDeriv}\left(k, f, x\right)))))))$$

*Formalization.* `D5/S3/Analytic/LogFunctionMonotoneChain.completelyMonotone` (`✓ std3`).

*Citation.* Rourou Ma; Julian Weigert (2025). *Complete monotonicity of log-functions*. DOI: [10.1007/s13324-025-01136-9](https://doi.org/10.1007/s13324-025-01136-9). URL: <https://arxiv.org/abs/2505.04225v2>.

*Commentary.*

Every derivative order, including order zero, must have its alternating sign nonnegative at every positive point. Order zero requires the function itself to be nonnegative. Intro.tex, lines 1–4, states complete monotonicity for smooth functions. This predicate records the derivative sign conditions alone, without a separate smoothness hypothesis; below it is applied to polynomial log-functions.

**Definition 1.4 (Nesting and the intersection for every degree bound).**

$$(\operatorname{D5.S3.Analytic.LogFunctionMonotoneChain.claim}) \Leftrightarrow (\forall (n: \mathbb{N}), ((\forall (k: \mathbb{N}), ((1 \le k) \to (\operatorname{D5.S3.Analytic.LogFunctionMonotoneChain.derivativeRegion}\left(n, (k) + (1)\right) \subseteq \operatorname{D5.S3.Analytic.LogFunctionMonotoneChain.derivativeRegion}\left(n, k\right)))) \land (\forall (p: \operatorname{Polynomial}\left(\mathbb{R}\right)), ((\operatorname{Polynomial.natDegree}\left(p\right) \le n) \to ((\forall (k: \mathbb{N}), ((1 \le k) \to (p \in \operatorname{D5.S3.Analytic.LogFunctionMonotoneChain.derivativeRegion}\left(n, k\right)))) \Leftrightarrow (\operatorname{D5.S3.Analytic.LogFunctionMonotoneChain.completelyMonotone}\left(\operatorname{D5.S3.Analytic.LogFunctionMonotoneChain.logFunction}\left(p\right)\right)))))))$$

*Formalization.* `D5/S3/Analytic/LogFunctionMonotoneChain.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rourou Ma; Julian Weigert (2025). *Complete monotonicity of log-functions*. DOI: [10.1007/s13324-025-01136-9](https://doi.org/10.1007/s13324-025-01136-9). URL: <https://arxiv.org/abs/2505.04225v2>.

*Commentary.*

For every natural degree bound n, the region of order k + 1 is contained in the region of order k whenever k is at least one. For each polynomial of natural degree at most n, membership in all regions of positive order is equivalent to complete monotonicity of its log-function. This expresses the nesting and intersection in infiniteOrderDeriv.tex, lines 154–159, on the positive half-line, and includes the degree bound n = 0.

**Theorem 1.5 (The signed derivative regions descend to complete monotonicity).**

$$\forall (n: \mathbb{N}), ((\forall (k: \mathbb{N}), ((1 \le k) \to (\operatorname{D5.S3.Analytic.LogFunctionMonotoneChain.derivativeRegion}\left(n, (k) + (1)\right) \subseteq \operatorname{D5.S3.Analytic.LogFunctionMonotoneChain.derivativeRegion}\left(n, k\right)))) \land (\forall (p: \operatorname{Polynomial}\left(\mathbb{R}\right)), ((\operatorname{Polynomial.natDegree}\left(p\right) \le n) \to ((\forall (k: \mathbb{N}), ((1 \le k) \to (p \in \operatorname{D5.S3.Analytic.LogFunctionMonotoneChain.derivativeRegion}\left(n, k\right)))) \Leftrightarrow (\operatorname{D5.S3.Analytic.LogFunctionMonotoneChain.completelyMonotone}\left(\operatorname{D5.S3.Analytic.LogFunctionMonotoneChain.logFunction}\left(p\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/LogFunctionMonotoneChain.result` (`✓ std3`). ∎

*Resolves.* `Problems/ma-weigert-2025-log-function-monotone-chain` (proved) by `D5/S3/Analytic/LogFunctionMonotoneChain.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ma-weigert-2025-log-function-monotone-chain","declaration_gid":"D5/S3/Analytic/LogFunctionMonotoneChain.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Rourou Ma; Julian Weigert (2025). *Complete monotonicity of log-functions*. DOI: [10.1007/s13324-025-01136-9](https://doi.org/10.1007/s13324-025-01136-9). URL: <https://arxiv.org/abs/2505.04225v2>.

*Commentary.*

Fix a real polynomial p. Define polynomials q₀ = p and qⱼ₊₁ = ((↑j : ℝ) + 1)qⱼ − qⱼ′, with j a natural number included in the real scalars. Induction gives (−1)ʲ f⁽ʲ⁾(x) = (x⁻¹)ʲ⁺¹ qⱼ(log x) for x > 0, where f(x) = p(log x)/x. At order zero this is division by x. For the next order, differentiate the identity on a neighborhood inside the positive half-line. The product rule for the inverse power and the chain rule for the polynomial composed with log give precisely the recurrence for qⱼ₊₁.

The factor (x⁻¹)ʲ⁺¹ is strictly positive. Evaluating at x = exp y shows that nonnegativity of the signed jth derivative on x > 0 implies qⱼ(y) ≥ 0 for every real y. Conversely, nonnegativity of qⱼ on the real line implies the signed derivative inequality by multiplication by that positive factor. The degree bound on p is retained in both directions.

A polynomial nonnegative on the real line has nonnegative leading coefficient. For natural degree zero, write it as a constant and evaluate at zero. For positive degree, a negative leading coefficient would make its values tend to minus infinity as the argument tends to plus infinity, contradicting nonnegativity.

Now let a > 0 and suppose r = aq − q′ is nonnegative everywhere. If q has natural degree zero, r = aq and division by a gives q ≥ 0. Otherwise q′ has smaller degree than aq, so r has the same degree as q and leading coefficient a times that of q. The leading-coefficient observation applied to r gives a nonnegative leading coefficient for q. Applying it to r(−y), and using the common degree and the sign of the leading coefficient under y ↦ −y, gives a nonnegative leading coefficient for q(−y) as well.

Positive degree makes both of these nonnegative leading coefficients nonzero and hence positive. Consequently q tends to plus infinity at both ends of the real line. Continuity then gives a global minimum at some m. Fermat's theorem gives q′(m) = 0, so 0 ≤ r(m) = aq(m). Since a is positive, q(m) ≥ 0; the minimum property yields q(y) ≥ 0 for every y.

Apply this implication with q = qₖ and a = (↑k : ℝ) + 1. Nonnegativity of qₖ₊₁ implies nonnegativity of qₖ. Transferring back to derivatives proves inclusion of the region of order k + 1 in the region of order k for every natural k, and hence for every k at least one.

Finally, membership in all regions of positive order supplies every positive-order sign inequality. Membership in the region of order one, followed by the inclusion at k = 0, supplies the zeroth-order inequality. Thus all orders satisfy the complete monotonicity predicate. In the reverse direction, that predicate supplies the sign inequality at each order, and the given degree bound supplies the remaining condition for membership. Combining this equivalence with the inclusions proves both assertions for each n.

## References

- Truth anchor: `D5/S3/Analytic/LogFunctionMonotoneChain.claim`
- Truth anchor: `D5/S3/Analytic/LogFunctionMonotoneChain.completelyMonotone`
- Truth anchor: `D5/S3/Analytic/LogFunctionMonotoneChain.derivativeRegion`
- Truth anchor: `D5/S3/Analytic/LogFunctionMonotoneChain.logFunction`
- Truth anchor: `D5/S3/Analytic/LogFunctionMonotoneChain.result`
