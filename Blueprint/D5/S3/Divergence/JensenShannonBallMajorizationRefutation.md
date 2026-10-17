# Jensen-Shannon balls need not have majorization-minimizers

## Abstract

A three-point Jensen-Shannon ball has no majorization-minimizer.

Vectors are real-valued functions on Fin d, whose indices run from zero to d - 1. A probability vector has nonnegative coordinates and total mass one. For any vector x, x_(j) denotes its j-th largest coordinate, numbered from zero. Thus a sum over j in Fin k is the sum of the k largest coordinates; for k = 0 it is zero.

**Definition 1.1 (Jensen-Shannon divergence).**

$$\forall d \in \mathbb{N},\; (\forall p \in (\operatorname{Fin}\left(d\right) \to \mathbb{R}),\; (\forall q \in (\operatorname{Fin}\left(d\right) \to \mathbb{R}),\; (\operatorname{jensenShannon}\left(p, q\right) = (\frac{1}{2}) \cdot (\sum_{i: \operatorname{Fin}\left(d\right)} (((p_{i}) \cdot (\operatorname{ln}\left(\frac{(2) \cdot (p_{i})}{(p_{i}) + (q_{i})}\right))) + ((q_{i}) \cdot (\operatorname{ln}\left(\frac{(2) \cdot (q_{i})}{(p_{i}) + (q_{i})}\right))))))))$$

*Formalization.* `D5/S3/Divergence/JensenShannonBallMajorizationRefutation.jensenShannon` (`✓ std3`).

*Citation.* Eric P. Hanson (2020). *Entropic Continuity Bounds & Eventually Entanglement-Breaking Channels*. URL: <https://arxiv.org/abs/2010.02408v1>.

*Commentary.*

The divergence uses natural logarithms. Write J(p, q) for the displayed expression. Division by zero is zero. The logarithm is totalized by ln(0) = 0 and ln(x) = ln|x| for nonzero x, so a coordinate of zero contributes zero to its weighted logarithm. If both coordinates are zero, both contributions vanish. Changing between natural and base-two logarithms rescales the divergence by a positive constant.

**Definition 1.2 (A least element for majorization).**

$$\forall d \in \mathbb{N},\; (\forall B \in \operatorname{Set}\left((\operatorname{Fin}\left(d\right) \to \mathbb{R})\right),\; (\forall r \in (\operatorname{Fin}\left(d\right) \to \mathbb{R}),\; ((\operatorname{IsMajorizationMinimizer}\left(B, r\right)) \Leftrightarrow ((r \in B) \land (\forall q \in (\operatorname{Fin}\left(d\right) \to \mathbb{R}),\; ((q \in B) \Rightarrow ((\forall k \in \mathbb{N},\; ((k < d) \Rightarrow (\sum_{j: \operatorname{Fin}\left(k\right)} (r_{(j)}) \le \sum_{j: \operatorname{Fin}\left(k\right)} (q_{(j)})))) \land (\sum_{j: \operatorname{Fin}\left(d\right)} (r_{(j)}) = \sum_{j: \operatorname{Fin}\left(d\right)} (q_{(j)})))))))))$$

*Formalization.* `D5/S3/Divergence/JensenShannonBallMajorizationRefutation.IsMajorizationMinimizer` (`✓ std3`).

*Citation.* Eric P. Hanson (2020). *Entropic Continuity Bounds & Eventually Entanglement-Breaking Channels*. URL: <https://arxiv.org/abs/2010.02408v1>.

*Commentary.*

A majorization-minimizer of a set B is a member r of B with r majorized by every q in B. Equation (2.3) expresses this order by descending partial sums: each sum of k largest coordinates of r is at most the corresponding sum for q, for every natural k < d, and the total sums agree. This is the minimum clause of Eq. (3.1). The set B need not consist of probability vectors.

**Definition 1.3 (The Jensen-Shannon clause of Question 1).**

$$(\operatorname{claim}) \Leftrightarrow (\forall d \in \mathbb{N},\; (\forall p \in (\operatorname{Fin}\left(d\right) \to \mathbb{R}),\; (((\forall i \in \operatorname{Fin}\left(d\right),\; (0 \le p_{i})) \land (\sum_{i: \operatorname{Fin}\left(d\right)} (p_{i}) = 1)) \Rightarrow (\forall t \in \mathbb{R},\; ((0 < t) \Rightarrow (\exists r \in (\operatorname{Fin}\left(d\right) \to \mathbb{R}),\; (\operatorname{IsMajorizationMinimizer}\left(\{q: (\operatorname{Fin}\left(d\right) \to \mathbb{R}) \mid ((\forall i \in \operatorname{Fin}\left(d\right),\; (0 \le q_{i})) \land (\sum_{i: \operatorname{Fin}\left(d\right)} (q_{i}) = 1)) \land (\operatorname{jensenShannon}\left(p, q\right) \le t)\}, r\right))))))))$$

*Formalization.* `D5/S3/Divergence/JensenShannonBallMajorizationRefutation.claim` (`✓ std3`).

*Citation.* Eric P. Hanson (2020). *Entropic Continuity Bounds & Eventually Entanglement-Breaking Channels*. URL: <https://arxiv.org/abs/2010.02408v1>.

*Commentary.*

For every dimension d, every probability vector p and every positive threshold t, the sublevel set of probability vectors q satisfying J(p, q) <= t has a majorization-minimizer. This is the Jensen-Shannon clause of Chapter 8, Question 1. The square-root Jensen-Shannon metric is sqrt(J(p, q) / ln(2)); its closed ball of radius epsilon > 0 is the displayed sublevel set with t = epsilon^2 ln(2).

**Theorem 1.4 (A three-point ball without a majorization-minimizer).**

$$\neg (\operatorname{claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/JensenShannonBallMajorizationRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/hanson-2020-jensen-shannon-ball-majorization-refutation` (refuted) by `D5/S3/Divergence/JensenShannonBallMajorizationRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hanson-2020-jensen-shannon-ball-majorization-refutation","declaration_gid":"D5/S3/Divergence/JensenShannonBallMajorizationRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Eric P. Hanson (2020). *Entropic Continuity Bounds & Eventually Entanglement-Breaking Channels*. URL: <https://arxiv.org/abs/2010.02408v1>.

*Commentary.*

Take p = (2/3, 4/15, 1/15), a = (1/2, 2/5, 1/10), b = (8/15, 1/3, 2/15) and t = J(p, a) > 0. All three are probability vectors. For every probability vector r in this ball that is majorized by a, the descending partial sums give 1/10 <= r_i <= 1/2 for every coordinate.

The supporting-line inequality for J(p, .) at a gives J(p, r) >= J(p, a) + (1/2) ln(5/7) (r_0 - 1/2), with equality only at r = a. Indeed, its three supporting coefficients are (1/2) ln(6/7), (1/2) ln(6/5) and (1/2) ln(6/5); their sum against r - a reduces to the displayed expression because the coordinates of r and a each sum to one. Since ln(5/7) < 0 and r_0 <= 1/2, membership in the ball forces r = a. Every majorization-minimizer would be majorized by a, which is itself in the ball, and would therefore equal a.

However, 60 (J(p, b) - J(p, a)) = ln(4 * 5^55 * 7^35 / 3^144) < 0, since 4 * 5^55 * 7^35 < 3^144. Hence b also belongs to the ball. The two largest coordinates of a sum to 9/10, whereas those of b sum to 13/15. The strict inequality 9/10 > 13/15 shows that a is not majorized by b. Thus this ball has no majorization-minimizer.

## References

- Truth anchor: `D5/S3/Divergence/JensenShannonBallMajorizationRefutation.IsMajorizationMinimizer`
- Truth anchor: `D5/S3/Divergence/JensenShannonBallMajorizationRefutation.claim`
- Truth anchor: `D5/S3/Divergence/JensenShannonBallMajorizationRefutation.jensenShannon`
- Truth anchor: `D5/S3/Divergence/JensenShannonBallMajorizationRefutation.result`
- Dependency: [D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing](../Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.md)
- Dependency: [D5/S3/TotalVariation/CycleSingleCutMinimax](../TotalVariation/CycleSingleCutMinimax.md)
