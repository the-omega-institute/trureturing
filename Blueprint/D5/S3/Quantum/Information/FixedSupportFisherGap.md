# Fixed-support Fisher gap

## Abstract

A normalized probability curve on one fixed finite support has a strict Fisher-information gap.

Let ι be any finite index type. The same support values x(j) and the same nonnegative weight curve p(j,u) are used for every parameter u in the open interval (2a−1,1). The curve is normalized, has mean a, and has second moment (1+u)/2 throughout that interval. The Fisher sum is filtered to the indices with positive current weight; indices of weight zero contribute zero because nonnegative differentiable weights have zero derivative at a local minimum.

**Theorem 1.1 (The exact gap).**

$$\begin{aligned}\forall \iota \text{finite}, \forall a,R\in \mathbb{R}, \forall x:\iota\to\mathbb{R}, \forall p:\iota\to\mathbb{R}\to\mathbb{R},\\J=(2a-1,1), 0<a<1,\\\forall j\in \iota, x_{j}\in [-1,1], p_{j} \text{differentiable on} J,\\\forall u\in J, \forall j\in \iota, 0\le p_{j}(u),\\\forall u\in J, \sum_{j\in \iota}p_{j}(u)=1, \sum_{j\in \iota}p_{j}(u)x_{j}=a, \sum_{j\in \iota}p_{j}(u)x_{j}^{2}=\frac{1+u}{2},\\\forall u\in J, \sum_{j\in \iota:0<p_{j}(u)}\frac{(p_{j}'(u))^{2}}{p_{j}(u)}\le \frac{R(1-a^{2})}{(1-u)(1+u-2a^{2})}\\\longrightarrow 1+\frac{a^{2}}{(1+4a+2(1+a)\log 2)^{2}}\le R\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FixedSupportFisherGap.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume 0<a<1, every support point lies in [−1,1], every weight is differentiable on (2a−1,1), and the displayed normalization and two moment identities hold for the same curve at every parameter. If its actual positive-support Fisher sum is at most R(1−a²)/((1−u)(1+u−2a²)) pointwise, then R is at least 1+a² divided by (1+4a+2(1+a) log 2)². The conclusion is uniform over the arbitrary finite fixed support and does not assume endpoint continuity or a limiting value of p.

The proof differentiates the three same-curve constraints, applies the finite weighted Cauchy–Schwarz inequality with zero-weight terms removed, and controls the resulting normalized mean along the interval. Monotonicity and continuity of the auxiliary expressions at the left endpoint produce the exact log 2 constant.

For nonvacuity, the support [−1,1/2,1] with a=1/2 and R=4/3 and weights ((1+2u)/12, 2(1−u)/3, (1+2u)/4) satisfies all hypotheses on (0,1); all three weights are strictly positive there, so the filtered Fisher sum is the full three-term sum.

## References

- Truth anchor: `D5/S3/Quantum/Information/FixedSupportFisherGap.result`
