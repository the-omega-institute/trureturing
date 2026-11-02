# Integrable equal-quantile-bin approximation

## Abstract

Synchronized conditional means of quantiles approximate integrable real laws while preserving discrete convex order and genuine absolute first-moment tails.

For a Borel probability law mu with integrable identity, let Q_mu be its generalized quantile. For positive integer n and k in Fin n, put a(mu,n,k)=n times the integral of Q_mu over (k/n,(k+1)/n]. BinLaw(mu,n) is the actual uniform finite probability law assigning weight 1/n to these n means. Repeated atoms are allowed. Tail(rho,R) denotes the integral of |x| over |x|>R against rho. CoordinateTail(i,R,pi) is the corresponding absolute ith-coordinate tail of the actual joint law. The same n is used for both marginals; no law is clipped or independently renormalized.

**Theorem 1.1 (Absolute tails of every bin-mean law).**

$$\begin{aligned}\forall mu: \operatorname{ProbabilityMeasure}\left(\mathbb{R}\right), \operatorname{IntegrableIdentity}\left(mu\right) \Rightarrow\forall n: \mathbb{N}, 0<n \Rightarrow\forall R: \mathbb{R}, 0 \leq R \Rightarrow\\\operatorname{Tail}\left(\operatorname{BinLaw}\left(mu, n\right), R\right) \leq 2\operatorname{Tail}\left(mu, R/2\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/NoncompactQuantile.absolute_tail_le` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

On a bin of mass 1/n, the absolute mean times 1/n is at most the integral of |Q_mu|. Split |Q_mu| at R/2. The portion below that threshold contributes at most R/(2n). If the absolute mean exceeds R, this contribution is less than half the absolute-mean contribution. Thus the latter is at most twice the remaining bin tail. Sum over the disjoint bins and apply the exact quantile pushforward identity. Integrability of the original absolute value then makes these bounds vanish uniformly over every positive resolution.

**Theorem 1.2 (Actual finite martingale joints with converging marginals).**

$$\begin{aligned}\forall mu: \operatorname{ProbabilityMeasure}\left(\mathbb{R}\right), \forall nu: \operatorname{ProbabilityMeasure}\left(\mathbb{R}\right), \operatorname{IntegrableIdentity}\left(mu\right) \Rightarrow\operatorname{IntegrableIdentity}\left(nu\right) \Rightarrow\\\operatorname{Mean}\left(mu\right)=\operatorname{Mean}\left(nu\right) \Rightarrow(\forall z: \mathbb{R}, \operatorname{StopLoss}\left(mu, z\right) \leq \operatorname{StopLoss}\left(nu, z\right)) \Rightarrow\\\exists piSeq: \mathbb{N} \to \operatorname{ProbabilityMeasure}\left(\mathbb{R}\times\mathbb{R}\right), (\forall n: \mathbb{N}, \operatorname{IsMartingaleCoupling}\left(\operatorname{BinLaw}\left(mu, n+1\right), \operatorname{BinLaw}\left(nu, n+1\right), \operatorname{apply}\left(piSeq, n\right)\right))\\\land \operatorname{WeakLimit}\left(n\mapsto\operatorname{BinLaw}\left(mu, n+1\right), mu\right) \land \operatorname{WeakLimit}\left(n\mapsto\operatorname{BinLaw}\left(nu, n+1\right), nu\right)\\\land \forall epsilon: \mathbb{R}, 0<epsilon \Rightarrow\exists R: \mathbb{R}, 0<R \land \forall n: \mathbb{N}, \operatorname{CoordinateTail}\left(1, R, \operatorname{apply}\left(piSeq, n\right)\right)+\operatorname{CoordinateTail}\left(2, R, \operatorname{apply}\left(piSeq, n\right)\right)<epsilon\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/NoncompactQuantile.exists_martingale_approximations` (`✓ std3`). ∎

*Citation.* Lasse Leskelä and Matti Vihola (2017). *Conditional convex orders and measurable martingale couplings*. DOI: [10.3150/16-BEJ827](https://doi.org/10.3150/16-BEJ827). URL: <https://arxiv.org/abs/1404.0999>.

*Commentary.*

Mean(rho) is the integral of the identity and StopLoss(rho,z) is the integral of max(x-z,0). IsMartingaleCoupling denotes both exact pushforward marginals, integrability of both joint coordinates, and zero displacement integrals for every bounded measurable first-coordinate test. WeakLimit denotes convergence in the weak topology of probability measures. The conclusion chooses one sequence of actual finite joint laws and asserts the two marginal convergences and a single uniform sum-of-coordinate-tails criterion.

Quantile integrability follows from the original law by its pushforward identity. Each bin mean is monotone in its bin index, and the sum through bin K is n times the integral of Q_mu over (0,(K+1)/n]. Equal means and the stop-loss inequalities give reversed lower integrated-quantile inequalities. Finite majorization therefore orders both lists of bin means, and the existing uniform finite martingale-coupling construction produces the actual joint laws.

At every continuity point in (0,1), the bin containing that point shrinks to it, and its average converges to the quantile value. Monotone quantiles have only countably many discontinuities. Dominated convergence for bounded continuous tests gives weak convergence of the finite laws. The absolute-tail bound gives uniform integrability separately, and the exact marginal identities transfer it to each actual joint. No density, nonatomicity, common compact interval or filtration-generation assumption is used.

**Theorem 1.3 (From bounded continuous tests to bounded measurable tests).**

$$\begin{aligned}\forall pi: \operatorname{ProbabilityMeasure}\left(\mathbb{R}\times\mathbb{R}\right), \operatorname{IntegrableCoordinate}\left(1, pi\right) \Rightarrow\operatorname{IntegrableCoordinate}\left(2, pi\right) \Rightarrow\\(\forall h: \mathbb{R} \to \mathbb{R}, \operatorname{Continuous}\left(h\right) \Rightarrow(\exists M: \mathbb{R}, \forall x: \mathbb{R}, |\operatorname{apply}\left(h, x\right)| \leq M) \Rightarrow\operatorname{DisplacementIntegral}\left(h, pi\right)=0) \Rightarrow(\forall h: \mathbb{R} \to \mathbb{R}, \operatorname{Measurable}\left(h\right) \Rightarrow(\exists M: \mathbb{R}, \forall x: \mathbb{R}, |\operatorname{apply}\left(h, x\right)| \leq M) \Rightarrow\operatorname{DisplacementIntegral}\left(h, pi\right)=0)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/NoncompactQuantile.tested_measurable_of_continuous` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

DisplacementIntegral(h,pi) is the integral of (y-x)h(x) against pi. Bound means the existence of one real bound for the absolute value of h at every real argument. Both coordinate-integrability hypotheses concern this same joint law. The premise quantifies over every continuous bounded h; the conclusion quantifies over every Borel measurable bounded h.

Weight the joint law by the positive and negative parts of y-x and project each finite weighted measure through the first coordinate. Vanishing continuous displacement tests identify these two finite measures by bounded-continuous extensionality. Their equality then gives the identity for every bounded measurable test. This is the shared weighted-measure argument used by the compact and integrable constructions.

## References

- Truth anchor: `D5/S3/Analytic/Probability/NoncompactQuantile.absolute_tail_le`
- Truth anchor: `D5/S3/Analytic/Probability/NoncompactQuantile.exists_martingale_approximations`
- Truth anchor: `D5/S3/Analytic/Probability/NoncompactQuantile.tested_measurable_of_continuous`
- Dependency: [D5/S3/Analytic/Probability/ConditionalMeanApproximation](ConditionalMeanApproximation.md)
