# Gurland Logarithmic Remainder

## Abstract

The original Gurland logarithmic remainder tends to zero for every positive real pair.

**Definition 1.1 (The source Hurwitz series).**

$$\forall s: \mathbb{N}, \forall b: \mathbb{R}, \operatorname{sourceHurwitz}\left(s, b\right) = \sum_{j \in \mathbb{N}} \frac{1}{\left(j + b\right)^{s}}$$

*Formalization.* `D5/S3/Analytic/SeriesInequalities/GurlandLogRemainder.sourceHurwitz` (`✓ std3`).

*Citation.* Halina Wiśniewska (2025). *Some inequalities for Gurland's ratio of the gamma functions*. URL: <https://arxiv.org/html/2512.07028v1>.

*Commentary.*

The index j ranges over natural numbers starting at zero. The exponent s is natural. In the expansion s=2k with k at least one, and the shift b=1+(x+y)/2 is strictly greater than one. The proof establishes summability on this domain by comparison with the shifted p-series. The shift is the actual real shift in equation (3); it is not reduced modulo one.

**Definition 1.2 (The modified Gamma ratio).**

$$\forall x: \mathbb{R}, \forall y: \mathbb{R}, \operatorname{gammaRatio}\left(x, y\right) = \frac{\operatorname{Gamma}\left(1 + x\right) \cdot \operatorname{Gamma}\left(1 + y\right)}{\operatorname{Gamma}\left(1 + \frac{x + y}{2}\right)^{2}}$$

*Formalization.* `D5/S3/Analytic/SeriesInequalities/GurlandLogRemainder.gammaRatio` (`✓ std3`).

*Citation.* Halina Wiśniewska (2025). *Some inequalities for Gurland's ratio of the gamma functions*. URL: <https://arxiv.org/html/2512.07028v1>.

*Commentary.*

This is equation (2), with the positive-real Gamma function. Its denominator is positive whenever x and y are positive, including positive integer arguments.

**Definition 1.3 (The finite Hurwitz expansion).**

$$\forall x: \mathbb{R}, \forall y: \mathbb{R}, \forall m: \mathbb{N}, \operatorname{partialExpansion}\left(x, y, m\right) = \sum_{k \in \operatorname{Ico}\left(1, m\right)} \frac{(\frac{x - y}{2})^{2 \cdot k} \cdot \operatorname{sourceHurwitz}\left(2 \cdot k, 1 + \frac{x + y}{2}\right)}{k}$$

*Formalization.* `D5/S3/Analytic/SeriesInequalities/GurlandLogRemainder.partialExpansion` (`✓ std3`).

*Citation.* Halina Wiśniewska (2025). *Some inequalities for Gurland's ratio of the gamma functions*. URL: <https://arxiv.org/html/2512.07028v1>.

*Commentary.*

The finite interval Ico(1,m) contains exactly the integers k with 1 <= k < m. This is the original S_m, with no restriction involving Q(x,y).

**Definition 1.4 (The original remainder).**

$$\forall x: \mathbb{R}, \forall y: \mathbb{R}, \forall m: \mathbb{N}, \operatorname{remainder}\left(x, y, m\right) = \operatorname{log}\left(\operatorname{gammaRatio}\left(x, y\right)\right) - \operatorname{partialExpansion}\left(x, y, m\right)$$

*Formalization.* `D5/S3/Analytic/SeriesInequalities/GurlandLogRemainder.remainder` (`✓ std3`).

*Citation.* Halina Wiśniewska (2025). *Some inequalities for Gurland's ratio of the gamma functions*. URL: <https://arxiv.org/html/2512.07028v1>.

*Commentary.*

Equation (4) determines the remainder as log(gammaRatio(x,y))-partialExpansion(x,y,m). The n in the source notation R_n^m is already summed out. This definition also determines the diagonal value without choosing a point in an empty Taylor interval.

**Definition 1.5 (The whole positive-pair question).**

$$claim \Leftrightarrow \forall x: \mathbb{R}, \forall y: \mathbb{R}, 0<x \implies 0<y \implies \operatorname{Tendsto}\left(\operatorname{remainder}\left(x, y\right), atTop, \operatorname{nhds}\left(0\right)\right)$$

*Formalization.* `D5/S3/Analytic/SeriesInequalities/GurlandLogRemainder.claim` (`✓ std3`).

*Citation.* Halina Wiśniewska (2025). *Some inequalities for Gurland's ratio of the gamma functions*. URL: <https://arxiv.org/html/2512.07028v1>.

*Commentary.*

Open Problem 1 asks: In Corollary 1 we showed that R_n^m(x,y) tends to zero under a sufficient condition. Does R_n^m(x,y) tend to zero hold for every x,y > 0? The limit is in the natural expansion order m, with the source using m >= 2. Tendsto uses the atTop filter on natural m and the neighbourhood filter of zero in the reals.

**Theorem 1.6 (The remainder converges on the whole domain).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/GurlandLogRemainder.result` (`✓ std3`). ∎

*Resolves.* `Problems/wisniewska-2025-gurland-remainder` (proved) by `D5/S3/Analytic/SeriesInequalities/GurlandLogRemainder.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wisniewska-2025-gurland-remainder","declaration_gid":"D5/S3/Analytic/SeriesInequalities/GurlandLogRemainder.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Halina Wiśniewska (2025). *Some inequalities for Gurland's ratio of the gamma functions*. URL: <https://arxiv.org/html/2512.07028v1>.

*Commentary.*

Put a=(x+y)/2, d=(x-y)/2 and c_n=d^2/(n+1+a)^2. Positivity gives 0 <= c_n < 1. The positive-real Euler limit at 1+x, 1+y and 1+a cancels the factorial and logarithmic terms. It identifies log(gammaRatio(x,y)) with the sum of -log(1-c_n). The nonnegative logarithmic power series is jointly summable, so its two sums can be exchanged. Each coefficient is exactly d^(2k) times the source Hurwitz series divided by k. Finite interchange identifies the source partial expansions, and their limit gives the stated remainder limit. For x=y the ratio is one and every partial sum and remainder is zero. The convergence is pointwise for every positive pair; no uniform rate on the unbounded quadrant is asserted. Open Problem 2 is the equivalent series identity. Open Problem 3 is not settled. The Euler limit, logarithmic power series, p-series comparison and summation theorems are classical tools. No priority claim is made; the full-text overlap with Merkle's 2005 paper remains unverified.

## References

- Truth anchor: `D5/S3/Analytic/SeriesInequalities/GurlandLogRemainder.claim`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/GurlandLogRemainder.gammaRatio`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/GurlandLogRemainder.partialExpansion`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/GurlandLogRemainder.remainder`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/GurlandLogRemainder.result`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/GurlandLogRemainder.sourceHurwitz`
