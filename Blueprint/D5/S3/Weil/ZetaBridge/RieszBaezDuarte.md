# Riesz and Baez-Duarte Identities

## Abstract

The reciprocal even zeta values define the Riesz function and the Baez-Duarte sequence. Their exponential generating series and signed Moebius series converge to the corresponding transforms.

The zeta function is the complex Riemann zeta function; natural arguments are viewed as complex numbers. Its values at the positive even integers are real and nonzero. The arithmetic Moebius function retains its signed integer values, viewed in the reals. HasSum denotes convergence of the entire real series to its specified value.

**Definition 1.1 (The Riesz function).**

$$\forall x\in \mathbb{R}, \operatorname{riesz}\left(x\right) = x \sum_{j=0}^{\infty} \frac{(-1)^{j} x^{j}}{j! \Re \operatorname{riemannZeta}\left(2j+2\right)}$$

*Formalization.* `D5/S3/Weil/ZetaBridge/RieszBaezDuarte.riesz` (`✓ std3`).

*Citation.* Jerzy Cislo and Marek Wolf (2008). *On the Riesz and Baez-Duarte criteria for the Riemann Hypothesis*. URL: <https://arxiv.org/abs/0807.2971v1>.

*Commentary.*

The defining series is absolutely convergent for every real argument. The absolute reciprocal coefficients are uniformly bounded by the sum of the positive reciprocal-square series; the exponential series then provides a summable majorant.

**Definition 1.2 (The discrete coefficients).**

$$\forall k\in \mathbb{N}, \operatorname{baezDuarte}\left(k\right) = \sum_{j=0}^{k} \frac{(-1)^{j} \operatorname{choose}\left(k, j\right)}{\Re \operatorname{riemannZeta}\left(2j+2\right)}$$

*Formalization.* `D5/S3/Weil/ZetaBridge/RieszBaezDuarte.baezDuarte` (`✓ std3`).

*Citation.* Jerzy Cislo and Marek Wolf (2008). *On the Riesz and Baez-Duarte criteria for the Riemann Hypothesis*. URL: <https://arxiv.org/abs/0807.2971v1>.

*Commentary.*

The finite binomial transform is defined at every natural index. It is distinct from both Li curvature coefficients and Jensen coefficients.

**Theorem 1.3 (The signed arithmetic representation).**

$$\forall k\in \mathbb{N}, \operatorname{HasSum}\left((n:\mathbb{N}) \mapsto \frac{\operatorname{moebius}\left((n+1)\right)}{(n+1)^{2}} (1-\frac{1}{(n+1)^{2}})^{k}, \operatorname{baezDuarte}\left(k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/RieszBaezDuarte.baez_duarte_hasSum_moebius` (`✓ std3`). ∎

*Citation.* Jerzy Cislo and Marek Wolf (2008). *On the Riesz and Baez-Duarte criteria for the Riemann Hypothesis*. URL: <https://arxiv.org/abs/0807.2971v1>.

*Commentary.*

Apply the signed Moebius Dirichlet series at each positive even zeta argument, then interchange the finite binomial sum with the convergent arithmetic series. The first arithmetic term is included: it is one at index zero and zero at positive discrete indices.

**Theorem 1.4 (The exponential generating series).**

$$\forall x\in \mathbb{R}, 0<x \Rightarrow \operatorname{HasSum}\left((k:\mathbb{N}) \mapsto \frac{\operatorname{baezDuarte}\left(k\right) x^{k}}{k!}, \operatorname{exp}\left(x\right) (\frac{\operatorname{riesz}\left(x\right)}{x})\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/RieszBaezDuarte.riesz_generating_hasSum` (`✓ std3`). ∎

*Citation.* Jerzy Cislo and Marek Wolf (2008). *On the Riesz and Baez-Duarte criteria for the Riemann Hypothesis*. URL: <https://arxiv.org/abs/0807.2971v1>.

*Commentary.*

The absolutely convergent Cauchy product of the exponential series and the original Riesz quotient series gives the identity. The factorial normalization turns each convolution coefficient into its finite binomial transform.

**Theorem 1.5 (The arithmetic exponential kernel).**

$$\forall x\in \mathbb{R}, 0<x \Rightarrow \operatorname{HasSum}\left((n:\mathbb{N}) \mapsto \frac{\operatorname{moebius}\left((n+1)\right)}{(n+1)^{2}} \operatorname{exp}\left(\frac{-x}{(n+1)^{2}}\right), \frac{\operatorname{riesz}\left(x\right)}{x}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/RieszBaezDuarte.riesz_hasSum_moebius` (`✓ std3`). ∎

*Citation.* Jerzy Cislo and Marek Wolf (2008). *On the Riesz and Baez-Duarte criteria for the Riemann Hypothesis*. URL: <https://arxiv.org/abs/0807.2971v1>.

*Commentary.*

The two preceding identities combine after an absolutely convergent double-series interchange. The product of a reciprocal-square weight and an exponential-series term bounds each absolute summand. Evaluating the inner exponential and multiplying by the negative exponential factor gives the stated kernel, with all positive arithmetic indices retained.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/RieszBaezDuarte.baezDuarte`
- Truth anchor: `D5/S3/Weil/ZetaBridge/RieszBaezDuarte.baez_duarte_hasSum_moebius`
- Truth anchor: `D5/S3/Weil/ZetaBridge/RieszBaezDuarte.riesz`
- Truth anchor: `D5/S3/Weil/ZetaBridge/RieszBaezDuarte.riesz_generating_hasSum`
- Truth anchor: `D5/S3/Weil/ZetaBridge/RieszBaezDuarte.riesz_hasSum_moebius`
