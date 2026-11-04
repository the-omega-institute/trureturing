---
bibkey: airapetyanwitt2001hankel
authors: Ruben Airapetyan and Ingo Witt
year: 2001
title: Isometric properties of the Hankel transformation in weighted Sobolev spaces
doi: 10.1080/10652460108819313
url: https://d-nb.info/1218376961/34
claim: Theorem 1 maps Mellin Sobolev spaces across opposite weights with an explicit derivative loss. Its nonexceptional order-seven-halves instance supplies the weighted output used for the same-source matched-null moment estimate.
strata_touched: []
license: bibliographic-reference-only
triage: anchor
---

# Weighted Hankel mapping supplier

The inspected primary is the [author preprint](https://d-nb.info/1218376961/34),
6 June 1997, 19 pages, SHA-256
`b2575ff48025a663f6a08cdaaa1e886ce14a4855da29967091ca935b98cd2e60`.
The published article is *Integral Transforms and Special Functions*
11(3) (2001), 201--224,
[DOI:10.1080/10652460108819313](https://doi.org/10.1080/10652460108819313).
The theorem and page locators below refer to the inspected preprint;
identity with the uninspected publisher-edition text is not asserted.
No third-party source code or PDF is retained in this repository.

Equation (1), printed p.1, uses

$$
 (\mathsf H_\nu\varphi)(\sigma)
 =\int_0^\infty J_\nu(\sigma\rho)\varphi(\rho)\rho\,d\rho,
 \qquad \nu\ge0.
$$

Appendix A.1, equation (38), printed p.16, defines the whole-half-line
Mellin Sobolev space $\mathcal H^{s,\gamma}$ using the weight line
$\Re z=1/2-\gamma$. In logarithmic coordinates,

$$
 \|\varphi\|_{\mathcal H^{s,\gamma}}
 \asymp\|e^{(1/2-\gamma)y}\varphi(e^y)\|_{H^s(\mathbb R)}.
$$

In particular $\mathcal H^{0,\gamma}=L^2(\rho^{-2\gamma}d\rho)$.
These spaces are not the appendix's distinct $\mathcal K$ spaces,
which splice a conormal norm near zero with another norm at infinity.

Theorem 1(a), printed p.4, supplies compatible continuous extensions

$$
 \mathsf H_\nu:
 \mathcal H^{s,-1/2+\delta}\longrightarrow
 \mathcal H^{s-\delta,-1/2-\delta}.
$$

For the central interval $|\delta|<1+\nu$, Theorem 1(d) states that
its inverse is again $\mathsf H_\nu$. This note uses only that interval,
with $\nu=7/2$, $\delta=5/2<9/2$, giving

$$
 \mathsf H_{7/2}:\mathcal H^{s,2}
 \longrightarrow\mathcal H^{s-5/2,-3}.
$$

This `literature-attested` theorem is reused without a new proof or
Lean declaration. The [actual matched-source application](grafakosteschl2013radial.md#the-matched-actual-null-enters-the-ordinary-hankel-domain)
pays its input domain, identifies the extended transform with the
original radial distribution, and transports the resulting weight to
the original physical moments. The supplier alone gives no sign
estimate for the complete Weil form, RH or Robin.
