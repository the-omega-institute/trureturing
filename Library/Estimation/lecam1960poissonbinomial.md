---
bibkey: lecam1960poissonbinomial
authors: Lucien Le Cam
year: 1960
title: An approximation theorem for the Poisson binomial distribution
doi: 10.2140/pjm.1960.10.1181
url: https://msp.org/pjm/1960/10-4/p11.xhtml
claim: "Theorem 1 and its indicator specialization bound full variation between an independent Bernoulli sum and a Poisson law of the same mean by twice the sum of squared success probabilities."
strata_touched: []
license: citation-only
triage: anchor
---

# Poisson approximation and the relative-probability boundary

## Verified locator

DOI: <https://doi.org/10.2140/pjm.1960.10.1181> resolves to the
[MSP publication page](https://msp.org/pjm/1960/10-4/p11.xhtml), HTTP 200,
identifying Le Cam, this title and *Pacific Journal of Mathematics*
10(4), 1181–1197.
The [publisher PDF](https://msp.org/pjm/1960/10-4/pjm-v10-n4-p11-s.pdf)
is accessible. The norm definition on printed p. 1181, Theorem 1
on p. 1183, and its proof and indicator specialization on p. 1184
(PDF pp. 2, 4–5) were inspected.

## Classical statement

For independent Bernoulli variables with probabilities $p_i$, set
$W=\sum_iX_i$ and $\lambda=\sum_ip_i<\infty$. The paper uses
full variation, $\|P-Q\|=\sup_{|f|\le1}|\int f\,d(P-Q)|$.
Its indicator specialization gives

$$
\sum_{k\ge0}\left|\mathbb P(W=k)
-e^{-\lambda}\frac{\lambda^k}{k!}\right|
\le 2\sum_i p_i^2.
$$

For the half-variation convention $d_{\rm TV}=\sup_A|P(A)-Q(A)|$,
the corresponding bound is $\sum_i p_i^2$. Theorem 1 is more general:
it compares a sum of independent rare increments with a compound
Poisson law; the Bernoulli case selects unit increments.

## Native marked counts require a relative bridge

An absolute event error $\delta$ supplies, for a Poisson atom
$\pi_\lambda(k)>0$, only

$$
\left|\frac{\mathbb P(W=k)}{\pi_\lambda(k)}-1\right|
\le\frac{\delta}{\pi_\lambda(k)}.
$$

Thus a small variation distance alone does not control a rare atom's
relative error uniformly in the count. The same issue occurs for
two-row product atoms. A path with overlapping observations also
needs its dependence accounted for before the independent theorem
can apply.

The [parity spectral-boundary volume](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
uses relative one- and two-row comparisons, with actual pair/path
histories, count range $n_\pm\le C_0L$ and an error proportional to
$L^{k+1}/M$ for $k=1,2$. These model-specific relations and their
shared conditioning are not conclusions of Le Cam's theorem.
The paper supplies the classical absolute approximation antecedent;
it does not supply the calibrated posterior's modulo-one small ball.
