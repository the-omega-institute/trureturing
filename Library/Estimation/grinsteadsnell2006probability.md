---
bibkey: grinsteadsnell2006probability
authors: Charles M. Grinstead and J. Laurie Snell
year: 2006
title: Grinstead and Snell's Introduction to Probability
doi: null
url: https://math.dartmouth.edu/~prob/prob/prob.pdf
claim: "Section 4.1 gives finite conditional probability and Bayes' formula; Theorem 8.1 gives the discrete Chebyshev inequality."
strata_touched: []
license: citation-only
triage: anchor
---

# Finite Bayes denominators, odds and Chebyshev tails

## Verified locator

The [Dartmouth CHANCE Project PDF](https://math.dartmouth.edu/~prob/prob/prob.pdf)
is HTTP 200 and has 518 PDF pages. Its title page identifies the
authors' text and version dated 4 July 2006. This version date
distinguishes the online text from the original 1997 book.
Section 4.1, “Discrete Conditional Probability,” including its
“Bayes' Formula” subsection, and Theorem 8.1 on printed p. 305
(PDF p. 313), were inspected. No DOI is asserted for this online version.

## Classical finite conditional law

For $\mathbb P(E)>0$,
$\mathbb P(H\mid E)=\mathbb P(H\cap E)/\mathbb P(E)$.
For a finite partition $H_1,\ldots,H_m$ with positive prior masses,
Bayes' formula is

$$
\mathbb P(H_i\mid E)
=\frac{\mathbb P(H_i)\mathbb P(E\mid H_i)}
{\sum_j\mathbb P(H_j)\mathbb P(E\mid H_j)}.
$$

When both posterior probabilities in a ratio are positive,

$$
\frac{\mathbb P(H_i\mid E)}{\mathbb P(H_j\mid E)}
=\frac{\mathbb P(H_i)}{\mathbb P(H_j)}
\frac{\mathbb P(E\mid H_i)}{\mathbb P(E\mid H_j)}.
$$

This odds identity is a direct cancellation in the displayed Bayes
formula. Null conditioning events and zero denominator odds are
excluded rather than divided through.

For a uniformly chosen support of fixed size $q$ and positive site
likelihood factors $L_i$, the same formula gives a posterior
proportional to $\prod_{i\in S}L_i$ on $|S|=q$. Its marginal is

$$
\pi_i=\frac{L_i e_{q-1}(L_j:j\ne i)}{e_q(L_j:j\in C_+)}.
$$

This is the finite Bayes application used in equation (116.49) of
the [spectral-boundary volume](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md).
The site factors, likelihood law and fixed-size prior must refer to
the same experiment. The formula does not make posterior indicators
independent or replace their shared symmetric-polynomial denominator
by independent Bernoulli normalizers.

## Classical tail inequality

Theorem 8.1 states, for a discrete variable of finite variance and
$a>0$, $\mathbb P(|X-\mathbb EX|\ge a)\le\operatorname{Var}(X)/a^2$.
Together with the exact hypergeometric variance this supplies the
$L^{-2}$ tail used in the rectangle small-ball decomposition.
It gives an upper tail bound, not a lower probability, maximum-atom
bound or anti-concentration theorem for a moving posterior mean.
