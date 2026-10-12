---
bibkey: rabiner1989hiddenmarkov
authors: Lawrence R. Rabiner
year: 1989
title: A tutorial on hidden Markov models and selected applications in speech recognition
doi: 10.1109/5.18626
url: https://www.cs.cmu.edu/~cga/behavior/rabiner1.pdf
claim: "Section III-A, equations (18)–(21), evaluates a complete hidden-state path sum by an initial distribution, a forward recursion and a terminal sum."
strata_touched: []
license: citation-only
triage: anchor
---

# Finite weighted paths and the forward recursion

## Verified locator

DOI: <https://doi.org/10.1109/5.18626> resolves to IEEE's article
18626 with an empty HTTP 202 response; Firecrawl returns HTTP 402.
Crossref identifies the title, author and *Proceedings of the IEEE*
77(2), 257–286. The accessible
[CMU-hosted article scan](https://www.cs.cmu.edu/~cga/behavior/rabiner1.pdf)
is HTTP 200 and has 30 PDF pages. Section III-A, equations
(12)–(21) and the explanation of the forward induction on printed
pp. 262–263 (PDF pp. 6–7), were inspected.

## Classical path-sum computation

For a finite hidden Markov model with initial law $\pi$, transitions
$a_{ij}$ and emission probabilities $b_j$, fixed observations
$o_1,\ldots,o_T$ have forward weights

$$
\alpha_1(i)=\pi_i b_i(o_1),\qquad
\alpha_{t+1}(j)=\left(\sum_i\alpha_t(i)a_{ij}\right)b_j(o_{t+1}),
\qquad
\mathbb P(o_1,\ldots,o_T)=\sum_j\alpha_T(j).
$$

The transition and conditional emission assumptions determine the
joint path product; summing it over the hidden states yields this
recursion. It does not require the successive hidden states to be
independent. The source's emissions are conditionally independent
given that state path.

## Correspondence with the native marked path

Section 120 of the
[spectral-boundary volume](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
uses edge weights $K(x,y)=P(x,y)(1+u_x+v_x\chi(y))$.
These depend on both endpoints and may be complex. They are not
automatically an HMM's one-state emission probabilities. Splitting
each complete path into its prefix and last edge instead gives the
same finite algebraic mechanism,
$p_{t+1}(y)=\sum_xp_t(x)K(x,y)$, without a probability interpretation
for an arbitrary complex tilt.

The original compensated averages, direction of the count factors,
two-coordinate reduction and uniform error bound require the model's
own identities. Forward recursion alone does not identify Poisson
coefficients, give relative count probabilities, or control the
complete posterior center. The tutorial is a method reference, not
a publication of those native estimates or the arithmetic small ball.
