---
bibkey: zimov2025leastca
authors: Bruce Zimov
year: 2025
title: On the Least Colossally Abundant Exception to Robin's Inequality
doi: null
url: https://arxiv.org/abs/2510.23889v1
claim: The preprint claims that, if RH is false, the least colossally abundant Robin counterexample lies in a narrow asymptotic excess band; this band is much wider than the explicit FIB §250 gap and does not identify a FIB source.
strata_touched: []
license: citation-only
triage: anchor
---

# On the Least Colossally Abundant Exception to Robin's Inequality

The source is [arXiv:2510.23889v1](https://arxiv.org/pdf/2510.23889v1), submitted 27 October 2025. This card records the stated result and its hypotheses; it is a preprint and was not independently audited or formalized here.

Write

$$
G(n)=\frac{\sigma(n)/n}{\log\log n}.
$$

Using the classical reduction to consecutive colossally abundant numbers, their prime or semiprime quotients, and Robin's oscillation theorem under $\lnot\mathrm{RH}$, Theorem 8 claims that the least CA counterexample satisfies

$$
e^\gamma<G(n)<e^\gamma\left(1+\frac{c}{(\log n)^b}\right),
\qquad 0<b<\frac12,
$$

for a positive constant $c$ depending on the chosen $b$. The paper distinguishes this least CA counterexample from the least integer counterexample; the former is a sufficient test set only through the classical CA reduction.

## Relation to the current FIB estimates

The upper band is of order $(\log n)^{-b}$, whereas the explicit §250 same-source gap is of order $1/(\sqrt n(\log n)^3)$. These scales do not contradict one another, and the band does not control the signed $\Phi$ term in the FIB decomposition. Applying it would additionally require proving that a FIB candidate is CA and that the consecutive-CA quotient is the same source used by the FIB price model. Neither implication follows from a five-window address or its congruence.
