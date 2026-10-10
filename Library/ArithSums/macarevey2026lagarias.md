---
bibkey: macarevey2026lagarias
authors: Andrew MacArevey
year: 2026
title: On the Lagarias Inequality and Superabundant Numbers
doi: null
url: https://arxiv.org/abs/2602.15905v2
claim: The preprint proves monotonicity of the continuous Lagarias comparison and reduces a least Lagarias counterexample to a superabundant integer; it does not identify a FIB source with a superabundant or colossally abundant integer and does not prove RH.
strata_touched: []
license: citation-only
triage: anchor
---

# Lagarias monotonicity and the superabundant reduction

The source is Andrew MacArevey, [*On the Lagarias Inequality and Superabundant Numbers*](https://arxiv.org/html/2602.15905v2), arXiv:2602.15905v2, submitted February 2026. The versioned TeX was inspected for the derivative argument and the superabundant reduction. This is a source applicability check, not a journal-proof audit, Lean verification, or claim of a new RH proof.

## The comparison function

Lagarias's criterion is

$$
\sigma(n)\le H_n+e^{H_n}\log H_n
\qquad(n\ge1),
$$

which is equivalent to RH. The preprint extends the harmonic numbers by

$$
H(x)=\psi(x+1)+\gamma
$$

and sets

$$
L(x)=\frac{H(x)+e^{H(x)}\log H(x)}{x}.
$$

Its Lemmas 1--5 use the trigamma series and integral comparisons to obtain

$$
\log(x+1)\le H(x)\le1+\log x,
\qquad
H'(x)\ge\frac1{x+1}
$$

for $x\ge1$, then lower-bound the numerator of $L'(x)$ by

$$
G(x)=\frac{x}{x+1}-(1+\log x)
 +\frac{x}{1+\log x}-\log(1+\log x).
$$

For $x\ge e^4$, the elementary estimate
$e^{\log x}\ge2(\log x)^2+3\log x+1$ gives $G(x)>0$. Hence
$L'(x)>0$ on that range. The paper then checks the finite cases
$1\le n\le54$ and concludes that

$$
B_n=\frac{H_n+e^{H_n}\log H_n}{n}
$$

is strictly increasing. An independent 80-digit decimal recomputation gives a positive minimum finite gap at $n=54$,

$$
B_{55}-B_{54}>0.0054605819041062294681,
$$

but this numerical check is not a Lean certificate.

## The superabundant reduction

Suppose $m$ is the least counterexample to the Lagarias inequality. If $m$ is not superabundant, choose the greatest superabundant $n<m$ and use

$$
\frac{\sigma(n)}n\ge\frac{\sigma(m)}m,
\qquad B_n<B_m.
$$

Then failure at $m$ implies failure at $n$, contradicting minimality. Thus a least counterexample, if one exists, is superabundant. This is a reduction of the search class; it does not establish the inequality on that class.

## Boundary for the FIB route

Superabundance is defined by the multiplicative ordering of $\sigma(n)/n$ over all smaller integers. A FIB ATOM address such as

$$
[null,2,3,2\,5,5]
$$

records additive Zeckendorf inclusion and window adjacency. It gives no prime factorization, valuation vector, $\omega(n)$ bound, or comparison against every smaller integer. Therefore the preprint cannot be applied to a FIB-generated family without a new arithmetic bridge proving that the same integer is superabundant (or reducing further to a valid CA source).

The result is useful as a non-duplicative candidate-class filter for the Lagarias formulation. It supplies no signed Robin tail estimate, no FIB-to-divisor-sum transport, and no RH proof.
