---
bibkey: rivin2026permanents
authors: Igor Rivin
year: 2026
title: "Permanents of matrix ensembles: computation, distribution, and geometry"
doi: null
url: https://arxiv.org/abs/2602.10141v3
claim: "Open Problems 2 and 3: the midpoint formula and a closed form for the universal function."
strata_touched:
  - D5/S3/Combinatorics/Permanental/CycleGeodesic
license: citation-only
triage: anchor
---

## Verified locator

Source: https://arxiv.org/abs/2602.10141v3

## Source statements

Page 19, Section 8.4, Open Problem 2:

> Prove the midpoint formula $\operatorname{perm}(\gamma(\frac12))=(-1)^{(n-1)/2}\cdot 2e^{-n}(1+\frac{1}{3n}+O(n^{-2}))$.

Page 19, Section 8.4, Open Problem 3:

> Find a closed form for the universal function $f(t)$.

Page 7, Section 4.1:

> The geodesic $\gamma(t)$ is therefore a circulant matrix with explicit entries

$$\gamma(t)_{jl}=\frac{e^{2\pi it}-1}{n\bigl(e^{2\pi i(l-j+t)/n}-1\bigr)}.$$

Page 7, Observation 4:

> Define $f(t)=-\frac{1}{n}\ln|\operatorname{perm}(\gamma(t)).|$. Then $f(t)$ converges to a universal function of $t$ as $n\to\infty$, with the properties:

The printed full stop inside the absolute value is a typographical artifact. The logarithm is taken of the complex norm of the literal permanent. The matrix indices are zero-based elements of `Fin n`; they are cast to real numbers before subtraction.

Page 8, Observation 5 specifies the odd-dimensional midpoint expansion and the even-dimensional permanent zero. At the midpoint the scaling limit is therefore taken along odd dimensions. The all-dimension nonmidpoint limit is on $0<t<1$, $t\ne1/2$.

## Closed form and range

With $\delta=\min(t,1-t)$, the universal function on the interior is
$1-\pi\delta\cot(\pi\delta)$. Reflection symmetry follows from the definition of $\delta$; its continuous extension is zero at the endpoints, its midpoint value is one, and its onset is $\pi^2t^2/3$. The formal settling statement proves the interior rate limit and the odd-dimensional midpoint limit; those other analytic consequences are follow-up deductions rather than additional Lean assertions in the settling module.

## Literature scope

The exact finite product specializes Han's Scott identity. The connection of that identity to the literal cycle-geodesic matrix, with a second-order Stirling estimate and logarithmic integral, supplies the two answers. The bounded title, identifier and phrase searches recorded in issue #13612 report no subsequent explicit settlement; this is a bounded literature finding, not a global novelty certificate.
