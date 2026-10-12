---
bibkey: siegrist2026hypergeometric
authors: Kyle Siegrist
year: 2026
title: The Hypergeometric Distribution
doi: null
url: https://www.randomservices.org/random/urn/Hypergeometric.html
claim: "The online finite-sampling chapter gives the hypergeometric mass function, adjacent-mass ratio, tied modes, mean and finite-population-corrected variance."
strata_touched: []
license: citation-only
triage: anchor
---

# The rectangle kernel, its modes and its second moment

## Verified locator

The [author-maintained chapter](https://www.randomservices.org/random/urn/Hypergeometric.html)
is HTTP 200 and identifies itself as *Random*, chapter 11, section 2,
“The Hypergeometric Distribution.” Its “The Probability Density
Function” and “Moments” sections were inspected, including the
unimodality paragraph, adjacent-mass ratio, mean and variance.
The chapter is undated; 2026 is the citation year, not an asserted
initial publication year. No DOI is assigned in the note.

## Classical finite-sampling formulas

Use population size $N>0$, marked population $R\le N$, and sample
size $U\le N$. Uniform sampling without replacement gives

$$
p(t)=\frac{\binom Rt\binom{N-R}{U-t}}{\binom NU},\qquad
\max(0,R+U-N)\le t\le\min(R,U).
$$

For positive neighboring masses,

$$
\frac{p(t+1)}{p(t)}
=\frac{(R-t)(U-t)}{(t+1)(N-R-U+t+1)}.
$$

Set $v=(R+1)(U+1)/(N+2)$. The mode is $\lfloor v\rfloor$
when $v$ is not an integer; when $v$ is an integer, both $v-1$
and $v$ are modes, restricted to the support. This includes ties
and degenerate sampling parameters. For $N>1$,

$$
\mathbb ET=\frac{UR}{N},\qquad
\operatorname{Var}T
=U\frac RN\left(1-\frac RN\right)\frac{N-U}{N-1}.
$$

The factor $(N-U)/(N-1)$ is essential for sampling without replacement.
The degenerate population $N=1$ is deterministic and treated separately.

## Correspondence and limits

The [parity spectral-boundary application](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
conditions on a four-cell rectangle with both margins fixed.
Its scalar varying cell has the same kernel after the actual
conditional-history weights are identified. The formulas above
give neither that conditional-history identification nor the
posterior's shared calibration response.

Combining this variance with the classical
[Chebyshev inequality](grinsteadsnell2006probability.md) gives the
population-scale tail $\mathbb P(|T-UR/N|>L\sqrt N)\le1/(4L^2)$
for $L>0$, since the variance is at most $N/4$.
That is a classical consequence, not a new probability estimate.
The uniform balanced maximum-atom bound additionally needs a local
or distribution-function approximation, as in
[Lahiri–Chatterjee–Maiti](lahirichatterjeemaiti2007hypergeometric.md).
Neither tail control nor mode location alone establishes that bound.
