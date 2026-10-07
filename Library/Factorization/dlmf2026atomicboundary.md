---
bibkey: dlmf2026atomicboundary
authors: NIST Digital Library of Mathematical Functions
year: 2026
title: Inversion formulas and divisor Dirichlet series
doi: null
url: https://dlmf.nist.gov/27.5
claim: Divisor accumulation is inverted by the arithmetic Mobius function; divisor power sums have a zeta-product Dirichlet series in its stated absolute-convergence domain.
strata_touched: []
license: citation-only
triage: anchor
---

# Inversion formulas and divisor Dirichlet series

The HTML mathematical alternatives at [§27.5, equation 27.5.3](https://dlmf.nist.gov/27.5#E3)
and [§27.4, equation 27.4.11](https://dlmf.nist.gov/27.4#E11) give the following
two ingredients. They are directly consumed by §§5 and 9 of
[FIB-ATOM](../../docs/develop/theory/AURIC_FIB_ATOMIC_BOUNDARY_CALCULUS.md).

Equation 27.5.3 states, for arithmetic functions on positive integers,

$$
g(n)=\sum_{d\mid n}f(d)
\quad\Longleftrightarrow\quad
f(n)=\sum_{d\mid n}g(d)\mu(n/d).
$$

Changing the divisor variable to $n/d$ gives the equivalent expression
$f(n)=\sum_{d\mid n}\mu(d)g(n/d)$. For $f(n)=1/n$ the cumulative response
is $g(n)=\sigma(n)/n$, since the involution $d\mapsto n/d$ permutes the
divisors. The sixteen-term evaluation at 5040 is an application of this
classical inverse, not a separate inverse theorem attributed to DLMF.

Equation 27.4.11 states

$$
\sum_{n=1}^{\infty}\sigma_\alpha(n)n^{-s}
=\zeta(s)\zeta(s-\alpha),
\qquad \operatorname{Re}s>\max(1,1+\operatorname{Re}\alpha).
$$

For $\alpha=-1$, $\sigma_{-1}(n)=\sigma(n)/n$, and the domain becomes
$\operatorname{Re}s>1$. The local proof of absolute rearrangement in
FIB-ATOM preserves precisely that domain. These references supply neither
critical-strip zero control nor a Robin sign bound over all integers.
No originality, quantum realization, or Lean verification is attested.
