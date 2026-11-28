---
bibkey: glampe2026polynomial
authors: Joey Glampe, Aryaman Joshi, Swagat Malla, Matthew Richey, Matthew Wright
year: 2026
title: Polynomial Identities for Generalized Fibonacci Sequences
doi: null
url: https://arxiv.org/abs/2610.15131v1
claim: "Equations (9) and (10) ask which integer-seeded order-two recurrences and positive multipliers k admit an identity expressing G(kn) as a polynomial of degree at most k in G(n), allowing a factor (-1)^n on individual coefficients."
strata_touched:
  - D5/S1/Recurrence/GlampeSixPeriodMultipliers
license: citation-only
triage: anchor
---

# Polynomial identities for generalized Fibonacci sequences

Equation (9) defines the gibonacci recurrence $G_0=a$, $G_1=b$ and
$G_n=rG_{n-1}+sG_{n-2}$ for $n\geq 2$, with integer parameters, $(a,b)\ne(0,0)$,
and $r,s\ne0$. Equation (10) asks when $G_{kn}$ is a polynomial of degree at
most $k$ in $G_n$ whose coefficients may each include a factor $(-1)^n$.
The paper studies polynomial identities via the Girard–Waring formula and
the algebraic roots of the characteristic polynomial.

The repository treats the specialized family $G_0=1$, $G_1=0$,
$(r,s)=(t,-t^2)$ for integer $t$ with $|t|\geq2$. Its rational generating
series is $(1-tx)/(1-tx+t^2x^2)$, as follows by multiplying the generating
series by the recurrence denominator and using the two seeds.
For every positive natural $k$ and every field $K$ of characteristic zero,
the checked result asserts the existence of fixed coefficients in $K$ and
one fixed sign bit per degree, valid at every natural index including zero,
if and only if $k\equiv1\pmod6$. Both recurrence values in the identity are
cast from the integers into $K$. The congruence classification is a
repository-derived result for this family. The general classification of
equation (9) remains open in this development.

## Verified locator

- URL: https://arxiv.org/abs/2610.15131v1
- PDF: https://arxiv.org/pdf/2610.15131v1
- Page 2, equations (9) and (10). Section 5 discusses remaining questions.
