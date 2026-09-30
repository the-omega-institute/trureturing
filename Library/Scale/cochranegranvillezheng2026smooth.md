---
bibkey: cochranegranvillezheng2026smooth
authors: Todd Cochrane, Andrew Granville, and Junren Zheng
year: 2026
title: Mixed incomplete character sums of rational functions with smooth moduli
doi: 10.48550/arXiv.2601.10927
url: https://arxiv.org/pdf/2601.10927v1
claim: Corollary 2 gives short character-sum cancellation for a specified smooth-modulus class, with an exceptional integer and a length threshold; the stated parameter uniformity does not reach logarithmic intervals for general moving moduli.
strata_touched: []
license: citation-only
triage: anchor
---

# Smooth-modulus character sums and the actual cutoff obligation

The inspected source is [arXiv:2601.10927v1](https://arxiv.org/abs/2601.10927v1),
submitted 16 January 2026. Theorem 1 and the parameter-uniformity paragraph
are on p.2; Corollary 2 is on p.3. This note checks those statements and
their applicability, not the full proof. It treats this version as a
preprint and claims no Lean verification or complete current survey.

## The source's actual class and hypotheses

The paper defines $\mathcal N(y)$ as the positive integers with at most
one prime factor in $(y,y^2]$, with all other prime-power divisors at most
$y$. Smoothness of the radical alone is not this condition.

Corollary 2 states that for each fixed $\delta,\varepsilon>0$ there are
$\eta=\eta(\delta,\varepsilon)>0$ and an explicitly determinable positive
integer $\mathcal M=\mathcal M(\delta)$ such that, if

$$
y=q^\delta,\qquad q\in\mathcal N(y),\qquad (q,\mathcal M)=1,
$$

then every nonprincipal character $\chi$ modulo $q$ and every interval
$I$ of length $H$ with $q\ge H\ge y^{1+\varepsilon}$ satisfy

$$
\left|\sum_{n\in I}\chi(n)\right|\ll H^{1-\eta}.
$$

The implicit constant depends on the fixed parameters. The character
need not be primitive. Theorem 1 treats mixed sums of rational functions;
its exceptional low-degree case explicitly uses the **primitive
conductor**, rather than automatically giving a saving in the full
modulus. No numerical value of $\eta$ or onset threshold is certified here.

The p.2 paragraph says that their developed proof permits
$\delta\to0$ only with $\delta\gg1/\log\log q$. For such a choice the
length requirement still has scale at least

$$
H\ge\exp\left(c\frac{\log q}{\log\log q}\right)
$$

for a positive constant in that parameter regime. At $q$ comparable to
the target integer $N$, setting $H=\log N$ would instead require
$\delta\le\log\log N/((1+\varepsilon)\log q)$, below this stated
uniformity range. This is a limitation of the cited application, not a
lower bound for every actual character sum.

## FIB interfaces still required

The [FIB theory volume](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
§§181,182,202 retains the actual conductor, induced zero-character primes
and multiplier costs. It has no all-source result placing the actual
moduli in $\mathcal N(q^\delta)$ or proving their coprimality with
$\mathcal M$. Its bound $q_D<4N/g^2$ alone supplies neither those
conditions nor the needed length comparison.

Character-sum cancellation also needs a justified sieve or other bridge
before it supplies the reciprocal-prime mass missing from the same actual
integer. The [Bourgain–Lindenstrauss weighted theorem](bourgainlindenstrauss2003entropy.md)
already supplies one such established input in its stated restricted range.
The present source should be reused if an actual FIB family meets its
hypotheses; reproving its smooth-modulus estimates does not fill these
family-specific obligations or settle general Robin and RH.
