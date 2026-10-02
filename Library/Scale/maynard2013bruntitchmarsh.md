---
bibkey: maynard2013bruntitchmarsh
authors: James Maynard
year: 2013
title: On the Brun-Titchmarsh theorem
doi: 10.4064/aa157-3-3
url: https://arxiv.org/pdf/1201.1777v2
claim: Published Theorem 3.2 supplies an effective uniform lower prime count for q at least q0, reduced classes and x at least q to the eighth power; its negative-class sum is reused in the linked, branch-restricted actual-CA application.
strata_touched: []
license: citation-only
triage: anchor
---

# Pointwise progression counts for the actual CA capacity

The inspected primary sources are the [published article](https://www.impan.pl/shop/publication/transaction/download/product/83060?download.pdf),
*Acta Arithmetica* **157** (2013), no.3, 249–296,
[DOI:10.4064/aa157-3-3](https://doi.org/10.4064/aa157-3-3), and
[arXiv:1201.1777v2](https://arxiv.org/abs/1201.1777v2), dated 21 May 2012.
The lower count is published Theorem 3.2, printed p.251, corresponding
to manuscript Theorem 2, printed p.3. Published equations (3.8) and
(3.11), printed pp.253–254, give the exceptional-zero and ordinary cases
and the effective constants. The theorem is reused, without reproducing
its analytic proof. No independent full proof audit, Lean verification,
or strongest-available-result claim is made.

## The published lower count

There are absolute effective constants $q_0\ge3$ and $c_0>0$ such that
every integer $q\ge q_0$, every reduced class $a\bmod q$, and every real
$x\ge q^8$ satisfy

$$
\pi(x;q,a)\ge
c_0\frac{\log q}{\sqrt q}\frac{x}{\varphi(q)\log x}.
\tag{M1}
$$

This is published Theorem 3.2 (manuscript Theorem 2), with its implied constant written as $c_0$. No GRH,
exclusion of exceptional real zeros, prime-modulus hypothesis or bounded
cubic-part condition is imposed. Published Theorem 3.3 has a different, ineffective
$q^{-\varepsilon}$ factor; it is not substituted for (M1). Published Theorem 3.1 is
an upper bound and is not used as the required lower supply.

Let $\chi$ be any real nonprincipal Dirichlet character modulo $q$,
primitive or imprimitive, and define

$$
\pi_-(x;\chi)=\#\{p\le x:\chi(p)=-1\}.
$$

On the unit group, $\chi$ is a surjection to $\{1,-1\}$, so exactly
$\varphi(q)/2$ reduced classes have value $-1$. Those classes are
disjoint. Summing the same uniform lower bound (M1), rather than giving
each class an independent copy of the prime population, yields

$$
\boxed{\pi_-(x;\chi)\ge
\frac{c_0}{2}\frac{x\log q}{\sqrt q\log x}}
\qquad(q\ge q_0,\ x\ge q^8).
\tag{M2}
$$

Primes dividing $q$ remain zeros and occur in none of these classes.
This is an application of the published theorem, not a new analytic
estimate or an originality claim.

The [actual-source application](pollack2017nonresidues.md#the-progression-count-crosses-the-deep-layer-capacity)
uses (M2) at $x=P^+(n)$, comparing it with the number of primes whose
CA exponent could be even at that same integer. It needs no promotion
of an unweighted prime count to reciprocal-prime mass. Conductors with
$q^8>P^+(n)$ are outside this supplier's range; it gives no signed Robin
estimate there.
