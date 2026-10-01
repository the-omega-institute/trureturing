---
bibkey: hayneswhite2014intervals
authors: Alan Haynes and Christopher J. White
year: 2014
title: Group automorphisms with prescribed growth of periodic points, and small primes in arithmetic progressions in intervals
doi: 10.1016/j.aim.2013.11.014
url: https://arxiv.org/abs/1309.2562v1
claim: Theorem 1.5 gives a prime in every reduced progression inside a fixed-ratio interval beyond modulus exponent 13.4; its direct quadratic-character application gives terminal negative primes for every fixed conductor exponent below 5/67, with an ineffective onset.
strata_touched: []
license: citation-only
triage: anchor
---

# A published progression interval with a numerical exponent

The article appeared in *Advances in Mathematics* **252** (2014),
572–585, [DOI:10.1016/j.aim.2013.11.014](https://doi.org/10.1016/j.aim.2013.11.014).
The inspected primary text is [arXiv:1309.2562v1](https://arxiv.org/abs/1309.2562v1),
Theorem 1.5 on printed p.4 and its proof in §3, especially (3.3) on
p.9. This note reuses the published interval result; its analytic proof
has not been reproduced or Lean-verified here. No optimality or complete
literature-search claim is made.

For every fixed $\kappa>13.4$ and $\varepsilon>0$, every sufficiently
large modulus $m$, every $a$ with $(a,m)=1$, and every $x>m^\kappa$,
Theorem 1.5 supplies a prime

$$
p\equiv a\pmod m,\qquad x\le p<(1+\varepsilon)x.
\tag{H1}
$$

This is an interval theorem, rather than only a least-prime theorem.
The exceptional-zero case of its proof uses Siegel's theorem in (3.3).
No effective onset is claimed for (H1) or the application below.

For a real nonprincipal primitive quadratic character $\chi$ of
conductor $q$, choose a unit class $a$ with $\chi(a)=-1$. Fix
$0<\eta<5/67$ and choose $13.4<\kappa<1/\eta$. Apply (H1) with

$$
m=q,\qquad x=2X/3,\qquad\varepsilon=1/2.
$$

If $q\le X^\eta$, then $q^\kappa\le X^{\eta\kappa}<2X/3$
eventually, uniformly over this conductor range. The supplied prime
lies in $[2X/3,X)\subset(X/2,X]$ and has $\chi(p)=-1$. The finitely
many smaller moduli excluded by the source's threshold are handled by
fixed-modulus prime distribution and enlarging the common onset.
Thus, for every fixed $0<\eta<5/67$, all sufficiently large $X$ and
all such characters with $q\le X^\eta$ have a negative-character
prime in $(X/2,X]$. In particular $\eta=1/14$ is admissible.
The prime is coprime to $q$; ramified zeros are preserved.

The [actual CA conductor application](pollack2017nonresidues.md#a-numerical-exponent-from-the-published-progression-interval)
uses only this interval supply. The
[Thorner–Zaman application](thornerzaman2019chebotarev.md) separately
gives an effective positive conductor exponent and a count, without
numerical values for its constants. Neither interface alone provides
the large-conductor weighted budget needed by Robin.
