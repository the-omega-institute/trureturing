---
bibkey: thornerzaman2019chebotarev
authors: Jesse Thorner and Asif Zaman
year: 2019
title: A unified and improved Chebotarev density theorem
doi: 10.2140/ant.2019.13.1039
url: https://msp.org/ant/2019/13-5/ant-v13-n5-p02-s.pdf
claim: Theorem 1.4 gives an unconditional effective relative-error prime count at polynomial conductor scale; its quadratic inert class supplies negative-character primes in a terminal dyadic interval with ramified zeros retained.
strata_touched: []
license: citation-only
triage: anchor
---

# Quadratic inert-prime supply at polynomial conductor scale

The published article is *Algebra & Number Theory* **13** (2019),
1039–1068, [DOI:10.2140/ant.2019.13.1039](https://doi.org/10.2140/ant.2019.13.1039).
The inspected primary statements are Theorem 1.1, printed p.1040, and
Theorem 1.4 with parameter (1-11), printed p.1042, in the
[journal PDF](https://msp.org/ant/2019/13-5/ant-v13-n5-p02-s.pdf).
The corresponding preprint is [arXiv:1803.02823v3](https://arxiv.org/abs/1803.02823v3).
This note applies the published theorem; it does not reproduce its
analytic proof or supply Lean verification, numerical onset constants,
or a claim that this is the strongest available interval theorem.

Let $\chi$ be a real nonprincipal primitive quadratic character of
conductor $q\ge3$, corresponding to the quadratic field
$L=\mathbb Q(\sqrt\Delta)$ with signed fundamental discriminant
$|\Delta|=q$. In Theorem 1.4 take $F=K=\mathbb Q$,
$H=G=\operatorname{Gal}(L/\mathbb Q)$, and the nontrivial singleton
Frobenius class. Its parameters are $D_K=n_K=1$ and $Q(L/K)=q$.
The count is precisely

$$
\pi_-(x)=\#\{p\le x:\chi(p)=-1\}.
$$

Ramified primes remain zeros and are absent from this count. The theorem
supplies absolute effective constants $a,c>0$ and an absolute effective
implied constant such that, for $x\ge q^a$,

$$
\pi_-(x)=M(x)\left(1+O\left(
e^{-c\log x/\log q}+e^{-\sqrt{c\log x}}\right)\right).
\tag{T1}
$$

Here $M(x)=\operatorname{Li}(x)/2$ without an exceptional zero, and
$M(x)=[\operatorname{Li}(x)+\operatorname{Li}(x^{\beta_1})]/2$ if
one exists. Since $\zeta(s)$ has no real zero in $(0,1)$, the exceptional
character in this quadratic extension is the nontrivial character.
Thus Theorem 1.4 has $\theta_1=-1$ on the inert class, giving the plus
sign. No RH or GRH hypothesis is used.

## The interval consequence needed by an actual CA source

There are absolute effective constants $C\ge1$ and $x_0$ such that every
such character and every $x\ge\max\{x_0,q^C\}$ satisfy

$$
\pi_-(x)-\pi_-(x/2)\ge\frac{x}{8\log x}.
\tag{T2}
$$

This is a consequence of (T1), not a separately quoted source theorem.
Enlarge $C,x_0$ until (T1) applies at both endpoints and each relative
error is at most $1/64$. Uniformity follows from
$\log(x/2)/\log q\ge C-\log2/\log3$. For sufficiently large $x$,
$\operatorname{Li}(t)\le2t/\log t$ at $t=x,x/2$, so
$M(x)+M(x/2)\le4x/\log x$. Also

$$
M(x)-M(x/2)\ge\frac12\int_{x/2}^{x}\frac{dt}{\log t}
\ge\frac{x}{4\log x}.
$$

The exceptional term is increasing and cannot reduce this difference.
Subtracting the two endpoint errors gives at least
$(1/4-4/64)x/\log x\ge x/(8\log x)$, proving (T2).
The constants are effective existence constants, not computed numerical
thresholds. A least nonresidue below $q^b$, or a prime count accumulated
below that cutoff, would not alone supply this interval conclusion.

The [actual CA application](pollack2017nonresidues.md#the-terminal-ca-prime-band-forces-a-conductor-lower-bound)
uses (T2) only where the same candidate's terminal support has exponent
one. No large-conductor weighted deficit or signed Robin estimate is
supplied by this note.
