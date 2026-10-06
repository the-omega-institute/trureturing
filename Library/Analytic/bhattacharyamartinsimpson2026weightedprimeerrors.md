---
bibkey: bhattacharyamartinsimpson2026weightedprimeerrors
authors: Shubhrajit Bhattacharya; Greg Martin; Reginald M. Simpson
year: 2026
title: Correlations of error terms for weighted prime counting functions
doi: 10.4064/aa250716-6-5
url: https://doi.org/10.4064/aa250716-6-5
claim: Theorem 1.4(b) bounds the difference of reciprocal and standard normalized prime-counting errors under RH; the Chebyshev pair identifies precisely the project's positive-time primitive but gives no unconditional critical estimate.
strata_touched: []
license: citation-only
triage: anchor
---

# Published weighted-error bound and the actual phase primitive

The inspected primary is the publisher's [72-page Online First PDF](https://www.impan.pl/shop/en/publication/transaction/download/product/116536?download.pdf) of *Acta Arithmetica*, DOI [10.4064/aa250716-6-5](https://doi.org/10.4064/aa250716-6-5). Crossref records online publication on 10 September 2026; the [publisher landing page](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/online/116536/correlations-of-error-terms-for-weighted-prime-counting-functions) gives the authors, title, journal, DOI and pp.1–72. No volume or final paginated issue is asserted. The numbering below was checked in the publisher PDF.

## Unconditional transform suppliers

Lemma 3.10, printed p.20, and Lemma 3.14, printed p.23, give respectively, for $\Re z>1$,

$$
\int_2^\infty\psi(x)x^{-z-1}dx
=-\frac{\zeta'(z)}{z\zeta(z)},\qquad
\int_2^\infty\psi_r(x)x^{-z}dx
=\frac{\zeta'(z)}{(1-z)\zeta(z)}.
$$

Here $\psi_r(x)=\sum_{n\le x}\Lambda(n)/n$. Both counting functions vanish for $1<x<2$, so the lower endpoint can be changed to $1$. These are existing Mellin identities, reused without reproducing their proofs. They do not supply a bound on the signed error.

## Exact conditional quantitative match

Definitions 1.2–1.3 use

$$
E^\psi(x)=\frac{\psi(x)-x}{\sqrt x},\qquad
E^{\psi_r}(x)=\sqrt x\,[\psi_r(x)-\log x+\gamma],
\qquad\beta_\psi=\beta_{\psi_r}=0.
$$

Theorem 1.4(b), printed p.5, explicitly assumes RH and gives lower and upper asymptotic bounds for the difference of a reciprocal and a standard error, centered at the bias difference, with allowance

$$
w=2+\gamma-\log(4\pi)=0.0461914\ldots.
$$

LI is not needed for these bounds. Remark 1.5 invokes LI additionally for equality of the limiting extrema; that stronger statement is not used here. The theorem's proof on printed p.15 also displays the $\psi,\psi_r$ comparison directly.

The [classical primitive identity](lay2015mertenssignchanges.md) and the [FIB source correspondence](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md), §415, give exactly

$$
\sqrt x\,h(\log x)=E^\psi(x)-E^{\psi_r}(x).
$$

Consequently, direct application of the existing theorem supplies

$$
\text{assuming RH},\qquad
\limsup_{u\to\infty}e^{u/2}|h(u)|\le w.
$$

The reversal of the source's reciprocal-minus-standard order changes the sign, and the two-sided allowance remains $w$. This is an exact match for the actual primitive, not a new decay theorem. It is asymptotic, with no explicit finite threshold asserted. Its RH premise prevents use as an unconditional supplier for proving RH or full Robin. Neither the unconditional transform identities nor a FIB change of coordinates removes that premise; no Lean verification is claimed.

## The signed Robin tail is an already-published cross-family race

Definition 1.1, printed pp.3–4, distinguishes the prime-power cutoff
$\Pi_r(x)=\sum_{p^k\le x}1/(kp^k)$ from the logarithm of the Euler product
$\pi_\ell(x)=\sum_{p\le x}\sum_{k\ge1}1/(kp^k)$. For the
[project's original signed tail](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md), §87.3,
use $P=\Pi_r$, not $\pi_\ell$. Definition 1.2 then gives directly

$$
E^{\Pi_r}(x)=\sqrt x\log x\,[P(x)-\log\log x-\gamma],
\qquad
\sqrt x\log x\,I_\psi(x)=E^\psi(x)-E^{\Pi_r}(x).
$$

These are parameter substitutions into the existing finite tail identity,
not a new integral or a new RH criterion. Lemma 3.1, printed p.16, supplies
unconditionally

$$
A(x):=E^\psi(x)-E^\theta(x)
=1+O(e^{-c\sqrt{\log x}}),\qquad c>0.
$$

Let $D(x)=E^{\Pi_r}(x)-E^\theta(x)$. Thus the same source data obey

$$
\sqrt x\log x\,I_\psi(x)=A(x)-D(x).
$$

Definition 1.3 gives $\beta_\theta=-1<\beta_{\Pi_r}=0$.
The pair $(\theta,\Pi_r)$ is outside all five excluded pairs in (1.2).
Consequently Theorem 1.6(b), printed p.6, already makes RH equivalent to
an eventual upper bound, or an eventual lower bound, for this $D$.
Since $A\to1$ unconditionally, an eventual finite lower bound for the
normalized original $I_\psi$ is precisely the upper-bound direction of
that published criterion. The project's §92.3 one-sided criterion is
therefore reused; its Landau argument is not reproduced as new work.
The unconditional within-family comparisons in Theorem 1.6(a) and
Lemmas 3.1–3.3 do not provide this cross-family upper bound.

The actual same-price reserve in §87.3 also transports without changing
its meaning. Put $r(x)=\sqrt x\log x\,R(x)$. For the unconstrained
pressure and its original $\lambda_x=1/(x\log x)$, the existing identity
$\Delta(\lambda_x)=I_\psi(x)+R(x)$ says exactly

$$
\Delta(\lambda_x)\ge0
\quad\Longleftrightarrow\quad
D(x)\le A(x)+r(x).
$$

All terms refer to the same real cutoff and actual optimal pressure;
no independently chosen prime or reciprocal extremum is combined here.
The project's §93.2 supplies $r(x)\to2(\sqrt2-1)$ unconditionally.
Theorem 1.4(b) supplies $\limsup D(x)\le1+w$ only **under RH**.
This restates the already-paid conditional comparison of §94.5, with
no effective starting threshold. The source's eventual ordering
$E^\theta<E^{\Pi_r}$ is a lower bound on $D$; it must not be used as a
lower bound on $I_\psi=A-D$.

The missing supplier is an unconditional upper comparison for this same
realized $D$ against $A+r$ at all required scales. The transform formulas,
prime-power biases and coordinate correspondence identify that obligation
but do not pay it. No new general criterion, finite verification range,
Lean theorem or proof of Robin/RH is asserted by this source application.
