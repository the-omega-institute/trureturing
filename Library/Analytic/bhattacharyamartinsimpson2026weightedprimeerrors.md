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

## A growing-modulus sign average does not supply the individual zeta bound

Suzuki, *On variants of Chebyshev's conjecture*,
[arXiv:2411.07436v3](https://arxiv.org/abs/2411.07436v3),
also studies half-weighted Mangoldt sums. The inspected statements are
Theorems 1 and 7 on printed pp.2 and 8 of that version; its linked DOI is
[10.1007/s11139-025-01238-9](https://doi.org/10.1007/s11139-025-01238-9).
The publisher version and complete source proofs are not independently
checked here. Reuse the source's criterion rather than reprove it.

Put

$$
S_\zeta(x)=\sum_{n\le x}\frac{\Lambda(n)}{\sqrt n}\log\frac xn-4\sqrt x.
$$

Theorem 1 makes RH equivalent to eventual $S_\zeta(x)\le0$ for
**every** real $x\ge x_0$, and also to
$S_\zeta(x)/\log x\to-\zeta'(1/2)/\zeta(1/2)$.
Neither the sign nor this limit is an unconditional conclusion.

For

$$
S_q(x)=\sum_{\substack{n\le x\\n\equiv1\pmod q}}
 \frac{\Lambda(n)}{\sqrt n}\log\frac xn-
 \frac{4\sqrt x}{\varphi(q)},
$$

Theorem 7, equation (29), supplies unconditionally, with $Q\ge x$,

$$
\sum_{3\le q\le Q}\varphi(q)S_q(x)
=4\sqrt x\left[\frac{x}{9}(1+o(1))-Q\right]
\qquad(x\to\infty).
$$

This negative aggregate ranges over growing moduli and explicitly
omits $q=1,2$. It does not assert the sign of $S_\zeta$, or of each
fixed-modulus summand. In this v3, the paragraph following Theorem 7
lists constant-$Q$ or weaker-range negativity as questions for further
study; no effective threshold is supplied here.

At the existing selected Robin source, the real-cutoff comparison would
use $x=A=\log N$, not $x=N$. Even there the prefix kernel
$n^{-1/2}\log(A/n)$ differs from the original $I_\psi$ tail and its
complete zero coefficient. The inspected interfaces have not supplied
a signed transport to that complete functional with its remainder paid.
The stated growing-modulus average does not pay the individual
cross-family bound above or the
complete same-source head-plus-cost requirement in
[the existing heat transport](../ArithSums/nicolas2025comparison.md#the-same-source-price-minimum-gives-a-nonnegative-heat-cost).
The original signed Robin estimate and RH remain unproved; no new
criterion, original theorem or Lean verification is claimed.
