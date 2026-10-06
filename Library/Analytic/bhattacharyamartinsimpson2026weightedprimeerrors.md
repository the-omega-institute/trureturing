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

The [classical primitive identity](lay2015mertenssignchanges.md) and the [FIB source correspondence](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md), §414, give exactly

$$
\sqrt x\,h(\log x)=E^\psi(x)-E^{\psi_r}(x).
$$

Consequently, direct application of the existing theorem supplies

$$
\text{assuming RH},\qquad
\limsup_{u\to\infty}e^{u/2}|h(u)|\le w.
$$

The reversal of the source's reciprocal-minus-standard order changes the sign, and the two-sided allowance remains $w$. This is an exact match for the actual primitive, not a new decay theorem. It is asymptotic, with no explicit finite threshold asserted. Its RH premise prevents use as an unconditional supplier for proving RH or full Robin. Neither the unconditional transform identities nor a FIB change of coordinates removes that premise; no Lean verification is claimed.
