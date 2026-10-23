---
bibkey: teschl2000jacobi
authors: Gerald Teschl
year: 2000
title: Jacobi Operators and Completely Integrable Nonlinear Lattices
doi: null
url: https://www.mat.univie.ac.at/~gerald/ftp/book-jac/jacop.pdf
claim: Bounded selfadjoint Jacobi operators admit half-line Green functions, a Riccati relation, and cyclic spectral-moment descriptions under the specified boundary and coefficient hypotheses.
strata_touched: []
license: citation-only
triage: anchor
---

# Half-line endpoint response

The source is *Mathematical Surveys and Monographs* 72, AMS, using the
[author-corrected online version of 24 August 2017](https://www.mat.univie.ac.at/~gerald/ftp/book-jac/jacop.pdf).
Section 1.1, Hypothesis H.1.4 and Theorem 1.5, p. 13, gives the bounded
selfadjoint operator setting. Lemma 1.8, p. 15, and equations (1.90)–(1.95),
p. 16, treat half-line Green functions. Section 2.1, pp. 27–29,
equations (2.1), (2.7)–(2.11), supplies the Weyl function and Riccati
relation. Section 2.5, pp. 40–41, equations (2.94)–(2.98) and Theorem 2.12,
connects cyclic vectors, spectral moments and polynomial Gram data.
The coefficients are real and bounded, with nonzero off-diagonals and a
specified half-line boundary.

[The Static continuation, Theorems 29.8–29.9](../../docs/develop/theory/AURIC_FIB_ATOM_STATIC_SEAMS_TRANSITION_CIRCULATION_AND_FIBONACCI_TOGGLE_CYCLES.md)
uses the half-line Dirichlet operator with $a=-1$, $b=3$, $z=-s$,
$s\ge0$. Its independently displayed coercivity puts $z$ outside the
spectrum. Alternating-sign conjugation changes the off-diagonal signs and
fixes the endpoint. The application selects the smaller Riccati root by
$0<r\le1/(s+1)\le1$; positivity alone would not select it.
The finite tridiagonal determinant recurrence and continued fraction are
intermediate computations, not new general Jacobi results.

The finite spectral decomposition in Theorem 29.2 groups repeated rates
by whole spectral projections. Extracting coefficients at distinct rates
uses finite Vandermonde algebra. The cited spectral method does not assert
that one static cancellation removes every cross response.
The application's positive path comparison and sharp all-time input error
are supplied in its own proof; they are not attributed to a quoted theorem
of this book. No pages or figures are reproduced.
