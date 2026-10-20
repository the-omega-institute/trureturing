---
slug: jain-2017-abs-cosine-hadamard-power-multiplicity-two
bibkey: jain2017hadamard
doi: 10.1016/j.laa.2016.06.030
url: https://doi.org/10.1016/j.laa.2016.06.030
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/JainAbsCosine/Defs.claim
---

# Jain: multiplicity two for absolute-cosine Hadamard powers

## Problem

Tanvi Jain, *Hadamard powers of some positive matrices*, Linear Algebra
and its Applications 528 (2017), 147–158, states in the final
unnumbered paragraph of section 3, after the proof of Theorem 3.3:

> We conjecture that the multiplicity of every nonzero eigenvalue of |C|∘r∘ (except the top eigenvalue) equals two.

For every natural m at least one, put n=2m+1 and
C_ab=cos((a-b)pi/n), with a,b from zero through n-1. The conjecture
concerns the matrix A(r) whose entries are |C_ab|^r for every real
r at least zero. Every nonzero characteristic-polynomial root other
than the top Fourier value must have algebraic multiplicity exactly
two. The formal definition `Defs.claim` retains all these quantifiers
and both exceptions.

The sentence is attributed to the publisher's indexed full text. The
journal PDF was inaccessible, so its page number is unverified.
The first version of arXiv:1803.06803 omits this sentence; the journal
article is the source of the conjecture.

## Motivation

Reflection pairs the nonconstant Fourier modes of an odd real
symmetric circulant matrix. This forces at least two occurrences of
each representative, but does not exclude coincidences between
different representatives. Jain's sign and inertia conclusions leave
that separation question open.

## Gap

Positive semidefiniteness, inertia, and the sign of an individual
Fourier value do not separate two values of the same sign. The
rank-two simplicity theorem for entrywise-positive positive
semidefinite matrices does not apply: the cosine matrix has negative
entries, and its entrywise absolute value need not have rank two.
The truncated-cosine Jain–Karlin–Schoenberg kernel differs from the
periodic absolute-cosine kernel here.

## Route

Put theta=pi/(2m+1), x_l=cos(l theta), and

$$
\lambda_j(r)=1+2\sum_{l=1}^m\cos(2jl\theta)x_l^r,
\qquad P_j(r)=\prod_{s=0}^{j-1}(r-2s).
$$

The bases satisfy 1>x_1>...>x_m>0. A generalized Descartes bound
for real exponential sums, the exact trigonometric coefficient
variation counts, and the forced zeros at 0,2,...,2j-2 give

$$
\operatorname{sgn}\lambda_j(r)=\operatorname{sgn}P_j(r),\qquad
\operatorname{sgn}(\lambda_j(r)-\lambda_{j+d}(r))
=\operatorname{sgn}P_j(r),\quad d\in\{1,2\}.
$$

The first identity has 1 at most j at most m. The second has j at
least one, d equal to one or two, and j+d at most m. Both hold for
every real r, including composite odd orders and zero intermediate
gap coefficients. Steps one and two separate representatives within
each sign class. Direct positivity of the cosine deficit separates
the top mode. The real symmetric circulant factorization is

$$
\chi_{A(r)}(z)=(z-\lambda_0(r))
\prod_{j=1}^m(z-\lambda_j(r))^2.
$$

Exactly one squared factor corresponds to a nonzero non-top root.

The analytic route to the spectral gap sign identities was derived
with the assistance of the ChatGPT Pro model.

## Falsifier

A counterexample would be an odd order at least three, a nonnegative
real exponent, and a nonzero non-top characteristic-polynomial root
whose multiplicity differs from two. A coincidence of distinct
nonzero Fourier representatives would contradict the separation
step. The zero-eigenvalue example below does not meet these
conditions.

## Evidence

The formal development uses the exponential-sum Descartes theorem,
trigonometric sign counts, forced even roots, exact gap signs,
separation, and the real circulant characteristic-polynomial
factorization. [GapSigns](../D5/S3/Quantum/Matrix/JainAbsCosine/GapSigns.lean)
proves both all-real sign identities;
[Separation](../D5/S3/Quantum/Matrix/JainAbsCosine/Separation.lean)
proves the all-real mode separation statements; and
[Result](../D5/S3/Quantum/Matrix/JainAbsCosine/Result.lean)
proves the exact claim. The numerical tests below provide a separate
finite check.

## Triage

- PROVED (formalized): the exact sign formulas for every real r, strict top-mode separation and injectivity of nonzero Fourier representatives for every real r, and algebraic multiplicity exactly two for every nonzero non-top eigenvalue at every nonnegative real r.
- PROVED (formalized): the generalized Descartes bound and exact sign theorem for real exponential sums; the odd real symmetric circulant characteristic-polynomial factorization; the trigonometric coefficient variation counts and low-even-exponent forced zeros.
- PROVED (paper proof, not formalized here): the multiplicity conclusion for negative r follows by the alternating mode signs and the step-two gap inequalities.
- PROVED (paper proof): the nonzero exception is necessary. At n=7 and r=2 the spectrum is 7/2, 7/4, 7/4, 0, 0, 0, 0, so the zero eigenvalue has multiplicity four.
- COMPUTED (mpmath, 40-digit arithmetic, outside the Lean development): sign formulas for m=1,...,15 and 67 exponents r in [-6,30], with zero violations. These are numerical checks and not part of the formal proof.
- OPEN: even orders and the analogous multiplicity statement for other entrywise functions of C.

## ASSUMED-UNVERIFIED

The quotation and access limit are attributed to the journal source;
the exact sentence page is unverified. The
[Jain note](../Library/Eigenstructure/jain2017hadamard.md) binds the
DOI and article URL and distinguishes the journal and arXiv versions.

Searches covered the verbatim sentence, title, DOI, author and
multiplicity keywords, MathDB, arXiv abstracts, and repository
Problems, Library and D5 material. Relevant literature includes
Jain's *Hadamard powers of rank two, doubly nonnegative matrices*
(arXiv:2004.03909), Theorem 2(iv); Baslingker–Dan's work on
Hadamard powers and positivity exponents (arXiv:2201.04443 and
2312.02766); Khare's Jain–Karlin–Schoenberg kernel treatment
(arXiv:2008.05121) and lecture notes; Damm–Dietrich
(arXiv:2207.08853); Belton–Guillot–Khare–Putinar
(arXiv:1812.05482 and 2310.18041); and Alsaafin's thesis.
The rank-two simplicity, positivity-exponent, truncated-kernel,
and negativity-preservation results do not provide the spectral-gap
separation required here.

No settlement of the conjecture was found in that scope. Citation indexes were unavailable, so the citing literature was not exhaustively checked; this is not a priority certification.
