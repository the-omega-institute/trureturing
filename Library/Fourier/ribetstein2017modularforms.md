---
bibkey: ribetstein2017modularforms
authors: "Kenneth A. Ribet and William A. Stein"
year: 2017
title: "Lectures on Modular Forms and Hecke Operators"
doi: null
url: https://wstein.org/books/ribet-stein/main.pdf
claim: "Triangular representatives for the level-one Hecke action give the classical normalized prime action and its analytic q-expansion coefficient law."
strata_touched:
  - D5/S3/Arith/ModularForms/ActualPrimeHecke
license: citation-only
triage: anchor
---

# Level-one prime Hecke action and coefficients

## Verified locator

The primary source is Ribet and Stein, *Lectures on Modular Forms and Hecke
Operators*, the PDF version whose title page is dated January 12, 2017,
at https://wstein.org/books/ribet-stein/main.pdf. Its SHA256 is
`8487222fa61e37ba3bf01a70168ede14237611b963e55b776ddbb329595f39e4`.
Page references below use the printed page numbers.

- Proposition 3.5.2, p. 20, classifies the triangular representatives for
  index-n sublattices. For prime n=p, these are the p+1 representatives
  underlying the action at pz and at (z+a)/p, with 0 <= a < p.
- Section 3.5.2, pp. 21–22, derives the factor `n^(k-1) d^(-k)` for a
  triangular representative and the resulting prime coefficient law
  `c(p*n) + p^(k-1) c(n/p)`, where the second term is zero unless p divides
  n. The derivation includes the constant coefficient. The coefficient law
  is derived in this section; it is not the statement of Proposition 3.5.2.

## Source and implementation scope

The source normalization gives
`T_p f(z) = p^(k-1) f(pz) + p^(-1) sum_(0 <= a < p) f((z+a)/p)`.
The owning Blueprint attributes this action and its analytic coefficient
law to the classical source through the typed literature reference
`D5/L/Fourier/ribetstein2017modularforms`.

The Lean implementation constructs a complex-linear endomorphism of the
actual level-one cusp-form space using Mathlib's translation and trace.
Its identification of the real conjugate-intersection subgroup through
divisibility of an integer matrix entry, its quotient bijection, and its
convergence and coefficient-uniqueness bridges are repository proofs
using pinned Mathlib APIs. This note does not attribute those Lean API
constructions or their exact statements to the cited proposition. The
endomorphism and subgroup-criterion descriptions retain repository
provenance.

The Lean laws quantify over every prime including 2, every integer weight,
and every natural coefficient index including zero; the implementation
also retains degenerate cusp-form spaces. Those formal scope choices are
checked by Lean rather than asserted to be the literal quantifiers of
the source. This is classical formal-library growth and supplies no
resolution of Lehmer's conjecture or claim of mathematical originality.

Citation and source-boundary note only; no source text, PDF or code is
vendored.
