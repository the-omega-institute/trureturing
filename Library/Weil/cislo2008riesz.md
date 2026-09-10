---
bibkey: cislo2008riesz
authors: Jerzy Cislo and Marek Wolf
year: 2008
title: On the Riesz and Baez-Duarte criteria for the Riemann Hypothesis
doi: null
url: https://arxiv.org/abs/0807.2971v1
claim: The Riesz function and the finite Baez-Duarte sequence have an exponential generating identity and signed Moebius series representations.
strata_touched:
  - D5/S3/Weil/ZetaBridge/RieszBaezDuarte
license: citation-only
triage: anchor
---

# Riesz and Baez-Duarte Transforms

Equations (2) and (4) define the Riesz function and the discrete coefficients:

\[
R(x)=x\sum_{j=0}^{\infty}\frac{(-1)^j x^j}{j!\,\zeta(2j+2)},
\qquad
c_k=\sum_{j=0}^{k}\frac{(-1)^j\binom{k}{j}}{\zeta(2j+2)}.
\]

The paper's equation (10) is the exponential generating identity:

\[
\sum_{k=0}^{\infty}\frac{x^k}{k!}c_k=\frac{e^x}{x}R(x).
\tag{10}
\]

Equations (13) and (14) give the signed Moebius series:

\[
R(x)=x\sum_{j=0}^{\infty}\frac{(-x)^j}{j!\,\zeta(2j+2)}
    =x\sum_{n=1}^{\infty}\frac{\mu(n)}{n^2}e^{-x/n^2},
\tag{13}
\]

\[
c_k=\sum_{j=0}^{k}\frac{\binom{k}{j}(-1)^j}{\zeta(2j+2)}
   =\sum_{n=1}^{\infty}\frac{\mu(n)}{n^2}
      \left(1-\frac{1}{n^2}\right)^k.
\tag{14}
\]

Here the dummy index in (2) has been renamed to j. The paper's c_k is the
repository theory's b_k and the formalization's baezDuarte k, with the same
finite alternating binomial definition. The formal Riesz function has domain
Real; its two HasSum identities are stated for real x > 0. These are the
repository's positive-real scope, not extra printed quantifiers attributed
to equations (10) and (13). The discrete identity includes every natural k,
including zero. Reindexing the positive arithmetic index as n+1 retains the
entire signed Moebius series, including mu(1)=1. At k=0 the formalization
uses the natural-power convention 0^0=1; the paper prints no separate
convention for that endpoint.

At the positive even zeta arguments the actual complex zeta value is real
and nonzero, so its reciprocal equals the real reciprocal used in the Lean
definitions after the real-to-complex identification. The HasSum values are
respectively exp(x)*(riesz x/x), riesz x/x, and baezDuarte k. Multiplying
equation (10) by exp(-x) gives the theory's R(x)/x presentation; multiplying
the arithmetic Riesz HasSum equality by nonzero x recovers equation (13).
HasSum certifies convergence as well as the value. The source calls its
intermediate operator equation (8) formal and does not print a separate
absolute-convergence calculation for these interchanges; the formalization
supplies those arguments.

This note records literature and its notation correspondence. It adds no
theorem, coverage, or priority claim. The identities alone do not establish
the Lemma 3 error O(k^(-3/2)), Lemma 4's uniform variation on all 0 < x < y,
Theorem 1's growth equivalence for delta > -3/2, or either original RH
criterion with its quantifier over every epsilon > 0.

## Source Validation

The authorized primary-source intake crosschecked PDF pages 2-3 against
CW_xxx.tex in the pinned v1 source archive: definition (2), lines 84-88;
definition (4), lines 99-104; equation (10), lines 154-158; equations (13)-(14),
lines 178-190. This is inherited source-transcription evidence, not an
independent proof review. The PDF and TeX name the first author Jerzy Cislo.
The repository theory bibliography's first name Jan is a bibliographic
discrepancy.

The intake records arXiv v1 submission at 2008-07-18T13:23:33Z and observes
only v1 in the arXiv submission history. The PDF title page prints October
28, 2018; its creation and modification metadata read
`D:20181030111744-04'00'`. Those printed and PDF-generation dates do not
establish a later arXiv version. The citation year follows the 2008
submission. No DOI was verified, so the citation uses doi: null and the
exact stable HTTPS v1 URL.

## Verified locator

- https://arxiv.org/abs/0807.2971v1
- https://arxiv.org/pdf/0807.2971v1
- https://arxiv.org/src/0807.2971v1
- Repository source, F09 and E14/E15:
  https://github.com/the-omega-institute/trureturing/blob/915a86bf19ec91fdbd690a70e75c84014d237b7d/docs/develop/theory/RH_RESEARCH_LANE_THEORY.md
