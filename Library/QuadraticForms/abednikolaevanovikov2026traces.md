---
bibkey: abednikolaevanovikov2026traces
authors: Sami Abdullah Abed; Irina Nikolaeva; Andrej Novikov
year: 2026
title: "How characterisations of traces and central elements fail: sharp violation constants via Michelson contrast and noncentrality"
doi: 10.48550/arXiv.2610.34388
url: https://arxiv.org/abs/2610.34388v1
claim: "Section 11.2(5) asks whether the Alhasan–Fawwaz constant is bounded on M_n(C) independently of the positive definite density."
strata_touched:
  - D5/S3/Quantum/Matrix/AbedNikolaevaNovikovAFDensityBound
license: citation-only
triage: anchor
---

## Verified locator

- DOI: 10.48550/arXiv.2610.34388
- Version: https://arxiv.org/abs/2610.34388v1
- Section 3.1, page 8: trace, modulus, and positive definite density conventions.
- Section 5.12, Proposition 5.44, pages 32–33: the quotient and existing bounds.
- Section 11.2(5), page 59: the fixed-dimension boundedness question.

This note is citation-only; it does not reproduce the source article or grant
permission to redistribute it. The original Alhasan–Fawwaz article and
worldwide novelty remain unverified.

## Source and domain

The source is arXiv:2610.34388v1, Sections 3.1, 5.12 (Proposition 5.44), and
11.2(5), printed pages 8, 32–33, and 59. Its PDF has SHA-256
`b6d9af9cdbf570646201ecce02ef2a52bf2540f96bf8a56992a1ada924265abb`.

Section 3.1 uses the ordinary matrix trace, defines
$|X|=(X^*X)^{1/2}$, and sets $\varphi_\rho(Y)=\operatorname{Tr}(\rho Y)$.
The standing density assumption is $\rho>0$, without trace normalization.
Section 5.12 defines

$$
a(\rho)=\sup\left\{
\frac{\varphi_\rho(A)}{\varphi_\rho(|A+iB|)}:
A\ge0,\ B=B^*,\ A+iB\ne0\right\}.
$$

The selected sentence in Section 11.2(5) is:

> Is $a$ bounded on $M_n(\mathbb C)$ independently of $\rho$?

Here $n$ is fixed. Determining the entire function, the factor question, and
the variant with positive $B$ are separate questions. Proposition 5.44(c)
already supplies the dimension-two bound; its condition-dependent general
bound does not supply a bound depending only on dimension.

## Scope

The companion formalization targets $C_n=n$ for every $n\ge1$, with the same
quotient set, positive denominators, and the genuine real least upper bound.
Its matrix argument diagonalizes $|X|$, including its zero eigenspaces, and
does not require $X$ to be invertible. No sharpness or priority claim is made.
The original Alhasan–Fawwaz article and worldwide novelty remain unverified.
