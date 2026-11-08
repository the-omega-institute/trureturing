---
bibkey: abednikolaevanovikov2026traces
authors: Sami Abdullah Abed; Irina Nikolaeva; Andrej Novikov
year: 2026
title: "How characterisations of traces and central elements fail: sharp violation constants via Michelson contrast and noncentrality"
doi: 10.48550/arXiv.2610.34388
url: https://arxiv.org/abs/2610.34388v1
claim: "Section 11.2(5) asks for a dimension-only Alhasan–Fawwaz bound; Conjecture 11.1, item 8, asks for the exact two-contrast Young envelope in every positive even dimension."
strata_touched:
  - D5/S3/Quantum/Matrix/AbedNikolaevaNovikovAFDensityBound
  - D5/S3/Quantum/Matrix/AbedNikolaevaNovikovTwoContrastYoung
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

## Two-contrast Young envelope

Conjecture 11.1, final clause, page 57: “and the lower bound of Proposition 5.22 is the two-contrast envelope of item 8 for even n.”

Section 3.2, page 8:

> For a positive invertible operator $T$ on a Hilbert space with $m=\min\sigma(T)$, $M=\max\sigma(T)$ let

$$
\kappa(T)=\frac Mm,\qquad \operatorname{OLC}(T)=\tfrac12\ln\kappa(T),\qquad
\operatorname{OMC}(T)=\tanh\operatorname{OLC}(T)=\frac{M-m}{M+m}.
$$

Section 3.8, page 12:

> The envelope $V_n(\delta)$ lets the operator variables range over all operators. To see how the violation depends on the operators themselves, we also prescribe their contrast. For a positive variable $A$ we use $\operatorname{OMC}(A)$, for an arbitrary or self-adjoint variable $X$ the contrast $\operatorname{OMC}(|X|)$ of its modulus (for the Peierls--Bogoliubov inequality, item 16, the variables are positive, as in [14]), and we let every operator variable of an item have the same contrast $\delta'\in[0,1]$:

$$
V_n(\delta,\delta')=\sup\left\{\frac{\mathcal L-\mathcal R}{\mathcal N}:\ \operatorname{OMC}(\rho)=\delta,\ \text{every operator variable of contrast }\delta'\right\}.
$$

Table 3, item 8, uses arbitrary complex matrices and
$\mathcal L=\varphi_\rho(|AB^*|)$,
$\mathcal R=\mathcal N=(\varphi_\rho(|A|^2)+\varphi_\rho(|B|^2))/2$.
Section 3.1 sets $|X|=(X^*X)^{1/2}$, $\varphi_\rho(X)=\operatorname{Tr}(\rho X)$ and, by default, $\rho>0$ without trace-one normalization.

Proposition 5.22, page 23, states
$V_n(\delta,\delta')\ge 4\delta\delta'/(1+\delta'^2-2\delta\delta')$
for every positive even dimension, including $\delta'=1$.
The repository proof establishes the matching upper bound for arbitrary independently oriented inputs; the repeated two-block construction attains it.

### Scope

The Lean statement uses $n=2r$ with $r\ge1$, $0\le\delta<1$, and $0\le\delta'\le1$.
It asserts nonemptiness and boundedness of the actual set of relative violations as well as its exact real supremum.
Singular nonzero inputs are included at $\delta'=1$; singular densities are excluded.
The sharp odd-dimensional envelope for interior contrasts remains open here.
The source is arXiv v1. Completeness of the literature screen in issue #22727 is ASSUMED-UNVERIFIED.
