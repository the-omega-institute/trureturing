---
bibkey: brandenhuh2020lorentzian
authors: Petter Brändén, June Huh
year: 2020
title: Lorentzian polynomials
doi: 10.4007/annals.2020.192.3.4
url: https://arxiv.org/abs/1902.03719v8
claim: Reciprocal-factorial generating polynomials of M-convex supports are Lorentzian, with positive-orthant root concavity and Hessian signature restrictions.
strata_touched:
  - D5/S3/Resource/SimplexCoverageHessian
  - D5/S3/Resource/SimplexCoveragePolynomial
  - D5/S3/Combinatorics/Permanental/SraReciprocalPermanentLorentzianRefutation
license: citation-only
triage: anchor
---
<!-- GID: D5/L/Combinatorics/brandenhuh2020lorentzian -->
# Lorentzian polynomials

The journal article is in *Annals of Mathematics* 192, issue 3, pages 821–891.
The source version used for the concavity-transfer route is arXiv:1902.03719v8.

## Verified locator

DOI: 10.4007/annals.2020.192.3.4

Source: https://arxiv.org/abs/1902.03719v8

## Definitions (verbatim source TeX)

Section 2.1, pages 6–7, and Definition 2.1, page 7, specify the positive
homogeneous coefficient space, strict Lorentzian recursion, and its closure.

```tex
Let $n$ and $d$ be nonnegative integers, and set $[n]=\{1,\ldots,n\}$.
We write $\mathrm{H}^d_n$ for the set of degree $d$ homogeneous polynomials in $\mathbb{R}[w_1,\ldots,w_n]$.
We define a topology on $\mathrm{H}^d_n$ using the Euclidean norm for the coefficients,
and write $\mathrm{P}^d_n \subseteq \mathrm{H}^d_n$ for the open subset of polynomials  all of whose %$\multiset{n}{k}$
coefficients are positive.
The \emph{Hessian} of $f \in \RR[w_1,\ldots, w_n]$ is the symmetric matrix
\[
\mathscr{H}_f(w)=\Big( \partial_i\partial_j f \Big)_{i,j=1}^n,
\]
where $\partial_i$ stands for the partial derivative $\frac{\partial}{\partial w_i}$.
```

```tex
\begin{definition}[Lorentzian polynomials]\label{FirstDefinition}
We set $\mathring{\mathrm{L}}^0_n=\mathrm{P}^0_n$, $\mathring{\mathrm{L}}^1_n=\mathrm{P}^1_n$, and
\[
\mathring{\mathrm{L}}^2_n=\Big\{f \in \mathrm{P}^2_n\mid \text{$\HE_f$ is nonsingular and has exactly one positive eigenvalue} \Big\}.
\]
For $d$ larger than $2$, we define $\mathring{\mathrm{L}}^d_n$ recursively by setting
\[
\mathring{\mathrm{L}}^d_n=\Big\{f \in \mathrm{P}^d_n\mid \text{$\partial_i f \in \mathring{\mathrm{L}}^{d-1}_n$ for all $i \in [n]$} \Big\}.
\]
The polynomials in $\mathring{\mathrm{L}}^d_n$  are called \emph{strictly Lorentzian}, and the limits of strictly Lorentzian polynomials are called \emph{Lorentzian}.
%polynomials in the closure of $\mathring{\mathrm{L}}^d_n$ are called \emph{Lorentzian}.
\end{definition}
```


## Mathematical interfaces

Section 2.2 gives the exchange condition for M-convex supports. Theorem 3.10,
implication (7) to (4), concerns normalized generating polynomials with
reciprocal-factorial coefficients. Theorem 2.30 and Proposition 2.33 supply
the positive-orthant log/root-concavity context. Polynomial support conditions,
nonzero evaluation, homogeneity, and degree hypotheses must be verified by a
consumer; a support-indicator polynomial is not the same normalized polynomial.

## Formal reuse boundary

The matrix component in `D5/S3/Resource/SimplexCoverageHessian` uses
Mathlib's finite real Hermitian eigenbasis and a maximum-ratio argument. It
does not import a formal Lorentzian theorem, establish the represented-span
polynomial induction, or settle a simplex optimizer conjecture. The citation
is published mathematical context, not kernel evidence or an independent
open-problem result.

`D5/S3/Resource/SimplexCoveragePolynomial` supplies the actual represented
coefficients and contractions, degree-two Hessian classification and reverse
inequality, positive-evaluation rank criterion, derivative-positive support
connectivity and rank/span zero obstructions. The higher-degree normalized
Hessian induction and the analytic and sampling bridges remain open.
