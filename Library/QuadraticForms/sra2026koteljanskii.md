---
bibkey: sra2026koteljanskii
authors: Suvrit Sra
year: 2026
title: A Koteljanskii inequality for permanents
doi: 10.48550/arXiv.2609.39979
url: https://arxiv.org/abs/2609.39979v1
claim: Section 4(b) asks about alpha-permanent log-supermodularity for symmetrizable inverse M matrices; Section 4(d) asks whether the reciprocal-permanent polynomial is Lorentzian.
strata_touched:
  - D5/S3/Combinatorics/Permanental/SraReciprocalPermanentLorentzianRefutation
  - D5/S3/Combinatorics/Permanental/SraSymmetricAlphaPermanentRefutation
license: citation-only
triage: anchor
---
<!-- GID: D5/L/QuadraticForms/sra2026koteljanskii -->
# A Koteljanskii inequality for permanents

## Verified locator

DOI: 10.48550/arXiv.2609.39979

Source: https://arxiv.org/abs/2609.39979v1

The source is arXiv v1. The inverse-M definition is on page 1,
the alpha-permanent definition is equation (3.1) on page 5, and both open
questions are on page 6. No journal version was identified in the screen
recorded in issues #21688 and #21689.

## Questions (verbatim source TeX, page 6)

### Section 4(d)

```tex
\item For an inverse \(M\)-matrix \(A\), consider
  \[
    f_A(x_0,x)=\nlsum_{S\subseteq[n]}\per(A_S)^{-1}x_0^{\,n-|S|}\prod\nolimits_{i\in S}x_i.
  \]
  For positive semidefinite \(A\), the polynomial with coefficients \(\det(A_S)\) in place of \(1/\per(A_S)\) is \(\det(x_0I+\diag(x)A)\), which is real stable \citep{branden08} and hence Lorentzian \citep{branden2020lorentzian}. Is \(f_A\) Lorentzian for every inverse \(M\)-matrix \(A\)? Numerical tests with \(n\le5\) found no counterexample, including the matrix of Theorem~\ref{thm:counterexample}; for random nonnegative \(A\), by contrast, \(f_A\) is usually not Lorentzian, and for symmetric inverse \(M\)-matrices the polynomial with coefficients \(\per(A_S)\) was never Lorentzian.
```

### Section 4(b)

```tex
\item For symmetrizable inverse \(M\)-matrices and \(\alpha\notin\{\tfrac12,1\}\), decide whether \(S\mapsto\per_\alpha(A_S)\) is log-supermodular. Theorem~\ref{thm:main} and Remark~\ref{rmk:real} settle \(\alpha=1\), \(\alpha=\tfrac12\), and every \(\alpha>0\) when the graph of \(A^{-1}\) is a tree.
```

## Source definitions

**Source definitions and conventions, verbatim.**

```tex
For an \(n\times n\) matrix \(A\) and \(S\subseteq[n]\), write \(A_S=A[S,S]\) for the principal submatrix with row and column set \(S\), and set \(\det(A_\varnothing)=\per(A_\varnothing)=1\).
```

```tex
where as usual the permanent of an $n\times n$ matrix is defined as
\begin{equation}
  \label{eq:1}
  \per(A)=\sum_{\pi\in \mathrm{Sym}_n}\prod\nolimits_{i\in [n]}A_{i,\pi(i)}.
\end{equation}
```

```tex
A matrix \(A\) is an inverse \(M\)-matrix if \(A\ge0\) entrywise, \(A\) is invertible, and \(A^{-1}\) has nonpositive off-diagonal entries. We prove~\eqref{eq:lsm} for inverse \(M\)-matrices that are symmetric after a positive diagonal similarity, which we call \emph{symmetrizable}, and show that~\eqref{eq:lsm} can fail without this hypothesis.
```

```tex
For \(\alpha>0\), the \(\alpha\)-permanent of a matrix \(H\) indexed by \(S\) is
\begin{equation}\label{eq:alphaper}
  \per_\alpha(H)=\sum_{\pi\in\mathfrak S(S)}\alpha^{c(\pi)}\prod_{i\in S}H_{i,\pi(i)},
\end{equation}
where \(\mathfrak S(S)\) is the group of permutations of \(S\) and \(c(\pi)\) is the number of cycles of \(\pi\); the ordinary permanent is \(\alpha=1\).
```

```tex
\begin{equation}\label{eq:lsm}
  \per(A_{S\cup T})\per(A_{S\cap T})\ge \per(A_S)\per(A_T),
  \qquad S,T\subseteq[n],
\end{equation}
```

The Lorentzian definition cited by the source is Brändén–Huh (2020),
arXiv:1902.03719v8, §2.1 (pages 6–7), Definition 2.1 (page 7).
Its complete source expression is quoted in
[the Brändén–Huh note](../Combinatorics/brandenhuh2020lorentzian.md).
The Lean predicate uses this recursive strict class and coefficientwise
closure, rather than replacing Lorentzianity by a necessary Hessian test.


## Exact settlement and scope

The reciprocal-permanent assertion is refuted by the positive 5×5 inverse M
matrix printed in Theorem 1.2. Its last three coordinate derivatives have a
Hessian positive definite on a two-dimensional plane. This persists under
sufficiently small coefficient perturbations, contradicting the recursive
strict Lorentzian signature condition. The symmetric 4×4 alpha-permanent
counterexample has negative union-intersection difference for every
0<alpha≤1/200. The two formal results refute the universal affirmative
assertions; the remaining parameter ranges and symmetric reciprocal question
are not settled here. No proved theorem of the source uses affirmative
answers to these open questions.

## Computation and literature boundary

The independent rational checker is in the private repository
`the-omega-institute/trureturing-experiments`, commit
`fc05f5ee612010d382cf8772f7bf43a1cb830aa1`, at
`docs/reports/sra-koteljanskii/check.py`, SHA-256
`bf8bef761479549a67a05ccf46ec6e0ebe90c9adf347d014cec66ea510a92a75`.
The command `python3 docs/reports/sra-koteljanskii/check.py` exits 0 and
ends `ALL_CHECKS_OK`. Computation is distinguished from the Lean results.
The literature search scope and its gaps are recorded in #21688 and #21689;
literature completeness is ASSUMED-UNVERIFIED.
