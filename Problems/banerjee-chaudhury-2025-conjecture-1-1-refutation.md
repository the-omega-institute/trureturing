---
slug: banerjee-chaudhury-2025-conjecture-1-1-refutation
bibkey: banerjeechaudhury2025stability
doi: null
url: https://arxiv.org/abs/2509.06715v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/BanerjeeChaudhuryStabilityRefutation.result
---

# The Banerjee–Chaudhury simultaneous stability conjecture

## Problem

Debraj Banerjee and Kunal N. Chaudhury, *On the Schur Stability of Some Image Reconstruction Operators*, arXiv:2509.06715v1, Conjecture 1.1:

> Let $W$ be primitive and stochastic, and let $B$ be positive semidefinite with $Be \leqslant \varrho(B) e$ and $\pi^\top Be > 0$, where $\pi$ is the left Perron eigenvector of $W$. Then $P(t)$ and $R(t)$ are stable for all $0 < t < 2/\varrho (B)$.

The source conventions fix every positive dimension $n$, real square matrices $W,B$, nonsymmetric nonnegative primitive row-stochastic $W$, nonzero symmetric positive semidefinite $B$, and a strictly positive stationary left vector $\pi$, normalized by $\pi^\top e=1$. Here $e$ is the all-ones vector, $We=e$, and primitivity means that some positive integer power of $W$ has all entries strictly positive. The inequality $Be\leq\varrho(B)e$ is componentwise. No entrywise nonnegativity of $B$ is required. The spectral radius $\varrho(A)$ is the maximum modulus of a complex eigenvalue of $A$; Schur stability is $\varrho(A)<1$. The operators are

$$P(t)=W(I-tB),\qquad R(t)=I-W+(I+tB)^{-1}(2W-I).$$

The assertion quantifies over every real $t$ with $0<t<2/\varrho(B)$ and requires both stability inequalities. The source assumes the displayed inverse exists. Positive semidefiniteness makes $I+tB$ positive definite for nonnegative $t$, so the explicit unit condition in the Lean claim is equivalent to the source's genuine inverse domain.

## Motivation

A simultaneous stability interval for these reconstruction operators would control convergence using only the stated stochastic and semidefinite hypotheses. An exact counterexample identifies a limit of those hypotheses without numerical spectral estimation.

## Gap

The full simultaneous assertion is false. The failure concerns the first operator $P$ inside the proposed interval. Stability of $R$ alone, a classification of Problem 1.1, and sufficient repaired conditions remain outside this result.

## Route

Take $n=4$, $t=9/5$, and

$$W=\frac1{40}\begin{pmatrix}37&1&1&1\\1&1&1&37\\1&1&1&37\\37&1&1&1\end{pmatrix},\qquad
B=\frac13\begin{pmatrix}1&1&1&0\\1&1&1&0\\1&1&1&0\\0&0&0&3\end{pmatrix}.$$

Set $\pi=(176,5,5,14)^\top/200$ and $x=(28,-19,-19,28)^\top$. Every entry of $W$ is strictly positive and its rows sum to one, so primitivity holds with exponent one; $W$ is nonsymmetric. The positive normalized vector $\pi$ satisfies $\pi^\top W=\pi^\top$. The nonzero symmetric matrix $B$ satisfies $B^2=B=B^\top B$, so it is positive semidefinite, $Be=e$, and $\varrho(B)=1$. Consequently $Be=\varrho(B)e$ and $\pi^\top Be=1>0$, while $0<9/5<2/\varrho(B)$.

The inverse at this parameter is $H=I-(9/14)B$: both $(I+(9/5)B)H=I$ and $H(I+(9/5)B)=I$. Direct exact multiplication gives

$$P(9/5)x=\frac{27}{25}x,\qquad x\ne0.$$

The eigenpair puts $27/25$ in the complex spectrum. The finite maximum-modulus bound gives $\varrho(P(9/5))\ge27/25>1$, contradicting the first conjunct and refuting the full assertion.

## Falsifier

A source mismatch would arise from omitting nonsymmetry, primitivity, nonzero symmetric positive semidefiniteness, the stationary left vector, either componentwise/strict positivity condition, the open parameter interval, or either stability conjunct. All occur in the canonical claim and its narrative mirror. The result has the literal type `Not claim`; it asserts no instability of $R$.

## Evidence

The formal source is `D5/S3/Quantum/Matrix/BanerjeeChaudhuryStabilityRefutation.lean`, with its corresponding Blueprint Scribe and generated Markdown. The proof reuses the frozen spectral-radius definition and eigenpair-to-spectrum theorem, together with pinned Mathlib's compact-spectrum maximum, positive-definiteness and matrix identities. It uses only `Classical.choice`, `Quot.sound` and `propext`.

The [versioned original source](https://arxiv.org/src/2509.06715v1) is licensed [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). Its `manuscript.tex` SHA-256 is `2a828b151c14f8bff40243c0a56cc6a9d3b4efce27e4258215db2940ad9baf4b`. The literature note identifies the definition and conjecture locators. The exact Lean proof is the formal result; this dossier contains no numerical experiment.

## Triage

`theorem`; proved: the negation of the full Conjecture 1.1 conjunction, through $P$. The theorem's proof shape is `bind-only`, with admission basis `open-problem-resolution`; no new spectral theorem is claimed. The eight private helper theorems have live consumers in the result's proof. The sole authored public theorem is the designated utility refutation result.

Open: the stability assertion for $R$ alone, the broader classification in Problem 1.1, and repaired sufficient hypotheses. The source's separate positive results under stronger hypotheses are outside this refutation.

## ASSUMED-UNVERIFIED

The accepted bounded primary and contemporary literature qualification does not establish exhaustive worldwide novelty or priority. Wiley, author confirmation and full citing-literature coverage remain unverified. The exact model-family isolation is unverified. These limitations do not change the formal counterexample or enlarge its scope.
