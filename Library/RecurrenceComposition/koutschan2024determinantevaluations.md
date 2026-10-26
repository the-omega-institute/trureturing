---
bibkey: koutschan2024determinantevaluations
authors: Christoph Koutschan; Christian Krattenthaler; Michael J. Schlosser
year: 2024
title: "Determinant evaluations inspired by Di Francesco's determinant for twenty-vertex configurations"
doi: 10.1016/j.jsc.2024.102352
url: https://arxiv.org/abs/2401.08481v1
claim: "Conjecture 23, equations (10.10)–(10.12), asserts the displayed identities between the four-parameter determinants for all n ≥ 3."
strata_touched:
  - D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG
  - D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserTenTen
  - D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserTenEleven
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1016/j.jsc.2024.102352

Source: https://arxiv.org/abs/2401.08481v1

The arXiv version is v1. The journal version is Journal of Symbolic
Computation 127 (2025), article 102352.

## Source statements

Page 1, equation (1.2), defines the binomial coefficient as
α(α−1)⋯(α−p+1)/p! if p ≥ 0, and 0 if p < 0.

Page 32: “Let us denote”

\[
G_{\alpha,\beta,\gamma,\delta}(n):=
\det_{0\le i,j\le n-1}\left(
2^{i+\beta}\binom{i+4j+\gamma}{4j+\alpha}
+\binom{-i+4j+\delta}{4j+\alpha}\right).
\]

Page 33, Conjecture 23:

> Moreover, the following identities are conjectured to hold for all n ≥ 3:

\[
\begin{aligned}
G_{3,0,3,3}(n)&=\tfrac23G_{0,1,-2,-4}(n+1)
=-\tfrac1{672}G_{1,3,-2,-8}(n+1)\\
&=\tfrac1{63}G_{5,4,3,-5}(n)
=\tfrac4{1002001}G_{6,6,3,-9}(n)
=-\tfrac85G_{9,5,8,-2}(n-1),\tag{10.10}\\
G_{1,1,0,-2}(n)&=-\tfrac1{49}G_{2,3,0,-6}(n)
=-\tfrac27G_{6,4,5,-3}(n-1)
=-\tfrac4{5577}G_{7,6,5,-7}(n-1),\tag{10.11}\\
G_{2,1,2,0}(n)&=2G_{7,4,7,-1}(n-1).\tag{10.12}
\end{aligned}
\]

Page 32, Proposition 22: “For all integers n ≥ 2 we have the following relations:”
> G₀,₁,−₂,−₄(n) = 3 G₄,₂,₃,−₁(n − 1) = 3 G₈,₃,₈,₂(n − 2), (10.2)
>
> G₁,₁,₀,−₂(n) = −2 G₅,₂,₅,₁(n − 1), (10.3)

The formalization uses rational matrix entries, integer parameters and integer
powers of 2. Nonnegative matrix sizes and zero-based finite indices encode the
source's ranges. Mathlib's generalized binomial coefficient `Ring.choose`
represents the falling-factorial branch.

## Literature boundary

The bounded literature screen supplied with issues #19228, #19236 and #19237
leaves completeness and publication priority ASSUMED-UNVERIFIED. The source
statements, including Proposition 22, are literature statements; the proofs of
the three conjectural identities are repository derivations. Product-formula
corollaries using other papers' evaluations are not formalized here.
