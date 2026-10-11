---
bibkey: kryvonos2023openproblems
authors: L. Kryvonos (ed.)
year: 2023
title: "Open problems on polynomials, their zero distribution and related questions: 2023"
doi: null
url: https://arxiv.org/abs/2312.07754v1
claim: "Geno Nikolov conjectures that snake polynomials for continuous even convex nonnegative majorants have nonnegative expansions in Chebyshev polynomials of the first kind."
strata_touched: []
license: citation-only
triage: anchor
---

## Locator

DOI: null

Source: https://arxiv.org/abs/2312.07754v1

The section “Snake polynomials with positive Chebyshev expansions” states the snake definition and Geno Nikolov's conjecture:

> Consider a majorant µ ∈ C[−1, 1], µ(x) ≥ 0, x ∈ [−1, 1]. If there exists P ∈ Pn, P ≠ 0, such that −µ(x) ≤ P(x) ≤ µ(x), x ∈ [−1, 1], then there exists a unique (up to orientation) polynomial ωµ ∈ Pn called snake polynomial associated with µ, which oscillates most between ±µ.

> The n-th snake polynomial ωµ is uniquely determined by the following properties: a) |ωµ(x)| ≤ µ(x) x ∈ [−1, 1]; b) There exists a set δ* = (τi*)_{i=0}^n, 1 ≥ τ0* > · · · > τn* ≥ −1, such that ωµ(τi*) = (−1)^i µ(τi*), i = 0, . . . , n

> Conjecture (G.N.) If µ ≥ 0 is a continuous even convex function in [−1, 1], then the associated with µ snake polynomials have non-negative expansion in the Chebyshev polynomials of the first kind.

The arXiv version is the source locator; no DOI is recorded.

# Snake polynomials and positive Chebyshev expansions

For a nonnegative majorant on $[-1,1]$, the snake conditions combine a pointwise bound with $n+1$ ordered alternating contacts. The degree is at most $n$, and the orientation in condition (b) begins with a positive contact. The conjecture concerns the signs of the coefficients in the first-kind Chebyshev basis, including the constant coefficient.

**Repository-derived counterexample.** The declaration `D5.S3.Analytic.Chebyshev.SnakeChebyshevExpansionRefutation.result` refutes the assertion at $n=6$ with

$$
\mu(x)=\max\left\{1,\frac{4860|x|-1078}{137}\right\},\qquad
P(x)=\frac{38656x^6-41568x^4+6831x^2-137}{137}.
$$

The majorant is positive, continuous, even and convex. The polynomial is bounded by it and alternates at $1,3/4,1/4,0,-1/4,-3/4,-1$. Every representation of $P$ in $T_0,\ldots,T_6$ has constant coefficient $-459/274$.

## Related literature and scope

*Open problems UP24*, arXiv:2504.04845, §7, repeats the assertion as Conjecture 7.1 (Geno Nikolov). Problem 7.1 asks for majorant classes whose snake polynomials have nonnegative or sign-alternating Chebyshev expansions; that classification remains open.

Nikolov–Shadrin, arXiv:1210.7795, establishes extremality in Markov–Duffin–Schaeffer inequalities with a majorant under the positive-expansion hypothesis. The 2023 collection describes extremality of the snake polynomial in the Markov problem as a folklore conjecture with no known counterexample. A negative Chebyshev coefficient does not refute that extremality assertion.

**ASSUMED-UNVERIFIED:** uniqueness up to orientation is quoted from the source and is not formalized in the counterexample module. Literature coverage is limited to the cited arXiv versions and establishes no exhaustive priority claim.

Citation only; no source PDF or TeX is redistributed.
