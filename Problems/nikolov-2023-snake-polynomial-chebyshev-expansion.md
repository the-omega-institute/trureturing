---
slug: nikolov-2023-snake-polynomial-chebyshev-expansion
bibkey: kryvonos2023openproblems
doi: null
url: https://arxiv.org/abs/2312.07754v1
triage: theorem
motivation_gids:
  - D5/S3/Analytic/Chebyshev/SnakeChebyshevExpansionRefutation.result
---

# Nonnegative Chebyshev expansions of snake polynomials

## Problem

L. Kryvonos (ed.), *Open problems on polynomials, their zero distribution and related questions: 2023*, arXiv:2312.07754v1, section “Snake polynomials with positive Chebyshev expansions”, states:

> Consider a majorant µ ∈ C[−1, 1], µ(x) ≥ 0, x ∈ [−1, 1]. If there exists P ∈ Pn, P ≠ 0, such that −µ(x) ≤ P(x) ≤ µ(x), x ∈ [−1, 1], then there exists a unique (up to orientation) polynomial ωµ ∈ Pn called snake polynomial associated with µ, which oscillates most between ±µ.

> The n-th snake polynomial ωµ is uniquely determined by the following properties: a) |ωµ(x)| ≤ µ(x) x ∈ [−1, 1]; b) There exists a set δ* = (τi*)_{i=0}^n, 1 ≥ τ0* > · · · > τn* ≥ −1, such that ωµ(τi*) = (−1)^i µ(τi*), i = 0, . . . , n

> Conjecture (G.N.) If µ ≥ 0 is a continuous even convex function in [−1, 1], then the associated with µ snake polynomials have non-negative expansion in the Chebyshev polynomials of the first kind.

The assertion is repeated as Conjecture 7.1 (Geno Nikolov) in *Open problems UP24*, arXiv:2504.04845, §7. Here $\mathcal P_n$ denotes polynomials of degree at most $n$, and $T_k$ denotes the first-kind Chebyshev polynomial.

## Motivation

Nonnegative Chebyshev expansion is the hypothesis under which Nikolov–Shadrin, arXiv:1210.7795, prove extremality of the snake polynomial in Markov–Duffin–Schaeffer inequalities with a majorant. The 2023 collection calls extremality of the snake polynomial in the Markov problem a folklore conjecture with no known counterexample. Refuting positive expansion distinguishes this sufficient hypothesis from the extremality question itself.

## Gap

The positive-expansion conjecture appears as open in both cited collections. The 2023 section proposes continuity, evenness, convexity and nonnegativity as sufficient conditions; UP24 repeats these conditions in Conjecture 7.1. Coverage of the literature check is limited to the cited arXiv versions; absence of any other resolution remains ASSUMED-UNVERIFIED.

## Route

Take $n=6$ and

$$
\mu(x)=\max\left\{1,\frac{4860|x|-1078}{137}\right\},\qquad
P(x)=\frac{38656x^6-41568x^4+6831x^2-137}{137}.
$$

The maximum of the constant convex function and the positively scaled absolute-value function with an added constant is convex. Both functions are continuous and even, and $\mu\ge1$.

On $0\le x\le1/4$, the certificates are

$$
\begin{aligned}
137(1-P(x))&=(1-4x)(1+4x)(2416x^4-2447x^2+274),\\
137(1+P(x))&=x^2(38656x^4-41568x^2+6831).
\end{aligned}
$$

The right-hand sides are nonnegative there, giving $|P(x)|\le1$. On $1/4\le x\le1$, put $L(x)=(4860x-1078)/137$. Then

$$
\begin{aligned}
137(L(x)-P(x))&=(1-x)(4x-1)(9664x^4+12080x^3+2292x^2-155x+941),\\
137(L(x)+P(x))&=(4x-3)^2(2416x^4+3624x^3+1479x^2+180x-135).
\end{aligned}
$$

The quartic in the second identity equals

$$
\frac{137}{2}+(x-1/4)(2416x^3+4228x^2+2536x+814),
$$

so it is nonnegative on this interval. The first quartic is also nonnegative there, as established by `P_bound_large`. These certificates give $|P|\le\mu$ on $[0,1]`; evenness extends the bound to $[-1,1]$.

The seven contacts, in decreasing order, are

$$
1,\quad3/4,\quad1/4,\quad0,\quad-1/4,\quad-3/4,\quad-1,
$$

with polynomial values

$$
3782/137,\quad-2567/137,\quad1,\quad-1,\quad1,\quad-2567/137,\quad3782/137.
$$

They satisfy the alternating contact condition with the orientation specified in (b). Comparing the coefficients of $x^0,x^2,x^4,x^6$ in any Chebyshev representation forces its $T_0$ coefficient to be $-459/274$.

The conjecture is read in the orientation fixed by property (b), where the first contact carries the sign of the majorant. The opposite orientation $-P$ has the negated coefficient vector, whose $T_6$ coefficient $-1208/137$ is negative, so neither orientation has a non-negative Chebyshev expansion.

## Falsifier

The displayed $\mu$ and $P$ satisfy the majorant hypotheses and both snake conditions at $n=6$. The exact expansion is

$$
P=-\frac{459}{274}T_0+\frac{1503}{274}T_2
+\frac{2052}{137}T_4+\frac{1208}{137}T_6.
$$

The negative constant coefficient excludes an expansion in $T_0,\ldots,T_6$ with all coefficients nonnegative. This falsifies the universal positive-expansion assertion.

## Evidence

The public declarations in `D5/S3/Analytic/Chebyshev/SnakeChebyshevExpansionRefutation.lean` are `IsSnake`, `claim`, and `result`; the counterexample and supporting lemmas are private.

`IsSnake μ n ω` asserts `ω.natDegree ≤ n`, the pointwise bound on `Set.Icc (-1) 1`, and a strictly decreasing map `τ : Fin (n + 1) → ℝ` with endpoints in the interval and values `ω.eval (τ i) = (-1) ^ (i : ℕ) * μ (τ i)`. It encodes conditions (a) and (b), rather than uniqueness.

`claim` quantifies over all real functions continuous, nonnegative, even and convex on that interval, all `n : ℕ` and all real polynomials satisfying `IsSnake`. Its conclusion is an expansion over `Finset.range (n + 1)` in `Chebyshev.T ℝ (k : ℤ)` with a coefficient function `a : ℕ → ℝ` nonnegative at every index.

The lemmas `μ_continuous`, `μ_nonneg`, `μ_even`, and `μ_convex` establish the majorant hypotheses. `P_degree`, `P_bound_small`, `P_bound_large`, `P_bound_nonneg`, `P_bound`, and `P_snake` establish the snake conditions. `constant_coefficient_negative` proves that every degree-six Chebyshev representation of `P` has `a 0 = -459 / 274`. The theorem `D5.S3.Analytic.Chebyshev.SnakeChebyshevExpansionRefutation.result` has type `¬ claim`.

The axiom closure is $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$, with no `sorry` or additional axiom. The full displayed expansion is an exact polynomial calculation; the coefficient obstruction is the statement proved by the private Lean lemma.

## Triage

### What the settlement shows

1. **Proved (Lean) — the majorant hypotheses.** The explicit majorant is continuous, nonnegative, even and convex on $[-1,1]$. Its defining maximum also gives the stronger pointwise bound $\mu\ge1$.

2. **Proved (Lean) — the snake conditions.** The polynomial has degree at most six and satisfies (a) and (b) at the seven displayed points. In particular, it is nonzero since $P(0)=-1$.

3. **Proved (Lean) — the negative coefficient and refutation.** Every Chebyshev representation through degree six has $a_0=-459/274<0$, so no such representation has all coefficients nonnegative. Hence `claim` is false.

4. **Computed (exact polynomial calculation) — the expansion.** Substituting the usual formulas for $T_0,T_2,T_4,T_6$ gives the displayed expansion. The module proves the forced constant coefficient without a separate theorem for all four expansion coefficients.

5. **Open — general explanatory mechanism (mathematical reasoning).** In this example the flat part $\mu=1$ on $[-1/4,1/4]$ forces near-Chebyshev oscillation of amplitude one around zero, while the steep linear part forces large alternating values at $\pm3/4$ and $\pm1$. The constant term absorbs the difference between these scales. This is an interpretation of the contacts and expansion, not a formal theorem about a class of majorants.

6. **Open — stricter majorant classes and small degree.** Whether positive expansion holds for strictly convex majorants, under additional smoothness, or for every $n\le5$ is not settled by this degree-six, piecewise linear example.

7. **Open — Markov extremality.** The folklore conjecture that the snake polynomial is extremal in the Markov problem is untouched. Failure of a sufficient positive-expansion hypothesis does not show failure of extremality.

8. **Open — majorant classification.** UP24 Problem 7.1, asking for classes with nonnegative or sign-alternating expansions, remains open. The example excludes continuous even convex nonnegative majorants as a universal class for nonnegative expansion; it does not classify the smaller classes.

## ASSUMED-UNVERIFIED

Uniqueness of the snake polynomial up to orientation is quoted from the source and is not formalized. The identification with the source's associated snake uses its characterization by (a) and (b); the Lean refutation itself uses exactly those conditions.

Coverage of the literature check is limited to arXiv:2312.07754v1, the cited UP24 version arXiv:2504.04845, and Nikolov–Shadrin arXiv:1210.7795. An exhaustive literature or priority claim is unverified.
