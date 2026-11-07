---
slug: occil-convex-bernstein-corrections
bibkey: occil2026bernreq
url: https://peteroupc.github.io/bernreq.html#Other_Questions
triage: theorem
motivation_gids:
  - D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.result
---

# Both convex Bernstein correction prescriptions fail

## Problem

Peter Occil, *Open Questions on the Bernoulli Factory Problem*, “Other Questions”,
first item after the final “Prove or disprove”, asks:

> Given that $f:[0,1]\to (0,1]$ is convex, the polynomials $(g_n) = (B_n(f) - \max\lbrace\text{abs}(B_n(f)(\lambda)-f(\lambda))) : 0\le\lambda\le 1\rbrace$ (where $n$ is a positive integer power of 2) are in Bernstein form of degree $n$, converge to $f$ from below, and satisfy: $(g_{2n}-g_{n})$ is a polynomial with nonnegative Bernstein coefficients once it's rewritten to a polynomial in Bernstein form of degree exactly $2n$. The same is true for the polynomials $(g_n) = (B_n(f) - \text{abs}(B_n(f)(1/2)-f(1/2)))$, if $f$ is also symmetric about 1/2.

The [Library source note](../Library/Analytic/occil2026bernreq.md) pins the
original text and basis convention. The unchanged coefficient conjunction,
its exact quantifiers and prospective registration are
[issue #27489](https://github.com/the-omega-institute/trureturing/issues/27489#issuecomment-6698804052).
This is an author-published Tier 1 question, with first publication unknown.
The supplied completed qualification is reused; the source check here confirms
the pinned assertion, not an exhaustive literature or priority search.

## Motivation

A nonnegative polynomial on the interval need not have nonnegative Bernstein
coefficients at a fixed representation degree. The source's coefficient
monotonicity is stronger than pointwise monotonicity of lower approximants.

## Gap

The formal target is the full registered universal coefficient conjunction.
The maximum-error branch quantifies over actual attained maxima at both
scales; the midpoint branch quantifies over symmetric functions without a
maximum premise. No continuity assumption is introduced. The result refutes
the coefficient requirement in each original branch; it does not require
choosing a convergence topology or disproving convergence separately.

## Route

Take $f(x)=x^2-x+1/2=(x-1/2)^2+1/4$ and $n=2=2^1$.
Its values lie in $(0,1]$ on $[0,1]$, it is convex, and $f(1-x)=f(x)$.
The native proof checks the convexity inequality for every permitted pair
and weight. Direct polynomial identities give

$$
B_2f(X)=	frac12(X^2-X)+	frac12,\qquad
B_4f(X)=	frac34(X^2-X)+	frac12.
$$

For every $x\in[0,1]$, the two errors are $x(1-x)/2$ and $x(1-x)/4$.
Their actual maxima, attained at $x=1/2$, are $1/8$ and $1/16$.
These are also the two midpoint absolute errors. Thus both prescriptions
have the identical increment

$$
p(X)=	frac1{16}-	frac14X(1-X)
     =	frac14(X-1/2)^2.
$$

Its exact degree-4 normalized Bernstein representation is

$$
p(X)=\sum_{j=0}^4 c_j\binom4jX^j(1-X)^{4-j},\qquad
(c_0,c_1,c_2,c_3,c_4)=(1/16,0,-1/48,0,1/16).
$$

The real coefficient vector is unique: map a competing polynomial identity
to complex coefficients, apply the existing complex Bernstein independence
theorem, and use injectivity of the real embedding. Hence no competing
nonnegative coefficient representation exists.

## Falsifier

A different sample operator, unnormalized basis, representation degree,
correction term, domain or maximum interpretation would answer a different
question. Every one of these is explicit in the native definitions. The
proof uses identities for all real inputs and interval-wide inequalities,
not numerical samples or finite positivity testing.

## Evidence

The source is
[OccilBernsteinCorrectionRefutation.lean](../D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.lean).
`claim : Prop` is the conjunction of the universal maximum and midpoint
branches; `result : Not claim` is its literal negation. The private consumed
`branch_refutations` proves the negation of each universal branch.
`nonnegativeCoefficients` asks for a nonnegative normalized representation;
`realization_unique` identifies that representation with the displayed vector.
All newly authored helpers are private and consumed. The sole public theorem
is the designated refutation result, exempt from four-slot registration.
The proposed admission basis is `open-problem-resolution`, not a claim of a new escape witness;
normalization and binding steps are not counted as new mathematical content.

## Triage

- The unchanged registered coefficient conjunction is the native refutation target.
- The same candidate gives a negative degree-4 coefficient in each original branch.
- Independent prefreeze fidelity, proof-shape and mirror review remains outstanding.
- No conclusion about all alternative correction schemes or general Bernoulli-factory
  existence follows. Convergence of these particular approximants is not refuted.
- Freeze, publication and resolution counting are outside this delivery.
