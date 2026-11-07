---
bibkey: occil2026bernreq
authors: Peter Occil
year: 2026
doi: null
title: "Open Questions on the Bernoulli Factory Problem"
url: https://peteroupc.github.io/bernreq.html#Other_Questions
claim: "The first convex correction question after the final Prove or disprove asks for nonnegative degree-2n Bernstein increment coefficients under maximum-error and symmetric midpoint-error corrections."
strata_touched:
  - D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation
license: citation-only
triage: anchor
---

# Original convex Bernstein correction question

## Verified locator

Author-published page: https://peteroupc.github.io/bernreq.html#Other_Questions

The author-published source is the first item after the final “Prove or disprove”
in “Other Questions”. Its source version is 2026-10-17; the same assertion
is present in the qualified 2025-04-29 version. First publication is unknown.
The immutable source is
[bernreq.md at ec9ea9783cd27a7169f0bf3e3e344286f14babe3](https://github.com/peteroupc/peteroupc.github.io/blob/ec9ea9783cd27a7169f0bf3e3e344286f14babe3/bernreq.md).
The complete pinned Markdown has SHA-256
`b56b77734cd4f49570c822f9c9f33cc9df250b463c592e74582432f37a8233c6`.

> Given that $f:[0,1]\to (0,1]$ is convex, the polynomials $(g_n) = (B_n(f) - \max\lbrace\text{abs}(B_n(f)(\lambda)-f(\lambda))) : 0\le\lambda\le 1\rbrace$ (where $n$ is a positive integer power of 2) are in Bernstein form of degree $n$, converge to $f$ from below, and satisfy: $(g_{2n}-g_{n})$ is a polynomial with nonnegative Bernstein coefficients once it's rewritten to a polynomial in Bernstein form of degree exactly $2n$. The same is true for the polynomials $(g_n) = (B_n(f) - \text{abs}(B_n(f)(1/2)-f(1/2)))$, if $f$ is also symmetric about 1/2.

## Convention and scope

The source defines a degree-r Bernstein form as

$$P(X)=\sum_{j=0}^r a_j\binom rj X^j(1-X)^{r-j}.$$

Its Bernstein approximation uses the original samples $a_j=f(j/r)$.
The formal claim retains real scalars, $0<f\le1$ on the entire closed interval,
convexity on that interval and the dyadic scales $n=2^k$, $k\ge1$.
An attained maximum means both a uniform absolute-error bound and an actual
attainer. There is no continuity premise or substitution of a supremum.
The symmetric branch uses its actual midpoint absolute error and has no
maximum premise. Representation degree is exactly $2n$, even if the
polynomial's ordinary degree is smaller.

The coefficient conjunction is preregistered in
[issue #27489](https://github.com/the-omega-institute/trureturing/issues/27489#issuecomment-6698804052).
Failure of either coefficient requirement refutes the corresponding full
source conjunction, independently of its unspecified convergence topology.
Truth of coefficient positivity alone would not establish convergence.

## Attribution and reuse

The question and basis convention are Occil's. The quadratic counterexample
and its source-specific deduction are repository work; no publication-priority
claim is made. Existing repository complex Bernstein independence supplies
the uniqueness bridge for real coefficients via the injective real embedding.
The source text is quoted for attribution; no source program is incorporated.
