---
bibkey: li2026concavity
authors: Yulong Li; Rachel Morgan; Michael Siegrist
year: 2026
title: Concavity structure of fractional differential equations and zeros of Mittag–Leffler functions
doi: 10.1007/s41478-026-01192-9
url: https://link.springer.com/article/10.1007/s41478-026-01192-9
claim: Conjecture 6.1 asserts a unique sign-changing zero of the second derivative under the hypotheses of Theorem 5.2.
strata_touched:
  - D5/S0/Certificates/LiMorganSiegristInflectionRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1007/s41478-026-01192-9

Source: https://link.springer.com/article/10.1007/s41478-026-01192-9

PDF: https://link.springer.com/content/pdf/10.1007/s41478-026-01192-9.pdf

The locators below use PDF page numbers. The publisher's HTML identifies the same
numbered definition, equation, theorem and conjecture.

## Source statements

Definition 1.1, PDF p. 2:

> For α > 0, the left-sided Riemann–Liouville fractional integral of a locally integrable function u is defined by I^α_{a+}u(x) = (1/Γ(α)) ∫_a^x (x − t)^{α−1} u(t) dt, x > a, whenever the integral is finite.

Section 3, equation (7), PDF p. 11, says that the weak solution

> is equivalently represented by u(x) = (I^α_{0+}f)(x) + c x^{α−1}, c = −(I^α_{0+}f)(1), x ∈ [0, 1]. (7) Conversely, the function defined by this formula is the unique weak solution

Theorem 5.2, PDF p. 27:

> Let f ∈ C([0, 1]) ∩ C¹((0, 1]) satisfy f(1) = 0 and f ≥ 0 on [0, 1], with f ≢ 0. Assume, in addition, that lim_{x→0+} x^{(3−α)/(2−α)} f′(x) = 0.

Conjecture 6.1 (Uniqueness of the concavity transition), PDF p. 43:

> Let 1 < α < 2. Under the hypotheses of Theorem 5.2, the second derivative F″ has exactly one zero in (0, 1). Moreover, F″ changes sign at this zero, so that this point is the unique inflection point of F.

The same page states:

> At present, even the uniqueness of the inflection point remains open

## Formal interpretation

The lower integration endpoint is zero. The function `solution` is equation (7),
with the boundary constant substituted. `Hypotheses` expresses continuous
regularity on the closed interval, first-order smoothness on the half-open
interval, the endpoint value, nonnegativity, nontriviality and the right-sided
weighted derivative limit. `claim` quantifies over all real orders between one
and two and all admissible real forcings. Its conclusion is one interior zero,
uniqueness among all interior zeros, and opposite strict signs at every nearby
pair on opposite sides. The derivative is `iteratedDeriv 2`.

The kernel proof refutes this proposition using order 3/2 and forcing
`(1 − x)(1 + 5x¹²)`. It proves at least two distinct zeros. It does not assert
an exact zero count, simplicity, or an independently formalized equivalence
between the integral representation and the fractional Sobolev weak solution.

## Literature status

The source explicitly labels Conjecture 6.1 open. The literature screen in
issue #18772 includes fractional-concavity references, Mittag–Leffler zero
references, source citations, formal-conjectures, this repository and its
issues. No settlement was identified there. Completeness of that screen is
ASSUMED-UNVERIFIED. The forcing counterexample leaves the source's at-least-one
conclusion and its principal-eigenfunction zero question distinct.
