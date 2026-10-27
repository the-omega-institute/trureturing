---
slug: javaheri-2026-cyclic-arrangement-conjecture-refutation
bibkey: javaheri2026arrangement
doi: 10.48550/arXiv.2610.33653
url: https://arxiv.org/abs/2610.33653v1
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Polynomials/JavaheriArrangementDimensionRefutation.result
---

# Refutation of Javaheri's cyclic arrangement dimension conjecture

## Problem

Mohammad Javaheri, *A new arrangement inequality (revised and extended
version)*, arXiv:2610.33653v1, Section 1, Conjecture 1.3, states that for all
real a,b ≥ 0 with a+b ≠ 1, the largest dimension N(a,b) for which

    (Σᵢ xᵢ)(Σᵢ xᵢᵃ xᵢ₊₁ᵇ) ≤ (Σᵢ xᵢ^((a+b+1)/2))²

holds for every nonnegative cyclic tuple equals

    N*(a,b) = max { n ≥ 1 : n = 1 or
        (a+b−1)² ≤ 8ab sin²(π/n) }.

The cyclic successor is xₙ₊₁ = x₁. The source writes the largest valid
dimension and the threshold maximum as named quantities. The Lean encoding
makes those implicit extrema explicit: `IsN` is the extended-natural
least-upper-bound predicate for the set of valid positive dimensions, and
`IsNStar` is the greatest-element predicate for the threshold set. It then
states the full universal claim together with existence of the two specified
objects, so the refutation does not depend on an underspecified maximum.

The claim was preregistered in GitHub issue [#22620](https://github.com/the-omega-institute/trureturing/issues/22620)
before the Lean probe and proof.

## Motivation

At a=6 and b=1, the threshold condition is 36 ≤ 48 sin²(π/n). It holds at
n=3, because sin²(π/3)=3/4, and the explicit n=1 exception is also present.
For every n ≥ 4, monotonicity of sine on the relevant interval gives
sin²(π/n) ≤ 1/2, so the threshold inequality fails. Thus the threshold set
has greatest element 3.

At the same parameters, use the nonnegative cyclic tuple (6,5,5). With
c=(6+1+1)/2=4, the difference between the left and right sides is exactly

    (6+5+5)(6^6·5 + 5^6·5 + 5^6·6) − (6^4+5^4+5^4)^2 = 364 > 0.

Therefore dimension 3 is not valid. If the published identity held at (6,1),
its asserted value would be 3, while the least-upper-bound specification of
valid dimensions cannot be 3 when 3 is absent. The kernel-checked theorem
`result : ¬ claim` formalizes this contradiction.

## Gap

The source is explicitly conjectural. The bounded literature and repository
screen recorded in issue #22620 found no prior proof or refutation of this
revised statement in the searched surfaces. The revised arXiv source was
read; the 2006 journal predecessor was not treated as the same statement.
No claim of exhaustive literature coverage or publication priority is made.

## Evidence

- Source: [arXiv:2610.33653v1](https://arxiv.org/abs/2610.33653v1), Section 1,
  Conjecture 1.3.
- Frozen Lean declaration:
  `D5/S0/Certificates/Polynomials/JavaheriArrangementDimensionRefutation.result`.
- The declaration has type `Not claim` and is checked by the pinned Lean
  kernel without `sorry` or a project-specific axiom.
- The proof uses exact real arithmetic and the analytic sine bounds in the
  pinned library; the displayed 364 is an exact integer difference.

## Triage

`theorem`; resolution `refuted` for the literal universal identity in
Conjecture 1.3. The public settling theorem is `result : ¬ claim`; its proof
shape is `bind-only`, with no escape witness, and its admission basis is the
preregistered external open-problem resolution in issue #22620. The result is
a certified instance refutation; it does not assert a corrected formula for
the largest valid dimension, settle the source's other parameter pairs, or
make finite arithmetic screening itself a Lean proof.

## ASSUMED-UNVERIFIED

The literature check is bounded to the source and repository/search surfaces
recorded above and in issue #22620. It does not establish worldwide absence,
novelty, or priority. The refutation settles only the literal universal
conjecture as encoded; any stronger corrected theorem remains open.
