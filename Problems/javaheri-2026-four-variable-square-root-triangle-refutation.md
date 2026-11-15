---
slug: javaheri-2026-four-variable-square-root-triangle-refutation
bibkey: javaheri2026arrangement
doi: 10.48550/arXiv.2610.33653
url: https://arxiv.org/abs/2610.33653v1
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Polynomials/JavaheriFourVariableTriangleRefutation.result
---

# Refutation of the four-variable square-root triangle prediction

## Problem

Javaheri's revised preprint, Section 8, PDF page 10, states:

> Taking n = 4, Conjecture 1.3 and Lemma 4.3 predict that (1.1) holds for
> n = 4 exactly when sqrt(a), sqrt(b), 1 form a triangle.

The complete assertion is: for every real a,b >= 0, with c=(a+b+1)/2,

    [for every nonnegative real quadruple,
       (sum_i x_i)*(sum_i x_i^a*x_(i+1)^b) <= (sum_i x_i^c)^2]
    iff
    [sqrt(a)<=sqrt(b)+1 and sqrt(b)<=sqrt(a)+1 and 1<=sqrt(a)+sqrt(b)].

Every sum has indices 1 through 4 and x_5=x_1, in the given cyclic order.
Powers use `Real.rpow`, including 0^0=1. This convention is implicit in the
source and explicit in the formal claim. Zero parameters, zero coordinates,
the all-zero quadruple, the line a+b=1, and all degenerate triangle boundaries
are included. Lemma 4.3 supports the weak interpretation through the
non-strict condition (a+b-1)^2 <= 4ab.

The complete event is separately registered in
[#30729](https://github.com/the-omega-institute/trureturing/issues/30729),
with its unchanged strict statement in
[comment 6890176505](https://github.com/the-omega-institute/trureturing/issues/30729#issuecomment-6890176505).
It is distinct from the already refuted general dimension identity owned by
[the parent dossier](javaheri-2026-cyclic-arrangement-conjecture-refutation.md).

## Motivation

The source's necessary second-variation condition is larger than the known
linear sufficient region b<=a+1, a<=b+1, 1<=a+b of Proposition 3.1.
The n=4 prediction asserts sufficiency throughout that larger weak region.
Testing its boundary distinguishes this assertion from the known theorem.

## Gap

The scoped source and literature screen in issue #30729 inspected the revised
v1, arXiv author/topic results, eight Crossref results, selected introductory
and theorem statements of arXiv:2301.00679v1, and the repository's Javaheri
ownership. No complete n=4 resolution was found within that scope. This is
neither an exhaustive literature survey nor a novelty or priority claim.

## Route

The formal claim reuses the existing `arrangementInequality` and `c`
definitions from `JavaheriArrangementDimensionRefutation`. It specializes
the full claimed equivalence at a=4, b=1. The square-root triangle condition
holds, so its reverse implication would force the inequality for the
positive tuple (10,9,7,7). Exact arithmetic contradicts that conclusion.
The settling declaration has the literal type `Not claim`, with `claim : Prop`.

## Falsifier

At a=4, b=1, c=3, the square-root sides are 2,1,1. Their three weak triangle
inequalities hold, including 2=1+1. For x=(10,9,7,7),

    sum x_i = 33,
    sum x_i^4*x_(i+1) = 90000+45927+16807+24010 = 176744,
    sum x_i^3 = 1000+729+343+343 = 2415.

Consequently,

    33*176744 - 2415^2 = 5832552 - 5832225 = 327 > 0.

Every coordinate and exponent in this counterexample is positive, so the
implicit source convention for 0^0 does not affect this contradiction.

## Evidence

- Primary source: arXiv:2610.33653v1, Section 1, Proposition 3.1,
  Lemma 4.3, and Section 8, PDF page 10.
- Inspected primary PDF SHA256:
  `7e6a3de06d5279fd41b67322c600f6333621492096ba9d2878779bf74a1e1c6b`.
- Settling declaration:
  `D5/S0/Certificates/Polynomials/JavaheriFourVariableTriangleRefutation.result`.
- The Lean proof checks the weak triangle premises, tuple nonnegativity,
  cyclic evaluation and contradiction by exact arithmetic.

## Triage

`theorem`; resolution `refuted` for the complete weak square-root triangle
characterization. The settling theorem is bind-only; its admission basis is
external open-problem resolution #30729, with no escape witness. The parent
dimension refutation is reused for definitions only and is not a new result.

### What the settlement shows

- **Proved — failure mechanism:** `JavaheriFourVariableTriangleRefutation.result`
  refutes the full assertion because the weak triangle condition at (4,1)
  does not imply global validity for all nonnegative quadruples. The failure
  occurs on a degenerate triangle boundary, with strictly positive data.
- **Computed — exact excess:**
  `python3 -c 'print(33*(10**4*9+9**4*7+7**4*7+7**4*10)-(10**3+9**3+7**3+7**3)**2)'`
  returns `327`; the formal proof independently checks the contradiction.
- **Open — surviving and corrected questions:** Proposition 3.1's smaller
  linear region and Theorem 1.2's necessary condition are source theorems;
  their independent formal verification is not supplied here. The formal
  certificate directly concerns the weak boundary. A quantitative
  description of validity and failure in the strict interior, and a complete
  corrected validity region, remain open here; no strict-interior
  characterization is asserted.
- **Proved — effect on the source prediction:** the separately stated n=4
  weak characterization is false, in addition to the parent dimension
  identity. This result does not verify or refute the source's other
  independent results, numerical observations, or strict-interior claims.

## ASSUMED-UNVERIFIED

The bounded literature screen does not establish worldwide absence of a
prior resolution, novelty, or priority.
