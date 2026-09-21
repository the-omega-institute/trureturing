---
slug: quasi-injective-order-separation
bibkey: pongsriiam2021quasi
doi: null
url: https://cs.uwaterloo.ca/journals/JIS/VOL24/Pongsriiam/pong23.pdf
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/QuasiInjectiveOrderSeparation.result
---

# Quasi-Injective Order Separation

## Problem

Pongsriiam, *Journal of Integer Sequences* 24 (2021), Article 21.10.1,
Definition 1, reads: "We call a function `f : N → C` a quasi-injective function
if for all `a, b ∈ N`, the condition `f(an) = f(bn)` for all `n ∈ N` implies
`a = b`. In addition, if `f : N → N` and `ℓ ∈ N`, then we say that `f` is
quasi-injective of order `ℓ` if `f, f^(2), f^(3), …, f^(ℓ)` are quasi-injective,
that is, for any `a, b, k ∈ N` with `1 ≤ k ≤ ℓ`, if `f^(k)(an) = f^(k)(bn)` for
all `n ∈ N`, then `a = b`." Section 5 asks:

> Question 17. For each `m ≥ 2`, is there a function `f : N → N` such that `f` is
> quasi-injective of order `m − 1` but not of order `m`?

## Motivation

The frozen theorem
`D5/S3/Combinatorics/QuasiInjectiveOrderSeparation.result` answers it
affirmatively for every `m ≥ 2` by an explicit family. The orders form a
decreasing chain of conditions, and the article's own examples do not separate
two consecutive links: `τ` and the Jordan totients are quasi-injective of every
order, and for `σ_s` only order two is established.

## Gap

The journal article and its HTML record were opened; the author's publication
page lists this as his only item on quasi-injectivity and shows no follow-up; the
one citing paper in the screened corpus, Pongsriiam, *J. Integer Seq.* 26 (2023), Article 23.9.1,
cites it only in the reference list and does not treat orders. Web search for
"quasi-injective of order" returns only the module-theoretic and order-theoretic
senses of the phrase. Citation-index result pages were not reachable, so this is
a bounded negative finding.

## Route

Fix `m ≥ 2`. Give an odd number `2t + 1` with `t ≥ 1` the level
`t mod (m − 1)`, and define

    g_m(1)     = 1
    g_m(2t)    = 2(m − 1)t + 1                               (t ≥ 1)
    g_m(2t+1)  = 1        if t mod (m − 1) = (m − 2) mod (m − 1)
    g_m(2t+1)  = 2t + 3   otherwise.

`g_m` raises the level by one, sends the top level to `1`, fixes `1`, and sends
an even number into level zero.

Two facts follow. First, for `1 ≤ k ≤ m − 1` and `t ≥ 1`,

    g_m^(k)(2t) = 2((m − 1)t + k − 1) + 1 ,

by induction on `k`: the first step gives `2((m − 1)t) + 1`, whose level is zero,
and each later step raises the level by one, so at step `k` the level is `k − 1`,
which stays below the top level `m − 2` as long as `k ≤ m − 1` and the collapse
branch is never taken. Second, `g_m^(m)` is constantly `1`: an even number needs
one step to enter, `m − 2` to climb and one to collapse; an odd number at level
`j` needs `m − j` steps; zero and one go to `1` at once, and `1` is fixed.

The first fact gives quasi-injectivity of order `m − 1`: if
`g_m^(k)(an) = g_m^(k)(bn)` for all `n` and some `1 ≤ k ≤ m − 1`, take `n = 2` to
get `2((m − 1)a + k − 1) + 1 = 2((m − 1)b + k − 1) + 1`, hence `(m − 1)a =
(m − 1)b` and `a = b`. The second gives the failure at order `m`: with `k = m`,
`a = 1` and `b = 2`, both sides are `1` for every `n` while `1 ≠ 2`.

## Falsifier

A single `m` on which `g_m^(m)` is not constantly `1`, or a single `1 ≤ k ≤ m−1`
together with `a ≠ b` for which `g_m^(k)(an) = g_m^(k)(bn)` holds for every `n`,
would invalidate the family. The second is the sharper test: reading the level
off the exponent of two in `n` instead of the entrance-by-even design fails it at
order one, because `a = 2^{m−1}` and `b = 2^m` then give
`g^(k)(an) = g^(k)(bn) = 1` for every `n` and every `k ≥ 1`.

## Evidence

An independent implementation checks, for `m = 2, …, 12`: `g_m^(m)(n) = 1` for
every `n < 4000`; the closed form `g_m^(k)(2t) = 2((m − 1)t + k − 1) + 1` for
every `1 ≤ k ≤ m − 1` and `t < 300`; that `a ↦ g_m^(k)(2a)` has no collision for
`a < 400`; and that `a = 1`, `b = 2` give equal `m`-fold values for every
`n < 4000`. There were no mismatches. This is a check of the family, not of the
theorem: the theorem is proved for every `m`.

At `m = 2` the family degenerates to `g_2(2t) = 2t + 1` and `g_2(2t+1) = 1` for
`t ≥ 1`, whose square is constantly `1`.

## Triage

`theorem`; Tier 1 named external open question, preregistered in issue 9295
before implementation. The admission basis is `open-problem-resolution`. The
classification is `proof_shape: content`; the escape content is the closed form
for the iterates on even inputs together with the collapse of the `m`-fold
composite, neither of which is an instantiation, projection or normalisation of
a pinned upstream statement. The computational content classification is `none`:
the delivered statement is a theorem for every order, and the check above stays
outside the module.

## ASSUMED-UNVERIFIED

The literature screen is bounded: the journal article and its HTML record, the
author's publication page, and the one citing paper in the screened corpus were
opened; citation-index result pages were not reachable, so no worldwide priority
claim is made.

Question 16 of the article, whether `σ_s` is quasi-injective of every order, and
Questions 18 and 19, on composites of `τ`, `σ_s` and `J_s` and on compositions of
quasi-injective functions, are not settled here.

The family `g_m` is one witness per order and is not claimed to be canonical or
minimal among the functions separating order `m − 1` from order `m`; in
particular no arithmetic function of the kind studied in the article is shown to
have this property.
