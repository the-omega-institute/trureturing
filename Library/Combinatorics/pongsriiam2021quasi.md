---
bibkey: pongsriiam2021quasi
authors: Prapanpong Pongsriiam
year: 2021
title: "Quasi-Injectivity of Some Arithmetic Functions"
doi: null
url: https://cs.uwaterloo.ca/journals/JIS/VOL24/Pongsriiam/pong23.pdf
claim: "Question 17 asks whether, for each m at least two, some function is quasi-injective of order m-1 but not of order m."
strata_touched:
  - D5/S3/Combinatorics/QuasiInjectiveOrderSeparation
license: citation-only
triage: anchor
---

# Pongsriiam quasi-injectivity of arithmetic functions

## Verified locator

URL: https://cs.uwaterloo.ca/journals/JIS/VOL24/Pongsriiam/pong23.pdf

DOI: none assigned; *Journal of Integer Sequences* **24** (2021), Article 21.10.1.
The journal does not mint a DOI for this article and no preprint version is
listed on the author's publication page, so the journal PDF is the locator.

## Definitions

Definition 1 reads:

> We call a function `f : N → C` a quasi-injective function if for all `a, b ∈ N`,
> the condition `f(an) = f(bn)` for all `n ∈ N` implies `a = b`. In addition, if
> `f : N → N` and `ℓ ∈ N`, then we say that `f` is quasi-injective of order `ℓ`
> if `f, f^(2), f^(3), …, f^(ℓ)` are quasi-injective, that is, for any
> `a, b, k ∈ N` with `1 ≤ k ≤ ℓ`, if `f^(k)(an) = f^(k)(bn)` for all `n ∈ N`,
> then `a = b`.

Here `f^(k)` is the `k`-fold composite and `N` is the set of positive integers.
The article notes immediately that quasi-injectivity of order `ℓ` implies
quasi-injectivity of every order `m ≤ ℓ`, so the orders form a decreasing chain
of conditions.

## What the article settles

`τ = σ_0` is quasi-injective of every order (Theorem 7), and the same holds for
the Jordan totient functions `J_s`. For the divisor-power sums `σ_s` the article
proves quasi-injectivity of order two and no further; Question 16 asks about the
higher orders. So none of the functions studied there separates two consecutive
orders, which is what Question 17 asks for.

## The statement in question

Section 5 states:

> Question 17. For each `m ≥ 2`, is there a function `f : N → N` such that `f` is
> quasi-injective of order `m − 1` but not of order `m`?

## Scope of the recorded answer

Yes, for every `m ≥ 2`. Give an odd number `2t + 1` with `t ≥ 1` the level
`t mod (m − 1)`, and let

    g_m(1)     = 1
    g_m(2t)    = 2(m − 1)t + 1                               (t ≥ 1)
    g_m(2t+1)  = 1        if t mod (m − 1) = (m − 2) mod (m − 1)
    g_m(2t+1)  = 2t + 3   otherwise.

So `g_m` raises the level by one, sends the top level to `1`, fixes `1`, and
sends an even number into level zero of the ladder. For `1 ≤ k ≤ m − 1` and
`t ≥ 1` the `k`-fold composite satisfies

    g_m^(k)(2t) = 2((m − 1)t + k − 1) + 1 ,

which is strictly increasing in `t`, so `n = 2` separates any two distinct
multipliers and `g_m` is quasi-injective of order `m − 1`. Every input reaches
`1` within `m` steps, so `g_m^(m)` is constantly `1`; taking `a = 1` and `b = 2`
shows quasi-injectivity of order `m` fails.

Entering the ladder only through the even numbers is the load-bearing choice.
Reading the level off the exponent of two in `n` instead breaks at order one
already: the multipliers `a = 2^{m−1}` and `b = 2^m` then give
`g^(k)(an) = g^(k)(bn) = 1` for every `n` and every `k ≥ 1`.

## Bounded prior-resolution evidence

The journal article and its HTML record were opened. The author's publication
page lists this as the only item on quasi-injectivity and shows no follow-up.
The one paper in the screened corpus that cites it, Pongsriiam, *J. Integer Seq.*
**26** (2023), Article 23.9.1, cites it only in the reference list and does not
treat orders of quasi-injectivity. Web search for the phrase "quasi-injective of
order" returns only the unrelated module-theoretic and order-theoretic senses.
Citation-index result pages were not reachable, so this is a bounded negative
finding and no worldwide priority claim is made.
