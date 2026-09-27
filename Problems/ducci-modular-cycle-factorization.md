---
slug: ducci-modular-cycle-factorization
bibkey: fellman2023ducci
doi: 10.5281/zenodo.10160456
url: https://math.colgate.edu/~integers/x86/x86.pdf
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/DucciModularCycleFactorization.result
---

# Ducci Modular Cycle Factorization

## Problem

Fellman and Klyve, *INTEGERS* **23** (2023), Article #A86, Section 7, state:

> Conjecture 1. Every cocomposite cycle is a product of a constant cycle and two
> generating cycles.

and add: "This conjecture has been verified for all moduli up to 161. One
possible direction of proving this conjecture is to show that all cocomposite
cycles are a product of a cocomposite constant cycle and a coprime cycle, but we
have been unsuccessful on this front."

The game replaces the difference map of the classical Ducci game by
`[a b c d] ↦ [ab bc cd da]` on `(Z_n)^4`. A 4-tuple is in a cycle when iterating
returns it; by their Lemma 2 the entries of such a tuple are then either all
units or all non-units, and the cycle is called coprime or cocomposite
accordingly. A cycle is constant when its tuples have four equal entries. A
generator 4-tuple is `[1 x 1 x^{-1}]` with `x` a unit lying on a cycle, and a
cycle containing one is a generator cycle. Products are taken entry by entry.

## Motivation

The frozen theorem `D5/S3/Combinatorics/DucciModularCycleFactorization.result`
settles the conjecture affirmatively. The proof does not use the cocomposite
hypothesis, so it covers coprime cycles as well and reproves the authors' own
Theorem 13 by an argument that never inverts an entry.

## Gap

Their Theorem 13 builds the three factors as the tuples two steps earlier in the
cycles of `[abcd abcd abcd abcd]`, `[1 a^{-1}c 1 ac^{-1}]` and
`[bd^{-1} 1 b^{-1}d 1]`. The last two are written with inverses of the entries,
so the construction needs the entries to be units, which is exactly what fails on
a cocomposite cycle. The suggested repair, splitting a cocomposite cycle into a
cocomposite constant cycle and a coprime cycle, is what the recorded proof
carries out, but through explicit powers of one entry product rather than through
a splitting of the ring.

## Route

Let `u` lie on a cycle, `step^[L] u = u`, and write `Q = u_0 u_1 u_2 u_3`. Three
identities come from the exponent vectors of the iterated map, all of them
visible in the source's own displays.

`Q` squares at every move, so `Q = Q^{2^L}`. The second move sends opposite
corners to `Q`, giving both `u_0 u_2 = u_1 u_3` and `u_0 u_2 = Q^{2^{L-1}}`. The
third move has exponent vector `(1,3,3,1)`, so every entry of `u` is divisible by
`Q`. The fourth move has exponent vector `(2,4,6,4)`, so every entry of
`step^[4] v` is a square; iterating, every entry of `u` is a `2^k`-th power for
every `k`.

The squaring map of the finite ring `Z_n` has `sq^[i] = sq^[j]` for some `i < j`,
and with `t = j - i` every `2^k`-th power with `k ≥ i` satisfies `z^{2^t} = z`.
Choosing `L` a large multiple of the period makes this apply to `Q` and to all
four entries at once.

Put `D = 2^t - 1`, `ε = Q^D`, `α = Q^{2^{L-2}}`, `e = 2^{L-2}` and
`αinv = Q^{(e+1)D - e}`. Then `ε` is idempotent, absorbs every positive power of
`Q` and every entry of `u`, `α² = u_0 u_2` and `α · αinv = ε`. With
`w_0 = u_1 u_2 u_3 Q^{D-1}` and `w_1 = u_0 u_2 u_3 Q^{D-1}` one has
`u_0 w_0 = u_1 w_1 = ε`, and

    x = u_1 · αinv + 1 - ε,   x^{-1} = α w_1 + 1 - ε,
    y = u_0 · αinv + 1 - ε,   y^{-1} = α w_0 + 1 - ε

are inverse to each other, the cross terms vanishing because
`αinv · ε = αinv` and `α · ε = α`. The factors are `A = [α α α α]`,
`B = [1 x 1 x^{-1}]` and `C = [y 1 y^{-1} 1]`, and the four entry identities are
`α y = u_0`, `α x = u_1`, `α² w_0 = u_2` and `α² w_1 = (u_1 u_3) w_1 = u_3`.

`A` returns after `t` moves. Four moves send `[1 x 1 x^{-1}]` to
`[1 x^{-4} 1 x^4]`, so eight moves raise the unit to the sixteenth power and `B`
returns after `8t` moves; `C` is `B`'s shape turned by one corner, the map
commutes with that turn, and two moves put `C` on a generator 4-tuple.

## Falsifier

A cycle carrying a tuple whose four entries do not all have the same greatest
common divisor with `n` would refute the conjecture outright, since `x` and `y`
are units. The route also fails if `x^{2^t} = x` fails, that is if some entry of a
periodic tuple has even multiplicative order on the part of `Z_n` where it is
invertible.

## Evidence

Exhaustive check over `n ∈ {6,10,12,15,20,21,22,26,30,33,35,39,45}`: all `n^4`
tuples were reduced to the periodic ones as the image of `step^{2^k}` with
`2^k ≥ n^4`, giving 810 periodic tuples of which 411 are cocomposite. For each
one the construction above was recomputed and every step checked: `Q^{2^t} = Q`,
`ε` idempotent, `u_i ε = u_i`, `α² = u_0 u_2`, `α · αinv = ε`, `u_i w_i = ε`,
`x x^{-1} = 1`, the four entry identities, `x^{2^t} = x`, membership of `A`, `B`
and `C` in the periodic set, `step^[8t] B = B`, and `step^[2] C` a generator
4-tuple. No violation occurred.

The smallest cocomposite cycles already show why the entries cannot be inverted:
modulo 6 the periodic tuples are `[0 0 0 0]`, `[1 1 1 1]`, `[3 3 3 3]` and
`[4 4 4 4]`, and the last two are cocomposite with `Q = 3` and `Q = 4`
respectively, both idempotent.

## Triage

`theorem`; Tier 1 named external open question, preregistered in issue 9336
before the construction was formalised. The admission basis is `escape-witness`
with `proof_shape: content`; the declared escape content is the product invariant
`Q(step u) = Q(u)^2`, the exponent vectors of the third and fourth moves, the
pigeonhole exponent `t`, and the orthogonal idempotent splitting that makes `x`
a unit. The computational use is `none`: the delivered statement is a universally
quantified theorem with no bounded enumeration, checker, numeric reduction or
certified instance among its declarations.

## ASSUMED-UNVERIFIED

The literature screen is bounded: the article PDF and the Zenodo record 10160456
were opened, a full-text arXiv search for the coined term "cocomposite" returned
no hits, and the recent arXiv work listed under "Ducci" treats the additive game
on `Z_m^n`. INTEGERS is not indexed in Crossref and citation-index result pages
were not reachable, so no worldwide priority claim is made.

The numerical check covers moduli below the range the authors report having
checked; it supports the construction rather than the statement, which the
recorded theorem settles for every modulus.
