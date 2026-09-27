---
bibkey: fellman2023ducci
authors: Tasha Fellman, Dominic Klyve
year: 2023
title: "Existence of Cycles in Ducci's Four-Number Game with Modular Multiplication"
doi: 10.5281/zenodo.10160456
url: https://math.colgate.edu/~integers/x86/x86.pdf
claim: "Section 7 states Conjecture 1, that every cocomposite cycle is a product of a constant cycle and two generating cycles, verified for all moduli up to 161."
strata_touched:
  - D5/S3/Combinatorics/DucciModularCycleFactorization
license: citation-only
triage: anchor
---

# Fellman and Klyve, cycles of the modular multiplicative Ducci game

## Verified locator

DOI: 10.5281/zenodo.10160456

URL: https://math.colgate.edu/~integers/x86/x86.pdf

*INTEGERS* **23** (2023), Article #A86. Received 2/1/23, revised 7/7/23, accepted
10/27/23, published 11/20/23. The Zenodo record 10160456 carries the same text
under the plural title "Four-Number Games"; the journal page and the article PDF
both read "Four-Number Game". Authors and title match both records.

## Definitions

Section 1 replaces the difference map of the classical Ducci game by the product
map on `(Z_n)^4`,

    [a b c d] ↦ [ab bc cd da].

Section 2 calls two 4-tuples equivalent when one is carried to the other by the
symmetries of the square, and says a 4-tuple is in a cycle when iterating the
game some `L + 1` times returns a tuple equivalent to it. Since every symmetry
`σ` satisfies `T ∘ R_σ = R_{σ'} ∘ T` with `σ'` again a symmetry, and rotations
commute with `T`, iterating carries the tuple back to itself: a rotation gives
`T^{4L} u = u` and a reflection gives `T^{2L} u = ρ^L u` and then
`T^{8L} u = ρ^{4L} u = u`. Being in a cycle is therefore the same as being a
periodic point, and the formalisation takes the periodic-point form.

Lemma 2 shows that a 4-tuple in a cycle has either all four entries in `Z_n^×`
or all four outside it; the cycles are called coprime and cocomposite
accordingly. Lemma 3 shows that a cycle containing a tuple with four equal
entries consists of such tuples, and such a cycle is called constant. Section 7
calls `[1 x 1 x^{-1}]` with `x ∈ Z_n^×` a generator 4-tuple when it lies in a
cycle, and calls a cycle containing a generator 4-tuple a generator cycle. The
product of 4-tuples is taken entry by entry.

## The statement in question

Section 7 proves Theorem 13, "Every coprime cycle is a product of a constant
cycle and two generator cycles", and then states:

> Conjecture 1. Every cocomposite cycle is a product of a constant cycle and two
> generating cycles.

followed by:

> This conjecture has been verified for all moduli up to 161. One possible
> direction of proving this conjecture is to show that all cocomposite cycles are
> a product of a cocomposite constant cycle and a coprime cycle, but we have been
> unsuccessful on this front.

## Why the published proof does not carry over

The proof of Theorem 13 takes `A`, `B`, `C` to be the tuples two steps earlier in
the cycles of `[abcd abcd abcd abcd]`, `[1 a^{-1}c 1 ac^{-1}]` and
`[bd^{-1} 1 b^{-1}d 1]`, whose existence it draws from Theorem 6. The last two
tuples are written with inverses of the entries, so the construction is available
only when the entries are units, which is exactly what a cocomposite cycle lacks.

## Scope of the recorded answer

The recorded result proves the conjecture, in the stronger form that covers both
kinds of cycle at once, so it also reproves Theorem 13. Writing `Q` for the
product of the four entries of a tuple `u` on a cycle of length `L`, the entries
carry three identities visible in the source's own displays: `Q` squares at every
move, the third move has exponent vector `(1,3,3,1)` and so is divisible by `Q`,
and the fourth move has exponent vector `(2,4,6,4)` and so is a square. The last
one makes every entry a `2^k`-th power for every `k`, and one pigeonhole step on
the iterated squaring maps of the finite ring `Z_n` produces a single `t ≥ 1`
with `z^{2^t} = z` for all of them. The constant factor is `Q^{2^{L-2}}`, whose
square is `u_0 u_2 = u_1 u_3`, and the two units come from the orthogonal
idempotent `ε = Q^{2^t - 1}`. Neither the Chinese remainder theorem nor any
counting of group orders enters.

## Bounded prior-resolution evidence

Issue 9336 records the screen. The article PDF and the Zenodo record were opened.
A full-text arXiv search for the article's coined term "cocomposite" returns no
hits, and the recent arXiv work listed under "Ducci" treats the additive game on
`Z_m^n` rather than this multiplicative variant. INTEGERS is not indexed in
Crossref and the citation-index result pages were not reachable, so this is a
bounded negative finding and no worldwide priority claim is made.
