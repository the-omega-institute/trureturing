---
slug: guo-han-binary-automatic-apwenian-level-generation
bibkey: guo2025apwenian
doi: 10.1016/j.disc.2025.114399
url: https://irma.math.unistra.fr/~guoniu/papers/p120autoapw.pdf
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Apwenian/GuoHanDefs.IsApwenian
---

# Binary automatic apwenian sequences have finite level generators

## Problem

Ying-Jun Guo and Guo-Niu Han, *On a family of automatic apwenian sequences*, Discrete Mathematics
348(5), 114399 (2025), Section 3, Conjecture 1, printed page 6 of the author manuscript:

> Let {u(n)}ₙ≥₀ be a 2-automatic apwenian sequence over {0,1}. Then there exist a finite alphabet
> Σ ⊂ N and a sequence σ over A(Σ) such that {u(n)}ₙ≥₀ = ϕ(σ) (mod 2).

The full domain consists of every binary sequence computed by a finite DFAO on canonical binary
expansions in most-significant-first order, with u(0) = 1 and
u(n) ≡ u(2n+1) + u(2n+2) modulo two for every nonnegative n. The alphabet Σ is a finite set of
natural numbers containing one. Every member of A(Σ) takes each letter of Σ to exactly two letters
of Σ whose sum is congruent to the original letter modulo two. Set X₀ = [1] and Xⱼ₊₁ = σⱼ(Xⱼ).
The generated sequence ϕ(σ) is the concatenation X₀X₁X₂⋯, and the conclusion is equality of its
parity with u at every nonnegative index.

## Motivation

`D5/S3/Combinatorics/Apwenian/GuoHanGeneration.result` constructs a single morphism whose constant
directive realizes the complete representation. It permits several odd letters and places no
fixed-point or prolongability requirement on the generated sequence. This is distinct from the
classification in Conjecture 2, whose domain consists of uniform-morphism fixed points on alphabets
with one odd letter.

## Gap

[Preregistration issue 13031](https://github.com/the-omega-institute/trureturing/issues/13031) records
the complete source statement and the bounded literature screen. The author bibliography, HAL
version metadata, Crossref, Semantic Scholar, arXiv apwenian screen and repository search supplied
no equivalent settlement in the inspected scopes. The author and institutional manuscripts agree
on the inspected clauses. The publisher version-of-record body and later unindexed bodies remain
outside the verified scope. This does not establish worldwide priority.

## Route

Adjoin a fresh zero-loop state z to the source DFAO. On one its transition enters the old machine
at the old start state's one-transition; on zero it stays at z. For every n and binary digit b,
a(2n+b) = δ_b(a(n)), including the exceptional zero case where a word-append identity would fail.
This machine argument does not use apwenianness. Either standard representation of zero is allowed.

Use precisely the finite set of occurring adjacent pairs sₙ = (a(n), a(n+1)). Its children
L(q,r) = (δ₁(q), δ₀(r)) and R(q,r) = (δ₀(r), δ₁(r)) equal s₂ₙ₊₁ and s₂ₙ₊₂ on each occurring pair.
Enumerate this set once with the root at index zero. The labels e(s) = 2i(s) + ε(s) are injective,
have the original output parity, and give root label one. Their image is Σ. The actual ordered
image τ(e(s)) = [e(L(s)), e(R(s))] stays in Σ, has length two and preserves letter parity as a sum.
The recurrence is applied only to occurring pairs.

The j-th whole level is exactly [e(s₂ʲ₋₁₊ₖ)] for 0 ≤ k < 2ʲ. The first j concatenated levels contain
exactly the first 2ʲ − 1 values of v, where v(n) = e(sₙ). The lengths 2ʲ − 1 are unbounded. The independent
exact-prefix definition of generation therefore gives an actual unique infinite sequence with
v(n) modulo two = u(n) for all n.

## Falsifier

The assertion would fail if some binary automatic apwenian sequence had no such finite-alphabet
directive. A construction must preserve all ordered levels and every coordinate, including zero;
word lengths, dyadic sums or selected-index parity alone do not satisfy the assertion.

## Evidence

The public theorem has only the source automaticity and apwenian hypotheses. Its conclusion gives
the finite alphabet, full letter-image conditions, the constant directive, exact unbounded prefixes,
alphabet membership, all-index parity and uniqueness. The source generation definitions are
independent of the sequence being represented.

## Triage

`theorem`; a complete universal representation result for the externally named Conjecture 1.
The mathematical construction uses finite-state recoding and ordered-word induction. It makes no
claim about central-bottleneck status, later citation impact or global priority.

## ASSUMED-UNVERIFIED

The publisher version-of-record body and any settlement outside the stated literature-search
scopes are unverified. The author and HAL manuscripts are the inspected source witnesses.
