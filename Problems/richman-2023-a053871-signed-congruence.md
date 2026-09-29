---
slug: richman-2023-a053871-signed-congruence
bibkey: richman2023a053871
doi: null
url: https://oeis.org/A053871
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/DerangedMatchingCongruence.result
---

# Richman's congruence for the deranged-matching numbers

## Problem

OEIS A053871 is the sequence `a(n) = 2(n − 1)(a(n − 1) + a(n − 2))` with
`a(0) = 1`, `a(1) = 0`. Its FORMULA section states

> Conjecture: if m == n (mod q) for q odd, then (-1)^m*a(m) == (-1)^n*a(n)
> (mod q). - _Harry Richman_, Aug 29 2023

Issue #10354 fixes the reading: `a` is the sequence of the recurrence in the
entry's name, `q` is a positive odd integer, and the congruence is in the
integers. The statement settled is that for every odd `q` and all `m ≡ n
(mod q)`, `(−1)^m a(m) ≡ (−1)^n a(n) (mod q)`.

## Motivation

The entry reads `a(n)` as the number of deranged matchings of `2n` people and
as the `n`-th central moment `E[(X² − 1)^n]` of the chi-squared distribution
with one degree of freedom, `X` a standard normal variable; its links include
Costa, Dobrescu and Fox, *Chiral Abelian gauge theories with few fermions*
(arXiv:2001.11991). The frozen declaration
`D5/S3/Combinatorics/DerangedMatchingCongruence.result` shows that the signed
moments are periodic with period `q` modulo every odd `q`, which proves the
conjecture.

## Gap

Issue #10354 preregisters the statement and its literature check before any
formalization. The entry (revision 173, 2026-04-23) still lists the conjecture.
The derangement numbers A000166 satisfy an analogous congruence proved in
their entry from a first-order recurrence; A053871 has a second-order
recurrence with a coefficient depending on `n`, which that argument does not
cover. Johnston, *Deranged matchings: proofs and conjectures*
(arXiv:2209.11319), treats asymptotics in its abstract; its full text was not
read. A web search for congruences of deranged matchings found no proof. These
readings are `not-found-in-searched-scope`; they do not establish an exhaustive
worldwide literature search or priority.

## Route

1. `b(n) = (−1)^n a(n)` satisfies `b(n + 2) = 2(n + 1)(b(n) − b(n + 1))`,
   `b(0) = 1`, `b(1) = 0`.
2. Let `c(n) = Σ_k (−1)^k C(n, k) (2k − 1)!!` and
   `d(n) = Σ_k (−1)^k C(n, k) (2k + 1)!!`. Pascal's rule gives
   `c(n + 1) = c(n) − d(n)`, and `(2k + 1)!! = (2k + 1)(2k − 1)!!` with
   `k C(n + 1, k) = (n + 1) C(n, k − 1)` gives
   `d(n + 1) = c(n + 1) − 2(n + 1) d(n)`. Hence `c` satisfies the recurrence of
   `b` with the same initial values, and `b = c`.
3. For odd `q` and `k ≥ 1`,
   `2^k C(q, k) (2k − 1)!! = q(q − 1)⋯(q − k + 1) · C(2k, k)` is divisible by
   `q`, and `2` is invertible modulo `q`, so `b(q) = c(q) ≡ 1 = b(0)`.
4. `b(q + 1) = 2q(b(q − 1) − b(q)) ≡ 0 = b(1)`.
5. The coefficient `2(n + 1)` has period `q` modulo `q`, so by induction
   `b(n + q) ≡ b(n)` for every `n`, and `b(m) ≡ b(n)` whenever `m ≡ n`.

## Falsifier

An odd `q` and `n` with `b(n + q) ≢ b(n) (mod q)` would refute the statement;
steps 3–5 exclude it.

## Evidence

Exact integer computation reproduces the entry's data and confirms
`b(n + q) ≡ b(n) (mod q)` for all odd `q < 300` with `n + q < 900` (112500
cases) and for all pairs `m ≡ n (mod q)` with odd `q < 60` and `m, n < 400`.
Controls fail as expected: without the sign every odd `q` from 3 to 39 has a
counterexample, and so has every even `q` from 2 to 18.

The canonical source is
`D5/S3/Combinatorics/DerangedMatchingCongruence.lean`. Its public declarations
are `a`, `claim`, and `result`. The frozen module state has statement identity
`sha256:748b6648d9f5c5f183cce045fa49e0edc8597878aa79885f93746323a7e31043`.
The result declaration has statement identity
`sha256:10ebaebf3eb0fddc30c27972480b1f173b46ea99b11029be73c6c138597b392d`.
The Freeze event is
`sha256:19520b9cd195fcf3ab685f3864b8bc8116f55d27e30332843b9429885180740f`
and has no project-level frozen prerequisites. The proof uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

`theorem`; resolution `proved`, as read in #10354. The public theorem has
`proof_shape: content`: the alternating-sum form of `b`, the divisibility of
its terms at `n = q` and the periodicity induction are new propositions on the
live path of the proof and are not instances of pinned lemmas.
`admission_basis: open-problem-resolution` under preregistration issue #10354.
There is no atom and no digestion coverage edge. The result is a uniform
theorem for every odd `q`, so `utility: none` applies.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof; the full text of
arXiv:2209.11319 was not read.
