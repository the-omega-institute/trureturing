---
slug: merca-2011-lifted-residue-sum-prime-order
bibkey: merca2011sums
doi: null
url: https://cs.uwaterloo.ca/journals/JIS/VOL14/Merca/merca3.pdf
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/MercaLiftedResidueSumPrimeOrder.result
---

# Merca's lifted residue sum at prime order

## Problem

Merca defines the remainder operation on printed page 2:

> When m is integer and n is a positive integer the quotient of m divided by n is ⌊m/n⌋ and the value m mod n = m − n⌊m/n⌋ is the remainder (or residue) of the division.

The multiplicative-order convention appears on printed page 17:

> For every positive integer m and every integer a relatively prime to m, we denote by ord_m(a) the multiplicative order of a modulo m, i.e., the smallest positive integer n such that a^n ≡ 1 (mod m), namely ord_m(a) = min {n ∈ N∗ | a^n ≡ 1 (mod m)}

The observation leading to Conjecture 2 appears on printed page 23:

> Using Maple to determine the value of some sums as Σ_{i=1}^{ord_m(a)} ((2a^i + m) mod 2m), necessary to determine the arithmetic mean (31) for round function, we notice another interesting identity.

The conjecture is stated on the same printed page:

> Conjecture 2. Let a and m be relatively prime positive integers. If m is prime and ord_m(a) is even then Σ_{i=1}^{ord_m(a)} ((2a^i + m) mod 2m) = m · ord_m(a).

The printed display brackets the summand as `((2a^i + m) mod 2m)`: the
remainder is taken of the whole quantity `2a^i + m`. Formula (39) on the same
page encloses each residue summand as `(a^i mod m)` in the same typography.

With the printed bracketing, the proved statement is: for every positive natural
number `a` and every prime natural number `m` coprime to `a`, if the
multiplicative order of `a` modulo `m` is even, then

```text
Sum_{i=1}^{ord_m(a)} ((2*a^i + m) mod (2*m)) = m*ord_m(a).
```

## Motivation

Conjecture 2 asks for an exact identity over the full multiplicative-order
cycle. The theorem settles the printed prime-modulus, coprime, even-order
statement uniformly rather than for a bounded range of moduli.

## Gap

Issue #9204 records the preregistered first-tier open problem and its bounded
literature check. No arXiv version of the paper was found. Four MathDB queries
for the title, conjecture, multiplicative-order sum, and lifted-remainder shape
returned no entry. Semantic Scholar returned HTTP 429 and was not verified.
The sibling Conjecture 1 refutation is tracked separately by issue #9191 and
PR #9211; it does not settle Conjecture 2.

These checked surfaces do not establish exhaustive worldwide literature
coverage, publication priority, or the absence of an independent proof.

## Route

The paper's `ord_m(a)` is encoded as pinned Mathlib's
`orderOf (a : ZMod m)`, the multiplicative order of the residue class. This is
the least positive `n` with `a^n` congruent to one modulo `m`, with Mathlib's
zero convention when no such `n` exists; the prime, coprime hypotheses give a
positive finite order here.

Write the even order as `2s`. The half-order power satisfies `a^s = -1` in
`ZMod m`: its square is one, while minimality of the order rules out
`a^s = 1`. Hence the residues at indices `i` and `i+s` are complementary
modulo `m`. Their two lifted terms sum to `2m`. Partitioning the order cycle
into `s` such pairs gives `s*(2m) = m*(2s)`.

Under CLAUDE.md section 3.2 the proof is bind-only: the half-order fact is the
instantiation of pinned Mathlib's order lemmas (`pow_orderOf_eq_one`,
`pow_ne_one_of_lt_orderOf`, `mul_self_eq_one_iff`; equivalently
`IsPrimitiveRoot.eq_neg_one_of_two_right`), the complementary residues follow
from `ZMod.natCast_eq_natCast_iff'` and cast rewriting, the pair sum `2m` is a
case split closed by `omega`, and the total is `Finset.sum_range_add` with
`ring`. Admission is by open-problem-resolution: the settlement of the named
conjecture is the new content, not the proof steps.

## Falsifier

A positive natural `a` and prime natural `m` with `Nat.Coprime a m` and even
`orderOf (a : ZMod m)` for which the displayed lifted sum differs from
`m * orderOf (a : ZMod m)` would refute the theorem. A different bracketing of
the printed `mod` expression or a different definition of multiplicative
order is a different claim.

## Evidence

The source and printed-page locators are recorded in
`Library/Certificates/merca2011sums.md`. The frozen declaration is
`D5/S3/Arith/Congruence/MercaLiftedResidueSumPrimeOrder.result`, with statement
ID `sha256:21c2588641c2ad1a616233587eb924caa2e09e9d5867321ca3a2973e8d63b68e`.
Its freeze event is
`sha256:df3b7bf067841400cee9022af543325b230e58e1a5941d4403a558b7b9d9c386`.
The axiom closure is exactly `propext`, `Classical.choice`, and `Quot.sound`;
the freeze event has no prerequisite frozen project nodes.

The orchestrator enumerated every prime `m < 400` and every `2 <= a < m`
having even order: 9111 cases, with zero failures. The relation
`a^(ord/2) congruent to -1 (mod m)` held in all 9111 cases. Boundary examples
are `m=7, a=3`, whose lifted sum is 42, and `m=7, a=6`, whose lifted sum is 14.
These finite readings are fault-detection evidence; the Lean theorem supplies
the uniform proof.

## Triage

First tier: a conjecture printed in Merca, Journal of Integer Sequences 14
(2011), section 11.9.1, preregistered in issue #9204. Resolution: `proved`.

| Declaration | proof_shape | direct frozen dependencies | escape_witness | admission_basis |
| --- | --- | --- | --- | --- |
| `result` | bind-only | none | none | open-problem-resolution |

The public surface is exactly `liftedSum`, `claim`, and `result`. The module is
symbolic rather than bounded enumeration, checker infrastructure, numeric
reduction, or a certified finite instance, so `utility: none` applies.

## ASSUMED-UNVERIFIED

Semantic Scholar is `ASSUMED-UNVERIFIED` because the query returned HTTP 429.
The bounded literature checks do not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof. The Lean kernel does not
authenticate the external PDF, its pagination, or its publication history.
