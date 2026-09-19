---
slug: wu-pyramidal-complement-conjecture-one
bibkey: wu2025pyramidalcomplement
doi: 10.5281/zenodo.17535229
url: https://math.colgate.edu/~integers/z95/z95.pdf
triage: theorem
motivation_gids:
  - D5/S3/Arith/CounterSequences/LeadingCounter
---

# Wu's k-gonal-pyramidal complement formula

## Problem

Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
A95, printed page 12, Conjecture 1, states:

> For k >= 9, (6) holds for all n >= 1.

For positive `m`, let
`P_k(m)=m(m+1)(m(k-2)-(k-5))/6`, and let the complementary sequence enumerate
the positive integers outside `{P_k(m) | m>=1}` in increasing order. Equation
(6), on printed page 11, sets `h=floor((6n/(k-2))^(1/3))` and gives `n+h+1`
when `6n` is at least
`(k-2)h^3+3(k-1)h^2+(2k-1)h+6`; if that test fails, it gives `n+h-1` when
`6n` is at most `h(h-1)(h(k-2)+k+1)`, and gives `n+h` otherwise.

## Motivation

This is an exact enumeration theorem, not an asymptotic estimate: it connects
a geometrically defined integer sequence to the rank of every positive integer
in its complement. The frozen leading-counter result supplies a related
repository precedent for proving an exact `Nat.nth` statement by counting all
earlier occurrences rather than replacing an infinite sequence with a finite
sample.

## Gap

The source proves neighboring eventual formulas and the cases `3 <= k <= 8`,
but leaves the uniform `k >= 9`, `n >= 1` statement as Conjecture 1. The
bounded literature and code search recorded in the linked Library note found
no complete earlier resolution in the searched scope. OpenAlex and Semantic
Scholar citation graphs were unavailable because both returned HTTP 429, so
the gap assessment is not exhaustive.

## Route

Use the integral extension
`P_k(m)=(k-2) choose(m+1,3)+choose(m+1,2)`, with `P_k(0)=0` only for counting.
Its consecutive difference is positive. Let
`H=nthRoot(3,(6n)/(k-2))` and prove that `H` is exactly the printed real-floor
cube root. The two threshold polynomials are respectively
`6(P_k(H+1)-H)` and `6(P_k(H)-H)`.

In the upper, lower, and middle branches, place the candidate strictly between
`P_k(t)` and `P_k(t+1)` for `t=H+1`, `H-1`, and `H` respectively. The lower
branch forces `H>=2`; the small-root cases are therefore included rather than
discarded. Strict monotonicity makes the excluded positive values below the
candidate exactly `P_k(1),...,P_k(t)`. Subtracting these `t` values from the
`a-1` positive integers below the candidate gives count `n-1`, and
`Nat.nth_count` identifies the candidate as the required term.

## Falsifier

A counterexample consists of natural numbers `k,n` with `9<=k` and `1<=n`
for which the displayed branch value is either a pyramidal value or has a
positive-complement count below it different from `n-1`. Failure of the exact
real-floor to natural-root equality, either inclusive threshold identity, or
the `H=0` and `H=1` branch analysis also falsifies the proposed route.

## Evidence

The canonical Lean module defines the positive complement independently of
the formula and proves the exact type
`wu_conjecture_one (k n : Nat) (hk : 9 <= k) (hn : 1 <= n)`. Its conclusion
uses `Nat.nth (complement k) (n-1)`, the literal real-floor cube root, the
ordered inclusive thresholds, and the three actual branch codes. The proof
has no `sorry` and its axiom closure is
`[propext, Classical.choice, Quot.sound]`.

## Triage

`theorem`. The public theorem has `proof_shape: content`; its conclusion is
produced by a new root-equivalence, interval, and exact-rank argument rather
than by instantiating a prior result. The intended admission basis is
`open-problem-resolution`. The result is unbounded symbolic mathematics, so
its computational utility classification is `none`.

## ASSUMED-UNVERIFIED

The bounded search does not establish worldwide novelty, priority, or absence
of unpublished solutions. Source fidelity, proof-shape classification, and
the correspondence between the source's complementary sequence and the Lean
predicate remain semantic review obligations even though the Lean kernel
checks the stated theorem.
