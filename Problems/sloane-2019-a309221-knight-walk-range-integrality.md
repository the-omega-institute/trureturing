---
slug: sloane-2019-a309221-knight-walk-range-integrality
bibkey: sloane2019a309221
doi: null
url: https://oeis.org/A309221
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/RandomWalks/KnightWalkRangeIntegrality.result
---

# The normalized expected range of a knight's random walk is an integer

## Problem

OEIS A309221 (N. J. A. Sloane, 2019) normalizes the expected number of
distinct squares visited by a knight's random walk on an infinite chessboard,
A326954/A326955 (the starting square counted):

> a(0)=1; for n>0, a(n) = (A326954(n)/A326955(n))*2^(3*n-3). (It is only a
> conjecture that this is always an integer).

Issue #10116 fixes the readings: `E(n)` is the expected number of distinct
squares of `ℤ²` visited by a walk from the origin whose `n` steps are chosen
independently and uniformly among the eight knight moves, the start included;
equivalently `E(n) = S(n)/8^n` with `S(n)` the total over all `8^n` step
sequences; the conjecture asserts that `E(n)·2^(3n−3)` is an integer for every
`n ≥ 1`.

## Motivation

The number of distinct sites visited by a random walk, its range, is a basic
quantity of lattice random walks in statistical physics. For the knight's
walk the exact expectations are known only by computation, and their
denominators looked like powers of two with one factor fewer than `8^n`. The
frozen declaration
`D5/S3/StatisticalMechanics/RandomWalks/KnightWalkRangeIntegrality.result`
proves the integrality for every `n ≥ 1`: `S(n)` is divisible by `8`.

## Gap

Issue #10116 preregisters the conjecture and its literature check. The entry
has not been revised since 2019 and still calls the integrality a conjecture;
only A326954 and A326955 cite it; the linked Math StackExchange answer uses
four-fold rotational symmetry, which gives only `4 | S(n)`; the repository had
no declaration or dossier for it. These readings are
`not-found-in-searched-scope`; they do not establish an exhaustive worldwide
literature search or priority.

## Route

The eight symmetries of the square lattice act on the eight knight moves
simply transitively: for every move `m` there are a signed permutation `g` of
the coordinates and a permutation `s` of the moves with `g(move i) =
move(s(i))` and `s(0) = m`. Replacing every step `i` of a walk by `s(i)` maps
its positions by `g` and hence its set of visited squares by `g`; since `g` is
injective, the number of visited squares does not change. For `n = k + 1`,
this replacement maps the walks whose first step is move `0` bijectively onto
the walks whose first step is `m`. So each of the eight classes of walks by
first step has the same total `T`, `S(k+1) = 8T`, and

```text
E(k+1) · 2^(3k) = 8T / 8^(k+1) · 8^k = T.
```

## Falsifier

A walk whose number of visited squares changed under a lattice symmetry, or a
symmetry not permuting the moves, would break the argument; the eight
symmetries and their action on the moves are checked exhaustively in the
proof. A value `E(n)·2^(3n−3)` that is not an integer would contradict the
kernel-checked theorem.

## Evidence

Exact enumeration of all step sequences reproduces `A326954(n)/A326955(n)` and
`A309221(n)` for `n = 0, …, 7`; the totals `S(n) = 16, 184, 1920, 18840,
178560, 1647536, 14932736` for `n = 1, …, 7` are multiples of `8`, and
`S(n) = 8·S₁(n)` with `S₁(n)` the total over walks whose first step is
`(1, 2)`.

The canonical source is
`D5/S3/StatisticalMechanics/RandomWalks/KnightWalkRangeIntegrality.lean`. Its
public declarations are `move`, `position`, `visited`, `expectedRange`,
`claim`, and `result`. The frozen module state has statement identity
`sha256:3d963e8a0caac97cba619918e048698b6de50d5b29544c3066558ba2bd9e8d95`.
The result declaration has statement identity
`sha256:e7feb5cc600b5dafba5455ec0b4e7185f112d978ff2b9de83d7aad849e75efce`.
The Freeze event is
`sha256:43d8160c84fbb647f6f658ca67a2f7b810bb6fdd7c8b46dfcff9194ed2251568`
and has no project-level frozen prerequisites. The proof uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

`theorem`; resolution `proved` for the quoted conjecture. The public theorem
has `proof_shape: content`: its conclusion comes from the bijection between
the classes of walks by first step, built from the action of the lattice
symmetries on the moves. `admission_basis: open-problem-resolution` under
preregistration issue #10116. There is no atom and no digestion coverage
edge. The result is a uniform theorem for every `n`, so `utility: none`
applies.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof.
