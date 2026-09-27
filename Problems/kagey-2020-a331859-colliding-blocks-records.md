---
slug: kagey-2020-a331859-colliding-blocks-records
bibkey: kagey2020a331859
doi: null
url: https://oeis.org/A331859
triage: theorem
motivation_gids:
  - D5/S3/Constants/Billiards/CollidingBlocksRecords.result
---

# Colliding blocks: the collision count leaves floor(π√n) only at records

## Problem

OEIS A331859 (Peter Kagey, 2020) counts collisions in the colliding-blocks
system of the 3Blue1Brown videos:

> Suppose there is a block A of mass n sliding left toward a stationary block B
> of mass 1, to the left of which is a wall. Assuming the sliding is
> frictionless and the collisions are elastic, a(n) is the number of
> collisions between A and B plus the number of collisions between B and the
> wall.

Its FORMULA section gives `a(n) = ceiling(Pi/arctan(sqrt(1/n))) - 1`, and its
COMMENTS state

> Conjecture: The values of n for which a(n) != A121854(n) is a subset of
> A331903.

where A121854 is `floor(Pi*(sqrt(n)))` and A331903 is the positions of records
in A331859.

Issue #10098 fixes the readings: `a(n)` is the FORMULA closed form for
`n ≥ 1`, whose identification with the collision count is the published count
of Galperin (2003) and is not formalized here; A121854 is `⌊π√n⌋`; A331903 is
the set of `n ≥ 1` with `a(k) < a(n)` for all `1 ≤ k < n` (strict records, as
the entry's data `1, 2, 4, 5, 6, 8, …` shows).

## Motivation

For large `n` the collision count is close to `π√n`; the conjecture says that
it can exceed `⌊π√n⌋` only at the masses where the count reaches a new
maximum. The frozen declaration
`D5/S3/Constants/Billiards/CollidingBlocksRecords.result` proves this for
every `n ≥ 1`.

## Gap

Issue #10098 preregisters the conjecture and its literature check. The entry
(revision 27, 2025-09-18) still lists it as a conjecture; the OEIS entries that
cite A331859 (A331903, A331904, A011545, A332045) do not settle it; MathDB
returns no entry for "A331859"; the repository had no declaration or dossier
for it. These readings are `not-found-in-searched-scope`; they do not establish
an exhaustive worldwide literature search or priority.

## Route

Write `t(m) = arctan(√(1/m))`; `a(m)` is the largest integer strictly below
`π/t(m)`. Since `t` decreases, `a` is nondecreasing. Since `arctan y < y` for
`y > 0` (from `y < tan y`), `t(n) < 1/√n`, so `π/t(n) > π√n` and
`a(n) ≥ ⌊π√n⌋`. For `n ≥ 2`, `sin t(n − 1) = 1/√n` and `sin θ < θ`, so
`t(n − 1) > 1/√n` and `π/t(n − 1) < π√n`. If `a(n) ≠ ⌊π√n⌋`, then

```text
a(n) ≥ ⌊π√n⌋ + 1 > π√n > π/t(n − 1) > a(n − 1) ≥ a(k)   (1 ≤ k < n),
```

so `n` is a record position; for `n = 1` there is no `k` to compare.

## Falsifier

An `n` with `a(n) ≠ ⌊π√n⌋` and some `k < n` with `a(k) ≥ a(n)` would refute
the statement; the chain above excludes it. A proof that the closed form
differs from the physical collision count would change the reading, not the
theorem about the closed form.

## Evidence

The closed form reproduces the entry's 67 data terms, `⌊π√n⌋` reproduces the
62 data terms of A121854, and an exact rational simulation of the collisions
agrees with the closed form for `n = 1, …, 300`. The recomputed record
positions reproduce the 59 data terms of A331903. For `n ≤ 200000` there are
940 values of `n` with `a(n) ≠ ⌊π√n⌋` (2, 6, 8, 10, 12, 14, 17, 29, …), all
record positions; `π/t(n)` stays at least `9.9·10⁻⁷` away from an integer for
`4 ≤ n ≤ 200000`.

The canonical source is
`D5/S3/Constants/Billiards/CollidingBlocksRecords.lean`. Its public
declarations are `a`, `claim`, and `result`. The frozen module state has
statement identity
`sha256:49afcd1dd195dd328ad2c60019758ae38f302e2aad94627b639490fcfc567752`.
The result declaration has statement identity
`sha256:72bc1ed4177a7473467df6e4c8b80033ffbe6fc0dde69c46b06bcc986b09002b`.
The Freeze event is
`sha256:208de528663e0203226ee23ca5d3cfdca4a903ea538e325e90258097830e0522`
and has no project-level frozen prerequisites. The proof uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

`theorem`; resolution `proved` for the quoted conjecture. The public theorem
has `proof_shape: bind-only`: it instantiates pinned Mathlib facts about
`arctan`, `tan`, `sin` and the floor and ceiling functions and closes by
normalization. `admission_basis: open-problem-resolution` under
preregistration issue #10098; `escape_witness: null`. There is no atom and no
digestion coverage edge. The result is a uniform theorem for every `n`, so
`utility: none` applies.

## ASSUMED-UNVERIFIED

The identification of the closed form with the number of collisions is
Galperin's published count and the entry's reading; the collision dynamics is
not formalized, and Galperin's paper was not read here. The bounded
literature check does not establish exhaustive worldwide novelty, priority,
or the absence of an independent proof.
