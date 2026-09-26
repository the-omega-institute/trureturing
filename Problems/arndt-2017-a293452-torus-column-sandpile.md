---
slug: arndt-2017-a293452-torus-column-sandpile
bibkey: arndt2017a293452
doi: null
url: https://oeis.org/A293452
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/Sandpiles/TorusColumnToppling.result
---

# The toppling count of the n × 1 torus sandpile

## Problem

OEIS A293452 (Joerg Arndt, 2017) counts the iterations of the sandpile of
A249872 on the `n × k` torus:

> Let the lattice be c[i,j], 0 <= i,j < n. Fill each cell except c[0,0] with
> 4 grains of sand. Until all c[i,j] < 4, do the following: Find a c[i,j] >= 4.
> (According to Knuth, it does not matter which cell is chosen, the result
> will be the same.) Decrement the chosen cell by 4 and increment its 4
> neighbors by 1. c[0,0] is never increased, sand grains placed here are lost.

and its FORMULA section states

> Conjecture: T(n,1) = A023855(n).

with A023855 `a(n) = 1*(n) + 2*(n-1) + ... + (n+1-k)*k, k = floor((n+1)/2)`.

Issue #10122 fixes the readings. The printed identity is false at every `n`
(`T(1,1) = 0` but `A023855(1) = 1`; `T(2,1) = 1` but `A023855(2) = 2`): the
column `T(n,1) = 0, 1, 2, 7, 10, 22, 28, 50, 60, 95` of the entry is A023855
shifted by one place, so the statement settled is the corrected identity
`T(n,1) = A023855(n − 1)` for `n ≥ 2`. On the `n × 1` torus the four
neighbours of `(i, 0)` are `(i ± 1, 0)` and the cell itself twice. The number
of iterations is read, following Knuth's remark, as the length of every legal
toppling sequence that ends in a final state, and the existence of such a
sequence is part of the statement.

## Motivation

The abelian sandpile model is the standard example of self-organized
criticality. The frozen declaration
`D5/S3/StatisticalMechanics/Sandpiles/TorusColumnToppling.result` shows that on
the `n × 1` torus every order of topplings stops after exactly
`A023855(n − 1) = Σ_{1 ≤ j ≤ ⌊n/2⌋} j(n − j)` topplings, which proves the
entry's conjecture with its index corrected.

## Gap

Issue #10122 preregisters the corrected statement and its literature check.
The entry (revision 19, 2022-03-11) still lists the conjecture; the entries
citing A293452 (A249872, A389565) do not address the column `k = 1`; the
repository had no declaration or dossier for it. Least action and discrete
maximum principles are standard in sandpile theory; the exact toppling count
for this initial configuration on the `n × 1` torus was not found in the
searched scope. These readings are `not-found-in-searched-scope`; they do not
establish an exhaustive worldwide literature search or priority.

## Route

Let `v(i)` count the topplings of `(i, 0)`. A toppling of `(i, 0)` removes 4
grains and returns 2 through the two self-neighbours, so every cell other than
`c[0,0]` holds `4 − 2v(i) + v(i − 1) + v(i + 1)` grains, and `c[0,0]` is never
toppled. Put `u(x) = (x(n − x) + [n even]·min(x, n − x))/2` for
`0 ≤ x ≤ n`. Its final configuration is 3 at every cell other than `c[0,0]`
(`1 ≤ x < n`), except 2 at `x = n/2` when `n` is even.

1. Least action: along a legal sequence `v ≤ u`, since a cell with
   `v(x) = u(x)` holds at most 3 grains. Hence every legal sequence has at most
   `Σ u` topplings, and one of maximal length ends in a final state.
2. Maximum principle: if a legal sequence ends in a final state, `d = u − v` is
   nonnegative, vanishes at `0` and `n`, and has second difference at least `0`
   (at least `−1` at `n/2`); at the leftmost and the rightmost maximum of `d`
   these bounds fail unless `d = 0`.
3. So every such sequence has `Σ u = Σ_{1 ≤ j ≤ ⌊n/2⌋} j(n − j) = A023855(n − 1)`
   topplings.

## Falsifier

A legal sequence ending in a final state with a different length, or a
configuration from which no final state is reachable, would refute the
statement; the least action bound and the maximum principle exclude both.

## Evidence

A direct simulation of the rules reproduces A249872 for `n ≤ 7` and the first
eight rows (36 terms) of A293452. The printed identity fails at `n = 1, …, 5`;
the corrected identity holds for the ten data terms of the column and, with
three random toppling orders each, for every `n ≤ 80`.

The canonical source is
`D5/S3/StatisticalMechanics/Sandpiles/TorusColumnToppling.lean`. Its public
declarations are `Cell`, `initial`, `neighbours`, `topple`, `run`, `Legal`,
`Stable`, `a023855`, `claim`, and `result`. The frozen module state has
statement identity
`sha256:f8bc8ef7325339ac9556f0e637452c6bf66d4f80c1243ed549df07c562e1fdbb`.
The result declaration has statement identity
`sha256:44b8cfc897eff38513e891ee46f1ad72f371eb6f6cb514b31f1ba1787e62d5ab`.
The Freeze event is
`sha256:a2fc339bf3168f65922fdfed96b2e64417db2d8524ac687c767dd5fbee2ec451`
and has no project-level frozen prerequisites. The proof uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

`theorem`; resolution `proved` for the conjecture with its printed index
corrected, as fixed in #10122. The public theorem has `proof_shape: content`:
the least action inequality is proved by induction along toppling sequences,
the discrete maximum principle by comparing the leftmost and the rightmost
maximum of the defect `u − v`, and neither is an instance of pinned lemmas.
`admission_basis: open-problem-resolution` under preregistration issue #10122.
There is no atom and no digestion coverage edge. The result is a uniform
theorem for every `n`, so `utility: none` applies.

## ASSUMED-UNVERIFIED

The reading of "the number of iterations" as the common length of all legal
sequences ending in a final state follows the rule's own remark attributed to
Knuth; the formal statement proves this independence rather than assuming it.
The index correction is a reading of the printed formula; the printed
identity itself is false. The bounded literature check does not establish
exhaustive worldwide novelty, priority, or the absence of an independent
proof.
