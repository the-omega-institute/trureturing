---
slug: chervov-2026-cayleypy4-conjecture-eleven-refutation
bibkey: chervov2026cayleypy4
doi: 10.48550/arXiv.2603.22195
url: https://arxiv.org/abs/2603.22195v1
triage: theorem
motivation_gids:
  - D5/S0/CayleyGrowth/ConsecutiveFourCycleDiameterRefutation.result
---

# CayleyPy-4 Conjecture 11: consecutive four-cycle diameter

## Problem

Chervov et al., *CayleyPy-4: AI-Holography. Towards analogs of holographic
string dualities for AI tasks*, arXiv:2603.22195v1, section 8.5, printed
page 57, states:

> Conjecture 11. Case k = 4 from n = 6:
>
> $n \equiv 0,1 \pmod{3}: D_4(n)=\frac{n(n-1)}{6}-1,$
>
> $n \equiv 2 \pmod{3}: D_4(n)=\frac{n(n-1)}{6}+\frac{2}{3}.$

Section 8.1 specifies the cycles `(i,i+1,i+2,i+3)`, for
`i = 0,...,n-4`, with no wrapping. Section 8.5 specifies Cayley graphs,
not Schreier coset graphs, and inverse-closed generators. The vertices are
all permutations of `{0,...,n-1}` and distance is inverse-closed word
distance. This dossier concerns the complete clause for every `n >= 6`.

## Motivation

A counterexample at one permitted rank negates this entire universal
clause. The first permitted rank is six, where its formula gives four.
The formal result is `Not claim`, rather than a standalone lower bound.

## Gap

Issue #11712 preregisters the exact target, graph and prospective falsifier.
The source is version 1, submitted 2026-03-23; the original PDF has SHA-256
`3dd686df0fde2af02dbb7936ba2d525a9b7f41edbd21243b4884c859484b76db`.
The arXiv version listing, the author's CayleyPy repository issues, and
the trureturing D5, Problems, Library, Blueprint and issue searches contain
no explicit prior settlement of this named clause in the checked scope.
The checked citing papers arXiv:2607.13219 and arXiv:2607.12026 supply no
such settlement. These are bounded `not-found-in-searched-scope` findings,
not a claim about all literature or priority. Semantic Scholar and arXiv
API HTTP 429 responses contribute no negative evidence.

Theorem 5 of the same source already states
`D_k(n) >= ceil((n(n-1)-2)/(2(k-1)))`. At `n=6, k=4` this is at least
five, sufficient to contradict the displayed four. That published
implication is prior mathematics; no originality of this bound or method
is asserted. Its accompanying parity/subgroup sentence reverses the
standard parity convention. The finite proof uses the explicit generators
on the full symmetric group and does not depend on that sentence.

## Route

Use native `Equiv.Perm (Fin n)` vertices. `cycle n i h` is
`List.formPerm` on the four distinct consecutive indices with `i+4 <= n`.
`generators n` contains these permutations and their inverses, and
`graph n` is `SimpleGraph.mulCayley (generators n)` with right edges.
Inverse closure handles both orientations of its undirected adjacency.

`formula n` casts `n` into the rationals before subtraction and division.
The closed definition `claim` states that, for every natural `n >= 6`,
there is a natural `d` with `(graph n).ediam = (d : ENat)` and
`(d : Rat) = formula n`. This includes finite diameter and avoids a
conversion that could send infinity to zero.

At rank six the exact generator list is `(0123)`, `(0123)^-1`, `(1234)`,
`(1234)^-1`, `(2345)`, `(2345)^-1`. Let `B_0=[identity]` and form
`B_(m+1)` by retaining `B_m` and appending every product of an element of
`B_m` with an element of this list. The permutation `(05)(14)(23)`,
which sends `j` to `5-j`, is not in `B_4`. A local induction proves that
every walk from the identity of length at most four ends in `B_4`.
The purported diameter four would bound its distance by four; finiteness
of that distance supplies an attained shortest walk and a contradiction.

## Falsifier

The proof would fail if a source generator were omitted, the graph used
wrapped or directed edges, reversal belonged to `B_4`, the walk induction
failed for reverse edges, or the exact source formula did not give four
at six. These obligations are checked by the single result's proof and
its native-permutation definitions.

## Evidence

The mathematical source is
`D5/S0/CayleyGrowth/ConsecutiveFourCycleDiameterRefutation.lean`.
Its only public theorem is `result : Not claim`; the other five public
declarations are the necessary definitions `cycle`, `generators`, `graph`,
`formula` and `claim`. The cumulative finite-product exclusion is checked
by `decide +kernel` inside the result. Generator identification, inverse
closure, walk soundness, finite-distance attainment and rational
specialization are on the same proof path. No numerical exact diameter,
all-rank connectivity assertion, new axiom, `sorry` or `native_decide`
is used.

## Triage

Tier 1 external numbered conjecture; resolution `refuted` for the complete
`k=4, n>=6` clause as printed. Admission basis is
`open-problem-resolution`; utility is `bounded-enumeration` with basis
`refutes`, closed `claim` and unique `result`.
The result has `proof_shape: content`: the active finite exclusion and
walk induction produce the universal negation, rather than merely binding
an existing Lean statement. This classification does not assert novelty
of the published lower bound, the enumeration method or the implication
from Theorem 5.

Proved: the exact six-generator cumulative ball excludes reversal through
four moves, contradicting the proposed diameter. The formula's correction
of minus one at the first rank is incompatible with this obstruction.
Published sufficient implication: Theorem 5 already gives the conflicting
lower bound. Numerical readings: no uncertified exact diameter is part of
this settlement. Unresolved: a corrected four-cycle formula, the other
`k` clauses, and the larger-rank formulas. Conjecture 12 starts its general
assertions at `n >= 2k`; the rank-six counterexample does not refute that
rank restriction for `k=4`. The older CayleyPy Growth Conjecture 14(1)
prints inconsistent generator indices; its intended graph is not settled
by silently replacing them. Subsequent claims using the printed
Conjecture 11 clause have a false premise on this exact graph; no separate
dependent theorem is refuted here.

## ASSUMED-UNVERIFIED

Exhaustive worldwide literature status, priority, the exact rank-six
diameter, and the neighboring or corrected universal formulas are not
established.
