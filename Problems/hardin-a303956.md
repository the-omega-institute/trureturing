---
slug: hardin-a303956
bibkey: hardin2018a303956
doi: null
url: https://oeis.org/A303956
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/TraceAvoidingArrays/HardinA303956KingStrip.result
---

# Hardin's OEIS A303956 recurrence

## Problem

R. H. Hardin's NAME states:

> Number of n X 3 0..1 arrays with every element unequal to 0, 1, 2 or 5 king-move adjacent elements, with upper left element zero.

The FORMULA states:

> Empirical: a(n) = a(n-1) +2*a(n-2) +3*a(n-3) +2*a(n-4) -2*a(n-5) -6*a(n-6) -4*a(n-7) for n>8.

### Statement echo

For every positive natural height, the objects are all labelled functions
`Fin n × Fin 3 → Fin 2`. At every cell, count distinct other in-bounds
cells with row and column distances at most one and with a different bit.
The count must belong to $\{0,1,2,5\}$ and the upper-left bit is zero.
`Admissible` states these clauses literally; `a` is the integer cast of
the subtype cardinality, independently of the recurrence. There is no
self-neighbour, wrapping, padding, symmetry quotient or complement division.
`claim` retains every natural $n>8$, every coefficient and sign, natural
subtraction in the lag indices, and integer arithmetic on the counts.
The minimum argument is two. Height zero is outside the source range.

## Motivation

The source labels this seventh-order formula empirical. A303961 column 3
is the same claim, rather than an independent second problem. The target
is the original all-height assertion, rather than a finite prefix or an
unspecified higher-order recurrence.

## Gap

Tier 1: an older small empirical conjecture, published in 2018. Bounded
exact-ID searches found no existing settlement in the inspected sources.
No comprehensive semantic, journal or citation search establishes global
unresolved status or priority. The exact source and search scope are in
`Library/Certificates/hardin2018a303956.md` and issue
[#30923](https://github.com/the-omega-institute/trureturing/issues/30923).

## Route

A row has eight codes, column zero being the least significant bit.
An ordered pair of rows is a state. Initial acceptance checks the root
and top row. Appending a row checks the centre row and shifts the pair.
Terminal acceptance checks the bottom row with no additional row present.
The neighbour partition and inverse row coding apply at every height,
including the two-row case with no transitions. The existing weighted-word
transfer theorem then gives $a(k+2)=vT^kt$ for all natural $k$.

For $P(X)=4+6X+2X^2-2X^3-3X^4-2X^5-X^6+X^7$, let $r=vP(T)$.
The actual finite local predicate yields $rt=0$, $rTt=0$ and $rT^2=0$.
Thus $rT^mt=0$ for every natural $m$: the first two cases are scalar
identities, and all later cases factor through $rT^2$. Substituting
$m=n-9$ gives the printed formula with its exact signs and threshold.

## Falsifier

A mismatch between native neighbours and a boundary row check, a failure
of the inverse coding, an incorrect actual transition or endpoint, or a
nonzero residual pairing would invalidate this route. Finite-prefix
agreement alone cannot establish `claim`.

## Evidence

The formal source is
`D5/S3/Combinatorics/TraceAvoidingArrays/HardinA303956KingStrip.lean`.
Its designated full result is `result : claim`, proving the complete
original-domain recurrence. The finite transition and residual identities
are checked by the Lean kernel inside the proof. The axiom closure is
`propext`, `Classical.choice` and `Quot.sound`.

The pre-existing private experiment at local commit
`7887bf79c93eab02e575b043cc59d86139819a7d` has certificate SHA-256
`02a9cca9a1919e828557d3bd8e4d7854c5ab98a9fb1df1d6ccc97784e295f49b`.
Its pinned [experiment directory and rerun instructions](https://github.com/the-omega-institute/trureturing-experiments/tree/7887bf79c93eab02e575b043cc59d86139819a7d/a303956-threshold0-6af9e4a8)
are in the private `the-omega-institute/trureturing-experiments` repository,
locally `../trureturing-experiments/a303956-threshold0-6af9e4a8`.
At that revision, from the experiment directory with Python 3.12 or newer,
`python3 probe.py --output certificate.json` generates the certificate and
`python3 verify.py --certificate certificate.json --output verification.json`
checks it independently of the generator implementation.
Independent finite checks cover all 4096 transitions and 18724 rooted
boards of heights one through five. These are computed evidence, rather
than a substitute for the universal native correspondence or kernel proof.

## Triage

### What the settlement shows

- Proved (`D5/S3/Combinatorics/TraceAvoidingArrays/HardinA303956KingStrip.residual_invisible`): the decisive mechanism is annihilation of the boundary-conditioned
  degree-seven residual after two transitions, together with its first
  two zero terminal pairings.
- Proved (`D5/S3/Combinatorics/TraceAvoidingArrays/HardinA303956KingStrip.result`): the scope is exactly three binary columns with the allowed unequal
  neighbour counts and root specified above. Minimal order, threshold
  sharpness, other widths and changed allowed counts are open here.
- The pinned entry supplies a finite table and the empirical formula;
  no downstream theorem in that entry is identified as depending on
  this formula. A303961 column 3 duplicates it.

## ASSUMED-UNVERIFIED

Worldwide priority and exhaustive absence of a prior proof are unverified.
The bounded exact-ID arXiv and indexed global GitHub Lean queries returned
zero; outside-repository issues returned zero and repository issue search
found only #30923. Historical/FAQ follow-up requests returned HTTP 403;
the earlier readings are inherited evidence. Kernel verification concerns
the encoded assertion and does not certify the source's historical status.
