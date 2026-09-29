---
slug: dalfo-fiol-reyes-three-quarter-conjecture-24
bibkey: dalfofiolreyes2026threequarters
doi: 10.61091/um128-09
url: https://arxiv.org/html/2609.33718v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture
  - D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture24Refutation
---

# Dalfó-Fiol-Reyes Conjecture 2.4

## Problem

Conjecture 2.4 of Dalfó, Fiol, and Reyes, *A note on three-quarters circulant
digraphs*, section 2, quantifies over every integer `k >= 1`. It specifies
`N=k^2+4k-2`, steps `a=1` and `b=-k-4`, and lattice columns `(k+2,1-k)` and
`(2,k)`. It says these data give a tile of a three-quarters digraph of sector
diameter `k`. The paper defines the sector distance using exactly the three
congruences `m*a+n*b`, `-m*a+n*b`, and `m*a-n*b` for `m,n >= 0`.

## Motivation

The conjecture proposes one lattice and two-step construction for all
`k >= 1`. The paper defines a digraph's arcs as a set of ordered pairs; its
`CD` construction uses the generating set `{a,b}` and calls the graph regular
of degree two in section 1 and property P1 of section 2. Under that convention,
the quantified graph assertion requires two distinct outgoing neighbors.

## Gap

At `k=1`, the specified data give `N=3`, `a=1`, and `b=-5=1` in `ZMod 3`.
The set `{z+a,z+b}` has cardinality one for every vertex `z`, contradicting
degree two. The sector construction at this boundary still has exact radius
one, and the two displayed lattice vectors still generate the congruence
kernel. The paper's separate `TQ(5,1,2)` example for `k=1` does not satisfy
Conjecture 2.4's specified `N,a,b`.

## Route

`ThreeQuarterCirculantConjecture` defines `SectorReach` with the source's three
sign sectors. Its construction results are `kernel_eq_generated`,
`sector_cover`, `sector_radius_lower`, and
`generator_regular_for_k_ge_two`. The latter also gives the cardinality-two
out-neighbor set for `k >= 2`.

For every `k >= 2`, the construction has the stated lattice kernel and
determinant, every residue is reached by radius `k`, residue `k` is absent at
radius `k-1`, and the two step residues are distinct and nonzero. Thus the
`k >= 2` corrected version has the intended degree-two generator condition;
the sector and lattice conclusions also hold at `k=1`.

## Falsifier

The `k=1` one-neighbor graph falsifies the original `k >= 1` degree-two
assertion under the paper's set-of-arcs convention. This refutation would not
apply to a reading that counts coincident generators as two parallel arcs;
that reading requires a different graph convention. The counterexample does
not falsify the sector-distance or lattice formulas.

## Evidence

`ThreeQuarterCirculantConjecture24Refutation.claim` states the quantified
lattice, sector, and degree conditions; its `result` proves `¬ claim` from the
`k=1` one-neighbor contradiction. The five named public theorems have scoped
Lean builds and accepted axiom-closure checks recorded in
[#11275](https://github.com/the-omega-institute/trureturing/issues/11275).
Freeze, successful Scribe emission, and required CI remain pending; the scoped
checks do not establish those integration states.

## Triage

This is an `open-problem-resolution` of the preregistered first-tier claim in
[#11225](https://github.com/the-omega-institute/trureturing/issues/11225).
The source-bound escape registration remains open in audit
[#11275](https://github.com/the-omega-institute/trureturing/issues/11275).
The graph conclusion depends on the source's set-of-arcs and degree-two
convention; the `k >= 2` construction satisfies that condition.

## ASSUMED-UNVERIFIED

The preregistration's arXiv exact-phrase, Crossref title, Google Formal
Conjectures code, and repository issue searches were bounded; OpenAlex was
unavailable because its unauthenticated quota was exhausted. They do not
establish exhaustive publication priority. No author clarification was
checked on whether the intended graph convention permits coincident steps
at `k=1`; the refutation is conditional on the paper's stated set-of-arcs
and degree-two reading, not on an unverified Lean calculation.
