# Retained45/75 anchors leave the mixed pair-support obstruction

The fixed auxiliary support from [report492](492-mixed-split-common-pair-support-obstruction.md)
remains above the same source mass threshold for77 of the561 legal45/75
phase pairs. Thus restoring just these two actual shallow exclusions does
not uniformly repair the mixed split/common pair comparison. This is an
ordinary exact method test, not a covering counterexample or new Lean result.

## The same source and a more precise upper chart

Keep the worst completed source type(2,4,1), its mass lower bound

    m7=7235955529/450000000000,

and conditional caps(3/2,5/3,3/2,2,9/5) at7,11,13,17,19. The comparison
has first-root splits at3,5,7, common queried paths at11,13,17,19, and fixed
references(2,7,3,4). Every original full numerical label retains its single
global selector. The source and its attributed inputs remain those of
[report467](467-the-same-core-law-has-a-smaller-density-cap-and-tail-cutoff.md)
and the [Schroeder library entry](../../../../../Library/Arith/schroeder2026nine.md).

The six selected shallow classes are

    0 mod3,1 mod9,4 mod27,0 mod5,1 mod25,2 mod15.                (R1)

Write A6 for their literal complement modulo675. It has221 cells. Selected
source completion at45 and75 allows precisely

    F45={r mod45:r%3!=0,r%9!=1,r%5!=0,r%15!=2},
    F75={s mod75:s%3!=0,s%5!=0,s%25!=1,s%15!=2}.              (R2)

These are report483's legal phases. Each class must avoid the already
selected proper-divisor classes. The incomparable45 and75 classes may
intersect; their joint choice is not restricted to disjoint cylinders.
There are17 and33 choices, respectively. All561 pairs are considered, with
one fixed choice throughout each actual completed source construction.

For a pair(r,s), define

    A8(r,s)={n in A6:n!=r mod45 and n!=s mod75}.               (R3)

The actual completed source is supported in this smaller chart. Its
complete mass lower bound m7 is unchanged; only the upper comparison now
retains these two further exclusions. This uses the same coarse-source
uniform bound, not the lower mass of an independently optimized source.
The paired later-coordinate laws are unchanged. Let eta_(r,s) be their
product against Haar restricted to this actual joint initial chart; it is
an unnormalized comparison measure, not a normalized posterior.

## One fixed support across all charts

Let U be report492's12705 finite profiles together with every Q>=39
profile. Neither its indices nor its references are optimized separately
for the561 choices. Its upward property holds with3/5 factors fixed, and
all pairs have zero pair-relaxation bound. Those statements depend on the
profile inventories, not on the initial chart's weights.

For each n in A6 let

    w_n=eta(U intersect{initial CRT cell=n}).                 (R4)

The consumer reconstructs w_n using the conditional3/5 shell law within
that cell. Since U contains every Q>=39 profile, its complement consists
only of finitely many profiles Q<=38. Thus subtracting their exact
conditional probability from one pays all infinite valuation tails.
Every w_n is a nonnegative rational, and sum_n w_n equals report492's
full support mass. This is one joint675-cell chart, not a product of its
separately filtered ternary and quinary marginals.

The exact reweighting is

    eta_(r,s)(U)=sum_{n in A8(r,s)} w_n.                       (R5)

The consumer evaluates R5 by inclusion-exclusion of the two actual cylinder
sets, preserving their overlap. The retained JSON contains all221 cell
weights and every one of the561 exact fractions.

The results are:

| Property | Exact comparison count or display value |
| --- | ---: |
| Phase pairs with eta_(r,s)(U)>m7 | 77 |
| Phase pairs with equality | 0 |
| Phase pairs below m7 | 484 |
| Maximum, at(r,s)=(31,16) | 0.016268987778316816... |
| Maximum minus m7 | 0.00018908660276125956... |
| Minimum, at(r,s)=(38,53) | 0.010230236822233278... |

The maximum chart has210 retained CRT cells, and the minimum has200.
All comparisons use exact fractions; decimal values are only display.
In particular the maximum occurs at a single legal pair, rather than by
combining a favorable45 choice from one source with a75 choice from another.

The support restricted to any chart still satisfies the pair exclusions.
For each of the77 charts its mass is above m7, so the refined comparison,
monotonicity and all pair exclusions are still insufficient to force its
permitted mass below the actual-source lower bound. No original family is
asserted to realize this support. The other484 charts eliminate this one
candidate support; they do not give an upper bound on all permitted supports
or prove the corresponding original congruence families noncovering.

## Reproduction

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/mixed_split_pair_support_retained_anchors.py

This standard-library consumer checks the content identities of the support,
retained phase list and source mass/caps, reconstructs the exact cell weights,
and compares its output with the adjacent result JSON. It does not rerun
report492's full pair audit, a source producer or Lean. Its mathematical
input is report492's certified fixed support and the same completed source.
