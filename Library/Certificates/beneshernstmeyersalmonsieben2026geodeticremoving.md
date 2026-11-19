---
bibkey: beneshernstmeyersalmonsieben2026geodeticremoving
authors: Bret J. Benesh, Dana C. Ernst, Marie Meyer, Sarah K. Salmon, and Nándor Sieben
year: 2026
title: Impartial geodetic removing games on graphs
doi: 10.48550/arXiv.2606.05483
url: https://arxiv.org/abs/2606.05483v1
claim: Conjecture 5.5 states that the initial Grundy value of TERMINATE is zero on odd cycle graphs.
strata_touched:
  - D5/S0/Certificates/Games/OddCycleTER
license: citation-only
triage: anchor
---

## Source

Section 2.3 defines the initial nim-value by the minimum excluded value
of the options. Section 2.5 defines geodetic convexity by all shortest
paths and the hull as the smallest convex superset. Section 3 defines
TERMINATE. From a position with full hull of the unselected vertices, a
move selects any unselected vertex. The player whose selection first
leaves a proper hull wins.

Section 5.1 defines the cycle family for $n\ge4$. Conjecture 5.5 on
printed page 7 reads “For cycle graphs with odd $n$,
$\operatorname{nim}(\operatorname{TER}(C_n))=0$.” The sentence preceding it
reports computer verification through $n=21$. Section 6(1) asks for its
settlement. [Pinned paper](https://arxiv.org/pdf/2606.05483v1#page=7)

The source and literature screen are recorded in the preregistration.
The formal conclusion applies to every $C_{2m+1}$ with $m\ge2$.
[Preregistration](https://github.com/the-omega-institute/trureturing/issues/31523)
