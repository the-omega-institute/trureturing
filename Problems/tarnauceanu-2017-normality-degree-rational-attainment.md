---
slug: tarnauceanu-2017-normality-degree-rational-attainment
bibkey: tarnauceanu2017normalitydegree
doi: 10.37193/CJM.2017.01.12
url: https://www.math.uaic.ro/~martar/pdf/articole/articol%2040.pdf
triage: theorem
motivation_gids:
  - D5/S3/FiniteGroups/NormalityDegree/TarnauceanuRationalRealization.result
---

# Tărnăuceanu's rational normality-degree conjecture

## Problem

Marius Tărnăuceanu, *Normality degrees of finite groups*, §4,
Conjecture 4.1, printed p. 125. The preprint arXiv:1312.1427v1
states the same question as Conjecture 4.4, p. 16.

> For every x ∈ (0, 1] ∩ ℚ there exists a finite group G such that ndeg(G) = x.

| Source clause | Lean binding |
| --- | --- |
| Every rational $x$ | `∀ x : ℚ` |
| $x \in (0,1]$ | `0 < x → x ≤ 1` |
| Some actual finite group | `∃ (G : Type) (group : Group G) (finite : Finite G)` |
| Normal subgroups | `{H : Subgroup G // H.Normal}`, including bottom and top |
| Whole subgroup lattice | `latticeCount G = Nat.card (Subgroup G)` |
| Exact degree $x$ | `@ndeg G group finite = x` in `ℚ` |
| Closed upper endpoint | `Cyclic 2` realizes $x=1$ |

## Motivation

For a uniformly sampled subgroup of a finite group, the normality degree
is the probability that it is normal. Exact attainment asks for a single
finite group at each rational value. The source also studies limits along
sequences of finite groups.

## Gap

The source gives exact formulas for ZM groups and discusses a consecutive-fraction
route to rational attainment. Direct use of the formulas requires one action
and compatible parameters that realize both subgroup counts on the same group.

## Route

For $0<x<1$, write $x=u/v$ with $0<u<v$. Put $d=v-u$ and $t=2d$.
Choose a prime $p>2t$ congruent to one modulo $2^t$, and put $B=pu+d-1$.
An automorphism of order $2^t$ of $C_p$ defines the action of the generator
of $C_{2^B}$. In the resulting group $C_p\rtimes C_{2^B}$, inverse images
of quotient subgroups give $B+1$ normal subgroups. The levels at most
$B-t$ contribute one additional normal subgroup each. At each of the
remaining $t$ levels the prime kernel acts freely and transitively on the
$p$ sections, so none of those sections is normal. The two counts are
$2B-t+2=2pu$ and $2B-t+2+pt=2pv$. At $x=1$ all subgroups of $C_2$ are normal.

## Falsifier

A rational $0<x\le 1$ for which every finite group has a different normality
degree would refute the conjecture. An unaccounted subgroup, incorrect
normality decision, or incorrect exact count in the proposed family would
invalidate the corresponding step of the construction.

## Evidence

The source's definition, conjecture, and ZM formula are recorded in the
[primary bibliography note](../Library/FiniteGroups/tarnauceanu2017normalitydegree.md).
Equation (3.13) provides published formulas for both counts on the split
family. The Lean proof derives the counts by explicit classification.

- [Preregistered exact statement and literature screen](https://github.com/the-omega-institute/trureturing/issues/28774)
- [Public timed Lean probe terminal](https://github.com/the-omega-institute/trureturing/issues/28774#issuecomment-7070842749)

## Triage

The settling declaration `TarnauceanuRationalRealization.result` proves
`claim` over all positive rationals at most one, with no extra condition
on the group. The paired symbolic subgroup counts are used in the proof of
the exact rational equality. The group may depend on the rational. The
construction places no minimality requirement on its order.

For each integer $a \ge 1$, the rational $x=a/(a+1)$ lies in $(0,1)$,
so `result` gives a finite group of that normality degree. This is the
consecutive-fraction assertion printed as Corollary 4.5. Corollary 4.4
already proved that every real $x \in [0,1]$ is the limit of the
normality degrees of a sequence of finite groups.
[Journal §4, p. 125](https://www.math.uaic.ro/~martar/pdf/articole/articol%2040.pdf#page=11)

## ASSUMED-UNVERIFIED

The bounded literature qualification found no explicit published settlement
of the complete conjecture. Its scope includes the primary editions,
published ZM formulas, selected citing papers, and repository and Lean
library searches. Citation coverage beyond the recorded searches and
inaccessible full texts remain unverified. The result makes no priority
claim.
