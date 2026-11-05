---
slug: luiz-vieira-2024-blanusa-independent-roman-closing-conjecture
bibkey: luizvieira2025independentroman
doi: 10.7151/dmgt.2580
url: https://arxiv.org/abs/2406.11688v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.result
---

# The Luiz–Vieira generalized Blanuša closing conjecture is false

## Problem

A. G. Luiz and F. A. S. Vieira, *Independent [k]-Roman Domination on Graphs*,
arXiv:2406.11688v1, Discuss. Math. Graph Theory 45 (2025), 1249–1272,
Section 6, conjecture that “this property holds for all generalized Blanuša
snarks,” where the property is $\gamma_{[kR]}(G)=i_{[kR]}(G)$ for $k\ge 2$.
The Lean claim is the literal quantification over $t\in\{1,2\}$, $i\ge 1$,
and $k\ge 2$ in `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.claim`.

### Statement echo

The source active-neighbour filter appears literally in `IsRomanDom`; the other
source definitions are mirrored by
`IsIndepRomanDom`, `weight`, `gammaRoman`, `indepRoman`, the block and link
edge sets, the recursive `verts` and `edges`, and `snark`. The settling
declaration is `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.result : ¬ claim`; it instantiates $t=1$, $i=1$, $k=21$.

## Motivation

The conjecture asserts equality for every generalized Blanuša snark and every
$k\ge2$. A single kernel-checked instance with
$\gamma_{[21R]}(B_1^1)\le108<110=i_{[21R]}(B_1^1)$ refutes that universal
statement.

## Gap

The preregistration is GitHub issue #19801. The source and journal version were
checked in the issue; the search records no published settlement in its searched
scope. Literature completeness is `ASSUMED-UNVERIFIED`; the unread surveys and
unbounded citation coverage do not support a worldwide priority claim.

## Route

For $B_1^1$ there are 18 vertices and every vertex has three neighbours. The
constant function $6$ is a $[21]$-Roman dominating function of weight $108$.
For an independent function, every positive label is at least $21$, its support
dominates, and the degree-three support bound leaves five positive vertices in
the only case below six. The private-neighbour argument then raises every one
of those five labels to at least $22$, giving weight at least $110$. An
explicit independent witness assigns $22$ exactly to `Vert.blk 1`,
`Vert.blk 4`, `Vert.blk 9`, `Vert.lnk 1 4` and `Vert.lnk 1 6`, and $0$
elsewhere, giving equality for the independent minimum.

## Falsifier

The refutation would fail if the source conventions were not represented by the
module's literal definitions, if the finite graph did not have the stated
18-vertex cubic structure, or if either the uniform Roman witness or the
independent lower-bound argument failed. The kernel-checked declarations
address these conditions for $B_1^1$ and $k=21$. The family-level extension,
the exact unrestricted minimum, and the classification of all $k$ remain
outside this settlement.

## Evidence

The canonical Lean source is
`D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.lean`.
Its public settling declaration is `result`; the designated refutation has
`utility: kind=certified-instance; basis=refutes=...` and is exempt from the
four-slot escape registration under CLAUDE.md §3.9. The axiom closure of the
public declarations is contained in `{propext, Classical.choice, Quot.sound}`.

The independent computation is pinned to
[the experiment directory at commit
89c3ef867b94d7635db748852158e92d39b54347](https://github.com/the-omega-institute/trureturing-experiments/tree/89c3ef867b94d7635db748852158e92d39b54347/docs/reports/luiz-vieira-2024-blanusa-independent-roman-closing-conjecture).
The file `check.py` exists at that commit (exit 0), has SHA-256
`1e7b2646261decf4b1a38cf8564f5424be93b79ec25e3cf3689ce0236a0be25d`, and
runs as `python3 /tmp/op-lv2406/resume-4c06431c/check.py` with exit 0 and `RESULT PASS`.
Its tested scope is $t\in\{1,2\}$ and $i=1,\ldots,6$ for cubic order, girth
and uniform validity; non-three-edge-colourability and independent Roman
minima are checked for $i\le2$, and the ordinary and independent domination
numbers in Theorem 19 are checked for $i\le3$.



### Declaration classification

| declaration | proof_shape | escape_witness | direct consumer(s) |
| --- | --- | --- | --- |
| card18 | bind-only | none | uniform_weight, weight_lower |
| cubic18 | bind-only | none | uniform_roman, weight_lower |
| uniform_roman | bind-only | none | gamma_le |
| uniform_weight | bind-only | none | gamma_le |
| gamma_le | bind-only | none | result |
| active_neighbors_eq | bind-only | none | private_label_ge |
| positive_ge | content | positive_ge | weight_lower |
| support_dominates | content | support_dominates | support_card_bound, weight_lower |
| covered_card_le | bind-only | none | private_neighbor_of_cover_bound, support_card_bound |
| support_card_bound | content | support_dominates | weight_lower |
| private_neighbor_of_cover_bound | content | private_neighbor_of_cover_bound | weight_lower |
| private_label_ge | content | private_label_ge | weight_lower |
| weight_ge_support_mul | bind-only | none | weight_lower |
| weight_lower | content | private_neighbor_of_cover_bound | indep_eq |
| witness_irdf | bind-only | none | indep_eq |
| witness_weight | bind-only | none | indep_eq |
| indep_eq | content | private_neighbor_of_cover_bound | result |
| result | content | private_neighbor_of_cover_bound | none |

The table uses names relative to the settling module namespace. The content
classification is independent of the designated result's registration exemption.

## Triage

Tier 1 external named conjecture, preregistered in issue #19801. Resolution:
`refuted`. Admission basis:
`open-problem-resolution (#19801; Refuted)`.

### What the settlement shows

- **Proved — integral support cost.** `uniform_roman` and `uniform_weight`
  give the $108$ upper bound through `gamma_le`; `positive_ge`,
  `support_dominates`, `covered_card_le`, `support_card_bound`,
  `private_neighbor_of_cover_bound`, `private_label_ge`, and
  `weight_lower` give the independent lower bound $110$.
- **Proved — degree-three private-neighbour criterion.**
  `private_neighbor_of_cover_bound` uses only maximum degree at most $3$,
  domination, and $1+4(|S|-1)<|V|$; it does not assume independence or exact
  cubicity in that criterion.
- **Computed — supplied checker.** The pinned experiment returns `RESULT PASS`:
  uniform labels are valid for both families at $i\le6$, and exhaustive
  independent minima are $110$ and $210$ for $i\le2$. This computation does
  not prove the family statement in Lean.
- **Source results — outside the settlement.** Theorems 16 and 20 are the
  source's independent-parameter bounds; the source also cites the $k=1$
  equality results. These are cited source results, not theorems proved by
  this delivery. The refutation concerns $B_1^1$ at $k=21$.
- **Open — family and exact values.** The full generalized-Blanuša family
  statement for every $i$ and the full uniform formulation for arbitrary cubic
  graphs are not formalized here, and the exact unrestricted
  $[21]$-Roman minimum on $B_1^1$ is not claimed beyond the proved upper bound
  $108$.
- **Open — equality range.** Classifying the values of $k$ for which equality
  holds across the generalized Blanuša family remains open.

## ASSUMED-UNVERIFIED

The literature search is incomplete beyond the sources and indexes recorded in
issue #19801. The settlement is the single instance $B_1^1$, $k=21$; it does
not claim a family theorem, worldwide novelty, or an exact unrestricted
minimum.
