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

The source definitions are mirrored literally by `activeNbrs`, `IsRomanDom`,
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
explicit independent witness with five labels $22$ gives equality for the
independent minimum.

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
The settling module state is
`Golden/Frozen/state/D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.lean.json`
with module statement identity
`sha256:41e90c47bfc335d2b9805f56ef01c1b689ec2a17c9c832724fd5b2d9113e49a2`.
Its public settling declaration is `result`; the designated refutation has
`utility: kind=certified-instance; basis=refutes=...` and is exempt from the
four-slot escape registration under CLAUDE.md §3.9. The axiom closure of the
public declarations is contained in `{propext, Classical.choice, Quot.sound}`.

The independent computation is pinned to
[the experiment directory at commit
89c3ef867b94d7635db748852158e92d39b54347](https://github.com/the-omega-institute/trureturing-experiments/tree/89c3ef867b94d7635db748852158e92d39b54347/docs/reports/luiz-vieira-2024-blanusa-independent-roman-closing-conjecture).
The file `check.py` exists at that commit (exit 0), has SHA-256
`1e7b2646261decf4b1a38cf8564f5424be93b79ec25e3cf3689ce0236a0be25d`, and
runs with exit 0 and `RESULT PASS`. Its tested scope is $t\in\{1,2\}$ and
$i=1,\ldots,6$ for cubic order, girth and uniform validity, with independent
minima searched for $i\le2$.

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
- **Proved — nearest surviving statements.** The source's independent-parameter
  bounds (Theorems 16 and 20) and statements restricted to $k=1$ are not
  refuted by this result.
- **Open — family and exact values.** The full generalized-Blanuša family
  statement for every $i$ is not formalized here, and the exact unrestricted
  $[21]$-Roman minimum on $B_1^1$ is not claimed beyond the proved upper bound
  $108$.
- **Open — equality range.** Classifying the values of $k$ for which equality
  holds across the generalized Blanuša family remains open.

## ASSUMED-UNVERIFIED

The literature search is incomplete beyond the sources and indexes recorded in
issue #19801. The settlement is the single instance $B_1^1$, $k=21$; it does
not claim a family theorem, worldwide novelty, or an exact unrestricted
minimum.
