---
slug: polettini-pinned-tree-span
bibkey: polettini2024coplanarity
doi: 10.1007/s11005-025-02026-8
url: https://arxiv.org/abs/2407.16093v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/PolettiniPinnedTreeSpanRefutation.result
---

# A pinned triangle refutes the spanning-tree dimension conjecture

## Problem

Polettini, Harunari, Dal Cengio and Lecomte, *Coplanarity of rooted
spanning-tree vectors*, arXiv:2407.16093v1, Introduction, conjecture:

> Finally, we conjecture that the 3ⁿ-vectors representing the deletion-constriction through n reversible edges span a n+1 dimensional space.

The source is recorded in the [Library note](../Library/StatisticalMechanics/polettini2024coplanarity.md).
The preregistration is [#19157](https://github.com/the-omega-institute/trureturing/issues/19157).
The universal assertion is refuted by unit-rate $K_4$ with the reversible
edges $(0,1),(1,2),(2,0)$ pinned.

### Statement echo

| Source clause or encoding | Lean counterpart | Fidelity and scope |
| --- | --- | --- |
| Irreducibility: a path of nonzero weight between any two vertices | `Irreducible` | Reflexive transitive closure of positive-rate arcs; all rates are nonnegative |
| A spanning tree directs every edge toward its root | `IsRootedTree` | The parent fixes the root; every non-root edge has positive rate; every vertex reaches the root |
| An arc belongs to the tree | `Contains` | Parent-map encoding excludes the auxiliary root loop |
| Deletion-constriction through $n$ reversible edges | `HasStatus` | Neither arc, forward only, or backward only, giving $3^n$ coordinates |
| Definition 1: sum of products over the conditioned trees | `tau` | The literal sum over parent maps with the selected statuses; products exclude the root |
| Deletion of all pins | `deletePins` | Both orientations of every pin receive rate zero |
| Dimension $n+1$ | `claim` | Real finrank of the span of the root-indexed vectors |
| Distinct reversible edges | Positive rates in both directions, distinct endpoints and injectivity through `Sym2.mk` | No parallel duplicate pins |
| Irreducibility after deletion | Last hypothesis of `claim` | A stronger admissibility condition, satisfied by the counterexample; it does not weaken the refutation |
| Universal parameters | Natural $N,n$, rates on `Fin N`, pins indexed by `Fin n` | Finite labelled graphs; aliases are expanded without changing the source convention |

The root loop encodes a fixed root and contributes no weight. An empty
product is one. The defining formulas and all parameters appear in the
Blueprint mirror; `result` displays the entire negated universal assertion.

## Motivation

The proposed dimension depends only on the number of pins. A triangle
introduces a cycle among three distinct reversible pins. The counterexample
refutes the proposed dimension even when deleting all pins leaves an
irreducible graph.

## Gap

The literature screen in #19157 covers arXiv:2407.16093v1 and the related
arXiv papers 2502.04298, 2412.05019, 2409.05827, 2602.20321, 2610.11970
and 2610.16894, Schweitzer's result through a restatement, MathDB, QIQC,
`google-deepmind/formal-conjectures`, and repository problem records.
No settlement was found in that searched scope. The journal full text
was not accessed; literature completeness is `ASSUMED-UNVERIFIED`.

## Route

For each of the four roots, the private catalogue contains all sixteen
rooted parent maps. `fourth_to_third` and `reaches_third` give the finite
reachability bound; `tree_iff`, `catalog_cases` and `tree_catalog_iff`
identify the catalogue with the original rooted-tree predicate.
`tau_eq_count` identifies the source's weighted sum with the filtered
catalogue count at unit rates. `count_relation` checks every one of the
twenty-seven statuses, and `tau_relation` transports that relation to real
vectors:

$$\tau_0+\tau_1+\tau_2=3\tau_3.$$

`tau_dependent` proves linear dependence; `span_finrank_le_three` bounds
the real dimension by three. `result` applies the universal conjecture
at $N=4,n=3$ and contradicts its required dimension four. The proof
imports only pinned Mathlib, with no D5 owner or frozen prerequisite.

## Falsifier

Incorrect status conditioning, incomplete tree enumeration, a violated
witness hypothesis or four independent root vectors would invalidate
the refutation. The kernel checks all statuses and catalogue completeness.
`rates_nonneg`, `rates_irreducible`, `pins_valid`, `pins_injective` and
`deleted_irreducible` verify every hypothesis, including connectivity of
the remaining bidirected star centred at vertex $3$.

## Evidence

The canonical module is
`D5/S3/StatisticalMechanics/PolettiniPinnedTreeSpanRefutation.lean`;
its only public theorem is `result`. All fifteen helper theorems are
private and consumed. Their proof shape and the result's proof shape
are `bind-only` under the normalization rule. The admission basis is
`open-problem-resolution (#19157; Refuted)` and the utility is a certified
instance refuting `claim`. No non-normalization escape witness is claimed.
There is no atom or coverage operation.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Experiment

[Pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/f7b148864def985e33d70c594831b800ba27c22e/docs/reports/polettini-harunari-dalcengio-lecomte-2024-pinned-cycle-rank).
The script is `check.py`, SHA-256
`104a55a023e87413b7aa73a9a40192a7ec445619a06f9bedd0e8f1e1444ea1cd`.
Command from that directory: `python3 check.py`; exit code $0$, result PASS.
The exact rational computation gives rank three and the stated relation
for unit-rate $K_4$; two positive random rational assignments for each
of $K_4,K_5,K_6$ with triangle pins also give rank three. Twelve sampled
forest pin sets of sizes two or three on $K_4$–$K_6$ give $n+1$ and
$1+\operatorname{rank}(B)$, and a sampled pinned four-cycle on $K_5$
gives dimension four instead of five. These finite checks do not establish
uniform statements over all rates or graph sizes.

## Triage

Tier 1 published conjecture; resolution Refuted. Literature completeness
is `ASSUMED-UNVERIFIED`. The canonical module, its Blueprint Scribe with
one Refuted resolution claim, Library note and dossier are the settlement
artifacts. Scoped admission and the frozen state record establish the
formal publication boundary; the external source and literature scope
remain as stated under Gap.

### What the settlement shows

| Item | Status and evidence |
| --- | --- |
| Finite reachability bound | Kernel-checked: `fourth_to_third`, `reaches_third` |
| Completeness of each root's catalogue | Kernel-checked: `tree_iff`, `catalog_cases`, `tree_catalog_iff` |
| Exact bridge from the source's $\tau$ to counts | Kernel-checked: `tau_eq_count` |
| All $27$ coordinate relations | Kernel-checked: `count_relation`, `tau_relation` |
| Every witness hypothesis | Kernel-checked: `rates_nonneg`, `rates_irreducible`, `pins_valid`, `pins_injective`, `deleted_irreducible` |
| Dimension contradiction | Kernel-checked: `tau_dependent`, `span_finrank_le_three`, `result`; the proved bound is at most three |
| Exact dimension three for the unit-rate witness | Computed by the pinned experiment; exact equality is not a Lean theorem here |
| Correct dimension $1+\operatorname{rank}(B)$ for general positive rates and an irreducible unpinned graph | Open: the incidence-rank mechanism proposed in #19157 is not proved by this module |
| Independence from positive rates; triangle pins on larger complete graphs, including $K_{28}$ | Open: no uniform theorem is proved, and $K_{28}$ is not tested |
| Triangle pins with sampled positive rates | Computed: rank three for exactly the six sampled assignments on $K_4,K_5,K_6$ named in the experiment entry |
| Source cases $n\leq2$ | Proved in prose: one or two distinct unordered edges cannot contain a cycle in a simple graph. The exhibited triangle has three edges, so this refutation does not contradict the source's results for one or two pins |
| Forest-pin and four-cycle checks | Computed: exactly the twelve sampled forest cases and the one four-cycle case named in the experiment entry |
| Uniform forest-pin and four-cycle formulas | Open: the finite computations do not prove uniform extensions |
| Further Lean goals required for this refutation | Kernel-checked: `result` proves the complete negated assertion |
| Proof-shape boundary | All sixteen theorems are `bind-only`, with consumed helpers and the external open-problem-resolution admission; no escape-content assertion |

For the unit-rate $K_4$ witness, the triangle pins yield dependence among
the root vectors. This single admissible witness refutes the
universal dimension formula. A forest-restricted dimension theorem,
the incidence-rank formula, and arbitrary-rate extensions are follow-up
questions rather than consequences established here. The source's
one-pin and two-pin theorems remain untouched; no other source theorem
is claimed to be invalidated.

## ASSUMED-UNVERIFIED

The literature screen is not exhaustive, and the journal full text is
not checked. The general incidence-rank formula, rate independence and
the $K_{28}$ case are not formalized or established by this delivery.
The real dimension upper bound and the refutation are kernel checked;
the exact rank equality and sampled extensions have computational
evidence only.
