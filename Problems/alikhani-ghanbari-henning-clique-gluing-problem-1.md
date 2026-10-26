---
slug: alikhani-ghanbari-henning-clique-gluing-problem-1
bibkey: alikhanighanbarihenning2026strongdomination
doi: 10.2989/16073606.2025.2574046
url: https://www.tandfonline.com/doi/full/10.2989/16073606.2025.2574046
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Domination/AlikhaniGhanbariHenningCliqueGluing.result
---

# Strong domination under clique gluing

## Problem

Saeid Alikhani, Nima Ghanbari and Michael A. Henning, *Strong domination number
of graphs from primary subgraphs*, Quaestiones Mathematicae 49(2), 195–211,
Problem 1, p. 202, asks whether, for every $r\ge2$,

$$\gamma_{st}(G)\ge\gamma_{st}(G_1)+\gamma_{st}(G_2)-1-\Sigma_{X,Y}.\tag{4}$$

The finite connected graphs $G_1,G_2$ have order at least $r+1$ and contain
enumerated $r$-cliques $A,B$. The graph $G$ identifies corresponding clique
vertices. Here $X_i=N_{G_1}(u_i)\setminus A$,
$Y_i=N_{G_2}(v_i)\setminus B$, and
$\Sigma_{X,Y}=\sum_i|X_i|+\sum_i|Y_i|$. A strong dominating set contains,
for every vertex outside it, an adjacent vertex of at least that vertex's degree.
The strong domination number is its minimum cardinality.

The settlement is **Proved** for Inequality (4), under exactly these hypotheses;
the preregistration is [#19327](https://github.com/the-omega-institute/trureturing/issues/19327).
The source's request for an optimum using finer parameters is outside this claim.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Every $r\ge2$ | `claim` quantifies over `r` with `2 ≤ r` | No upper cutoff. |
| Two finite simple connected graphs | `V1`, `V2`, their finite instances, `G1`, `G2`, and connectedness hypotheses | Finite vertex labels and decidable equality add representation, not restrictions on finite graphs. |
| Order at least $r+1$ | The two `Fintype.card` inequalities | Literal order hypotheses. |
| Enumerated $r$-cliques | Embeddings `A`, `B` from `Fin r`, with `IsClique` on their ranges | Zero-based labels correspond to source indices plus one. |
| Identify $u_i$ with $v_i$ | `embedRight`, `glue` on the sum/subtype vertex type | Edges are the union of the factor edge images; identified clique edges occur once. |
| Strong domination | `IsStrongDominatingSet`, `strongDominationNumber` | The degree comparison is literal; the natural infimum is attained. |
| External-neighbour sum | `X`, `sigmaXY` | Neighbours shared by several clique vertices contribute once for each such vertex. |
| Inequality (4) | `result : claim` | Subtraction is in integers; no additional assumptions. |

## Motivation

The journal's Theorem 3 proves the edge-gluing case $r=2$. The declaration
`D5/S3/Combinatorics/Graph/Domination/AlikhaniGhanbariHenningCliqueGluing.result`
establishes the stated inequality for every $r\ge2$. The cited
[Library note](../Library/GraphInvariants/alikhanighanbarihenning2026strongdomination.md)
records the journal locator and source definitions.

## Gap

Only clique vertices can gain degree when the factors are glued. A dominator
in the common clique can therefore lose its degree advantage in a factor.
Ordinary domination results do not supply this degree comparison.

## Route

The proof preserves exterior adjacencies and degrees. In each factor it chooses
a maximum-degree clique vertex, which strongly dominates the other clique
vertices. The private `restriction_bound` constructs a repaired strong dominating
set by adjoining that vertex and, when needed, the clique's external neighbours.
The public `result` applies this construction to both factors and counts the
resulting sets.

## Falsifier

A counterexample to (4) would be two finite connected factors of the stated
orders, paired clique embeddings, and a minimum strong dominating set in their
gluing whose cardinality violates the displayed integer inequality. The
kernel-checked `result` excludes such data in the stated formalization.

## Evidence

The settling module and its Blueprint Scribe give the universal statement and
proof. Its imports are the pinned Mathlib clique, connectedness, finite inverse,
and finite-sum modules; there are no imported D5 owners or frozen prerequisites.
The axiom closure of every public declaration is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The escape audit for the public theorem `result` is unfinished:
[#19524](https://github.com/the-omega-institute/trureturing/issues/19524).
No four-slot registration is supplied. The missing evidence is a faithful
varying-carrier source reconstruction, equivalence bridge, variation,
sensitivity and actual observational dependence for an enrolled readout.

### Finite experiment

The executable check is in
[trureturing-experiments at commit 1c65304ff77ef2db2de46c1e757948c07e50797f](https://github.com/the-omega-institute/trureturing-experiments/tree/1c65304ff77ef2db2de46c1e757948c07e50797f/docs/reports/alikhani-ghanbari-henning-2026-clique-gluing-strong-domination).
Its `check.py` has SHA-256
`851fc352c79e955aaf40f2afc6d0c0fbe0922bb32d4a208bb38b424e3ac0a4d7`.
The executed command was
`python3 /Users/auric/.sshx/10bc509544500b180b7fba51/attempt-1/experiment-check.py`,
using exactly those committed bytes, with exit 0 and `RESULT PASS`.

| Tested scope | Computed result |
| --- | --- |
| Connected factors of order $r+1$ through $5$, $r=2$ | 194481 pairs; zero violations and zero repair-construction failures. |
| Connected factors of order $r+1$ through $5$, $r=3$ | 14161 pairs; zero violations and zero repair-construction failures. |
| 1500 random pairs for each $r=2,3,4$, orders at most $r+6$, with clique matchings permuted | Zero violations; minimum slacks $1,2,2$, respectively. |
| Source tightness family, $t=2$, $r=2$ | Factor number $9$, glued number $13$, external sum $4$: equality. |
| Source tightness family, $t=2$, $r=3$ | Factor number $11$, glued number $17$, external sum $4$: equality. |
| Superseded v1 family $H_r$, $r=2,3,4$ | Glued numbers $5,7,9$ versus v1 lower bounds $7,9,11$; (4) holds with equality. |

These finite readings do not establish a uniform sharpness theorem or a uniform
refutation of the superseded family.

## Triage

- **Proved, kernel-checked:** journal Problem 1's Inequality (4) for all $r\ge2$,
  by the public `result` in the settling module. This includes the source's
  edge-gluing inequality at $r=2$.
- **Computed:** the exhaustive, random, finite-tightness and v1 checks have
  exactly the scopes and values in the experiment table, with exit 0 and
  `RESULT PASS`. They support no untested universal claim.
- **Open in this settlement:** general sharpness of the source family is not
  a Lean theorem in `claim`; optimum bounds using finer parameters remain outside
  the settlement. The journal gives a general sharpness example; this delivery
  does not certify that entire family's domination numbers.
- **Computed (artifact inventory):** the proof is the settling module, with its
  Scribe and Proved resolution claim, this dossier, and the linked unfinished
  escape audit. The freeze registration is the canonical module state record.
- **Literature reading:** the journal replaces arXiv:2306.01608v1's Question 1
  and Theorem 4 by the distinct Theorem 3 and Problem 1. The finite $H_r$ checks
  above contradict those v1 bounds at $r=2,3,4$; they do not refute journal (4).

### What the settlement shows

**Proof mechanism (explanation of the kernel-checked construction).** Let $D$
be minimum in the glued graph and $c=|D\cap A|$. If $c>0$, repair each exterior
restriction by a maximum-degree clique vertex and every external neighbour.
Their total size is at most $|D|-c+2+\Sigma_{X,Y}$, hence at most
$|D|+1+\Sigma_{X,Y}$. If $c=0$, both restrictions need only their extra clique
vertex; connectedness and the proper clique range give an external neighbour,
so $\Sigma_{X,Y}\ge1$ and the same bound follows. Taking the two minima yields
(4). The private construction is `restriction_bound`; the universal bound is
`result`. The explanatory identities here are not separate public theorems.

**Extent and sharpness.** The theorem covers every stated finite factor and
every clique size $r\ge2$, without a dimension or enumeration bound. The two
finite source-family instances are computed equalities. Relaxed connectedness
or order hypotheses, uniform family sharpness and finer-parameter optima are
open here. The journal's other proved results are unchanged; its conditional
assertion that (4) holds for all $r\ge2$ is discharged by `result`.

## ASSUMED-UNVERIFIED

Literature-screen completeness is **ASSUMED-UNVERIFIED**. The screen recorded
on #19327 includes the journal text, arXiv v1, later papers by the same authors,
Hattingh–Henning, the cited 2024 Mathematics paper, formal-conjectures and
repository searches, and citation-index readings. It is not proof that no
independent settlement exists. General source-family sharpness and all
finer-parameter classifications are outside the Lean claim.
