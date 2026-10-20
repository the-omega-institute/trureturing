---
slug: samadzadeh-mojdeh-nadimi-2024-paired-coalition-binary-tree
bibkey: samadzadeh2024pairedcoalition
doi: 10.1080/09728600.2024.2389070
url: https://arxiv.org/abs/2402.10842v4
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Domination/SamadzadehMojdehNadimiRefutation.result
---

# Conjecture 1 on paired coalition numbers of perfect binary trees is false

## Problem

Samadzadeh, Mojdeh and Nadimi, *Paired coalition in graphs*,
arXiv:2402.10842v4, Section 4.2, p. 12, Conjecture 1:

> If T(h) is a perfect binary tree with height h, then PC(T(h)) = 5 if h = 2; 3 if h is odd; 0 otherwise.

The domain is every positive natural height. The root has depth zero and
all leaves have depth $h$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Perfect binary tree of height $h$ | `PairedCoalitionBinaryTree.perfectBinaryTree h` | Heap labels $1,\ldots,2^{h+1}-1$, children $2r,2r+1$. |
| Dominating set whose induced subgraph contains a perfect matching | `IsPairedDominating` | Reused `SimpleGraph.IsDominating` and a matching subgraph with exactly the selected vertices. |
| Disjoint sets, neither paired dominating, with paired dominating union | `IsPairedCoalition` | All four requirements are conjuncts. |
| Vertex partition; each part has another coalition partner | `IsPCPartition` | Nonempty, pairwise disjoint, covering parts; distinct partners in the same finset. |
| Maximum partition order; zero if none exists | `pcNumber` | Natural supremum of attained orders; finite vertex sets bound all orders. |
| Every positive height | `claim` | $h:\mathbb N$ with $1\le h$. |
| Height two first, then odd heights, then otherwise | `claim` | Values $5,3,0$ in exactly that order. |
| Conjecture is false | `result` | Negation of the complete positive-height claim. |

All declaration names in this dossier belong to
`D5.S3.Combinatorics.Graph.Domination.SamadzadehMojdehNadimiRefutation.PairedCoalitionBinaryTree`
unless another owner is explicit. No additional hypothesis restricts the conjecture.

## Motivation

`D5/S3/Combinatorics/Graph/Domination/SamadzadehMojdehNadimiRefutation.result`
refutes the conjecture. Its private prerequisite `pc_lower` establishes
$5\le PC(T(5))$, whereas the odd-height clause asserts $PC(T(5))=3$.
The Library note is
[Paired coalition in graphs](../Library/GraphInvariants/samadzadeh2024pairedcoalition.md).

## Gap

The conjecture specifies an exact value. One valid partition with five parts
at height five contradicts that value without requiring an exact computation
of the maximum. A statement excluding partitions of order four cannot exclude
one of order five.

## Route

Use heap labels $1,\ldots,63$ and $R=\{1,8,9,10,11,12,13,14,15\}$.
Set $A=\bigcup_{r\in R}\{r,2r,2r+1\}$ and
$B_j=\{4r+j:r\in R\}$ for $j=0,1,2,3$.
The five parts have sizes $27,9,9,9,9$, so none admits a perfect matching.
They are nonempty, disjoint and cover the tree.

For $j=0,1$, match $r$ with $2r+1$ and $2r$ with $4r+j$ in each block.
For $j=2,3$, match $r$ with $2r$ and $2r+1$ with $4r+j$.
These are perfect matchings of each $A\cup B_j$, and every such union dominates.
Thus each $B_j$ has partner $A$, and $A$ has partner $B_0$.
The partition order five is attained, giving the supremum lower bound.

## Falsifier

The counterexample would fail if the five sets did not partition all vertices,
if a part were paired dominating, if a designated union lacked a perfect
matching or domination, or if the source used a different height convention.
The Lean proof checks the partition, matchings, parity and supremum argument
for the stated heap tree and source predicates.

## Evidence

The kernel-checked public conclusion is `result : ¬ claim`. Its live private
prerequisites include `partition_pc`, `partition_card` and `pc_lower`.
The imported domination owner is
`D5/S3/ConceptDynamics/GraphColoring/GraphCoverDomination`, and the matching
notion is pinned Mathlib `SimpleGraph.Subgraph.IsMatching`.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Experiment

[Experiment directory at commit f4f5f6b6925228604ce8f8e805067a3fc7667a8c](https://github.com/the-omega-institute/trureturing-experiments/tree/f4f5f6b6925228604ce8f8e805067a3fc7667a8c/docs/reports/samadzadeh-mojdeh-nadimi-2024-paired-coalition-binary-tree).
Command: `python3 check.py`, in that directory; exit code 0; script SHA-256
`89ff4366726353f026f6c90a61c4d8993730ab2f20bd508bf8b2f2726fb22ec3`.
The computation validates the block partitions at exactly heights $2,5,8$,
with part sizes $(3,1,1,1,1)$, $(27,9,9,9,9)$ and $(219,73,73,73,73)$,
and the explicit height-five witness. It checks coverage, disjointness,
non-paired-domination of each part and a coalition partner for every part.
It establishes lower bounds at these heights, not exact coalition numbers.

## Triage

| Item | Status and evidence |
| --- | --- |
| Conjecture 1 is false | Proved in Lean: `result` negates the complete binding `claim`. |
| $PC(T(5))\ge5$ | Proved in Lean: private `pc_lower`, consumed by `result`. |
| $PC(T(5))=5$ | Open; the proof supplies a lower bound only. |
| Infinite family formally verified | Open; Lean certifies only height five. |
| $PC(T(h))\le5$ | Open; no upper bound of this form is established. |
| $PC(T(h))\ge5$ for every $h\ge5$ | Open; neither the Lean instance nor the finite experiment establishes it. |
| Heights $h\not\equiv2\pmod3$ | Open; no general conclusion for these heights. |
| Block construction at heights $2,5,8$ | Computed; experiment entry above, exit 0 and the pinned script hash. |
| No published settlement beyond the supplied inventory | Open; completeness is ASSUMED-UNVERIFIED. The bounded literature inventory below does not establish absence. |

### What the settlement shows

**Proved in Lean.** The height-five partition defeats the odd-height value
three. Odd part sizes prevent a perfect matching in each part, while the four
unions have explicit perfect matchings and dominate. `parts_odd`, `not_paired`,
`union_paired`, `partition_pc` and `pc_lower` are private prerequisites on the
proof path of the public `result`.

**Proved in prose.** For the block construction at heights $h=3t-1$, $t\ge1$,
take roots at depths $0,3,\ldots,3t-3$. Each vertex belongs to exactly one
seven-vertex block: root, two children and four grandchildren. There are
$\sum_{k=0}^{t-1}8^k$ blocks, an odd number. Consequently $A$ has three times
that many vertices and every $B_j$ has that many vertices; all five sizes are
odd. The two matching rules in Route cover each block of $A\cup B_j$ exactly,
and every excluded grandchild has its parent in $A$. Thus these unions
dominate, giving a five-part pc-partition for each such height. This is a
prose argument, not a Lean-verified infinite family. At $t=1$ the lower bound
agrees with the conjectured height-two value; $t\ge2$ contradicts the
conjectured odd or even value along these heights. Exact values and the
remaining height classes stay open.

**Computed.** The finite experiment validates the construction at heights
$2,5,8$ only. It independently validates the explicit height-five witness.

**Proved in prose from the Lean lower bound.** Lemma 4.10, p. 9, asserts
$PC(T(h))\le4$ for $h\ge3$, which is incompatible with $PC(T(5))\ge5$.
The final remark on p. 12 reduces the proposed proof to excluding value four
for $h\ge5$; that exclusion cannot settle the conjecture in the presence of
a five-part partition. The counterexample makes no assertion about the
paper's independent results on paths, cycles or other trees.

**Literature reading.** The inventory on preregistration
[#19217](https://github.com/the-omega-institute/trureturing/issues/19217)
contains arXiv:2402.10842v4, the publisher text, arXiv:2409.10185,
2502.07310 and 2509.15386 versions one and two, plus the Henning–Mojdeh
double-coalition papers. It reports no settlement of Conjecture 1 within
that inventory. Completeness is ASSUMED-UNVERIFIED.

## ASSUMED-UNVERIFIED

Completeness and currentness of the literature screen, absence of an unindexed
settlement and literature priority are not established by the Lean proof.
The exact value $PC(T(5))$, a Lean-verified infinite family and uniform
lower or upper bounds beyond the stated instance remain open.
