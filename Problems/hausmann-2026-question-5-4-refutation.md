---
slug: hausmann-2026-question-5-4-refutation
bibkey: hausmann2026weightedmaxcut
doi: null
url: https://arxiv.org/html/2611.05178v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/ComponentPacking/HausmannQuestion54Refutation.result
---

# A counterexample to Hausmann Question 5.4

## Problem

Will Hausmann, *Weighted Max Cut in Subcubic Graphs*, arXiv:2611.05178v1,
[Question 5.4](https://arxiv.org/html/2611.05178v1#S5.Thmtheorem4), asks:

> Does every subcubic graph $G$ of odd girth exactly five admit a partition
> $V(G)=L\cup R$ such that $L$ is independent and every component of $G[R]$
> has order at most three?

The quotation uses the primary HTML's words and mathematical alttext, with
spacing normalized. Section 1 fixes finite simple graphs and defines
subcubic as degree at most three. The full affirmative assertion is:
for every finite vertex set $V$ and every simple undirected graph $G$ on $V$,
if every vertex has degree at most three, $G$ has a simple cycle of length
five, and every odd simple cycle of $G$ has length at least five, then there
exist $L,R\subseteq V$ such that

$$
L\cap R=\varnothing,\qquad L\cup R=V,\qquad
\forall x,y\in L\;(x\ne y\Rightarrow \neg(x\sim_G y)),\qquad
\forall C\in\operatorname{Comp}(G[R])\;|V(C)|\le 3.
$$

Here $G[R]$ is the actual induced graph, its components include singleton
components, and order means number of vertices. Even cycles are allowed.
The quantification has no vertex-count cutoff and imposes no connectedness,
planarity, regularity, sparsity, maximality of $L$, edge-weight, or special
construction hypothesis. Finite decidable presentations in the Lean claim
do not restrict this class.

The answer is **no**: the explicitly labelled generalized Petersen graph
$GP(7,2)$ below meets every input condition, and every independent $L$ leaves
a component of at least four vertices in its complement. The settling
statement is the negation of this entire universal assertion.

## Motivation

The source proposes a small-component independent-side partition as a
sufficient structural route to a weighted maximum-cut bound. An obstruction
to that partition distinguishes the structural proposal from the weighted
bound it was intended to establish. The counterexample excludes the whole
partition assertion on its stated class; it is not a failure of a particular
partition algorithm or a restricted positive search.

The source supplies the question and its relation to weighted Max Cut.
The explicit counterexample and residual obstruction are repository-derived
results, not results attributed to Hausmann's paper.

## Gap

Hausmann's Lemma 4.7 states that triangle-free subcubic graphs admit an
independent side with residual components of order at most six. It does not
supply order three. Theorem 2.2 assumes a component-union bipartiteness
structure and gives a weighted-cut inequality; it does not construct the
partition in Question 5.4. These are literature comparisons, not suppliers
on this Lean module's proof path.

The accepted bounded literature intake also identifies an order-three
forest-partition result under an additional maximum-average-degree bound
$18/7$ in Cranston–Yancey, arXiv:2006.11445v2. That extra hypothesis is absent
from Question 5.4. This comparison is attributed to the accepted intake;
it is not a fresh reading or a compiled dependency of this module.

The bounded Lean-library comparison found repository
`Brooks/Subcubic.brooks_cubic` and its private induced-colouring helper,
which supply three-colourability, and the
`ComponentPacking/AhanjidehEkimYildizZ` matching/extremal constructions.
Neither supplies the required partition or its refutation. The inspected
third-party `Vilin97/lean-pool` revision
`91c154506e3d08a1a25e4966c22c99212bf9df54` likewise supplies three-colourability.
The proof directly reuses Mathlib's three-clique/three-cycle equivalence,
cycle-length lower bound, adjacency-to-component membership, and
`Nat.card_le_card_of_injective`; these interfaces support the new finite
obstruction rather than already proving it. This is a bounded supplier
comparison, not an exhaustive ecosystem or novelty claim.

The missing target fact is settled negatively by the connected-four-vertex
obstruction for one legal graph. The inspected source and accepted bounded
prior conclusions establish no claim of global openness, novelty, priority,
or exhaustive third-party-library clearance.

## Route

### The labelled graph

For $i$ modulo seven, let $u_i=i$ and $v_i=7+i$. Use exactly the edges

$$
\{u_i,u_{i+1}\},\qquad \{u_i,v_i\},\qquad \{v_i,v_{i+2}\}
\quad (i\in\mathbb Z/7\mathbb Z).
$$

Equivalently, on vertices $0,\ldots,13$, the unordered edge set is

$$
\begin{aligned}
E=\{&\{0,1\},\{0,6\},\{0,7\},\{1,2\},\{1,8\},\{2,3\},\{2,9\},\\
&\{3,4\},\{3,10\},\{4,5\},\{4,11\},\{5,6\},\{5,12\},\{6,13\},\\
&\{7,9\},\{7,12\},\{8,10\},\{8,13\},\{9,11\},\{10,12\},\{11,13\}\}.
\end{aligned}
$$

The explicit edge set fixes the labels; no graph-encoding relabelling is
needed. There are fourteen vertices and twenty-one edges.

### Legal source input

Both layers are seven-cycles: adding two modulo seven traverses the entire
inner layer. The spokes form a matching between the layers. Each vertex
has two distinct layer neighbours and one spoke neighbour, so the graph is
simple and cubic, hence subcubic.

A triangle cannot lie in either seven-cycle. A triangle meeting both layers
would use two spokes, which is impossible because distinct spokes have no
common endpoint. Thus there is no triangle. The sequence
$0,1,2,9,7,0$ is a simple five-cycle. Simplicity and triangle-freeness exclude
shorter odd simple cycles, so the odd girth is exactly five. The private
Lean helper `legal` discharges the graph's actual degree and odd-girth
premises at the call to the universal claim.

### A connected residual set for every independent side

For every independent $L\subseteq\{0,\ldots,13\}$, the private theorem
`four_obstruction` supplies four distinct vertices $a,b,c,d\notin L$ with

$$
a\sim b,\qquad (a\sim c\ \lor\ b\sim c),\qquad
(a\sim d\ \lor\ b\sim d\ \lor\ c\sim d).
$$

Its exhaustive membership split uses independence to exclude neighbours
of vertices placed in $L$. Every completed branch supplies the four
outside vertices, their distinctness, and the displayed attachment edges.
The argument covers arbitrary independent sets, including empty and
nonmaximal sets; it has no cardinality restriction on $L$. The attachment
edges connect the four vertices. They need not form an entire component,
and no assertion that their induced graph is exactly a tree is needed.

If $L\cup R=V$, all four vertices belong to $R$. Their attachment edges lie
in $G[R]$ and put them in the same actual connected component. Distinctness
gives an injection from a four-element set into that component's vertex
support. Its order is therefore at least four, contradicting the required
bound three. This is the private theorem `residual_large`, which does not
need the disjointness assumption. The public `result` instantiates the
universal `claim` on this legal graph and applies that obstruction to the
asserted partition. A single legal negative instance refutes the universal
statement over all finite graphs.

## Falsifier

A defect in this refutation would require a failure of source correspondence,
a missing source input premise for the specified graph, an uncovered
independent set in the four-vertex obstruction, or an invalid passage from
the attachment edges to the order of an actual induced component. An
independent $L$ in this exact graph whose complementary components all have
order at most three would directly contradict the stated obstruction.
The accepted mathematical evidence settles these checks for this graph.
A different graph's successful partition would not refute this counterexample.

## Evidence

### Exact formal result and scope

The formal module
`D5/S3/Combinatorics/Graph/ComponentPacking/HausmannQuestion54Refutation.lean`
defines `claim : Prop` and proves
`D5/S3/Combinatorics/Graph/ComponentPacking/HausmannQuestion54Refutation.result : Not claim`.
Its canonical frozen membership and module identity are maintained in
[the owning state record](../Golden/Frozen/state/D5/S3/Combinatorics/Graph/ComponentPacking/HausmannQuestion54Refutation.lean.json).
The corresponding Blueprint gives the full claim and proof mechanism.
The proof is self-contained in Lean with Mathlib imports; the axiom
closure is contained in `{propext, Classical.choice, Quot.sound}`.
The finite evaluator's output is not an assumption of that proof.

The declaration-level classification is: `four_obstruction`,
`residual_large`, and `result` are content; `legal` is a consumed
bind-only helper whose consumer is `result`. Admission is by
`escape-witness`, with `four_obstruction` on the live component-injection
path. There are no frozen D5 suppliers. The unique designated public
`result` is exempt from four-slot Reg registration; the other authored
theorems are private, consumed helpers.

### Independent exhaustive computation

The completed independent evaluator reconstructed this same labelled graph
and examined all $2^{14}=16{,}384$ subsets. Exactly $435$ subsets were
independent, and zero gave a permissible complementary partition. For each
independent side, a connected residual set of at least four vertices was
checked; a separate union-find evaluation also rejected every complement.
These counts concern this single graph, not all graphs of a bounded order
or a minimal-counterexample search.

The accepted evaluator identifies the program as
`hausmann26496-independent-evaluation-1104m/verify.py` in the private
`the-omega-institute/trureturing-experiments` repository, with SHA-256
`cf57e9ab6361dd60489fef9ad2a4f407af94b812d10f0cec8e4a7485194def99`.
Its reported command, from the main repository root with CPython 3.13.12
selected on `PATH`, is

```sh
python3 ../trureturing-experiments/hausmann26496-independent-evaluation-1104m/verify.py
```

The evaluator reports exit code zero. These are attributed completed
evaluation results; no rerun is asserted here. The experiment's immutable
repository revision is ASSUMED-UNVERIFIED. The program hash identifies the
reported procedure, while the Lean obstruction supplies the deductive
refutation independently of its output.

## Triage

`theorem`; a full refutation of the affirmative assertion in Question 5.4.
Issue [26496](https://github.com/the-omega-institute/trureturing/issues/26496)
registers the exact finite-simple, subcubic, odd-girth-exactly-five target.
The accepted conservative research-line route and escape-witness admission
are retained; no automatic Tier 1/2 or open-problem-resolution admission
exception is asserted.

| Mathematical item | Result and evidence | Boundary |
| --- | --- | --- |
| Legality of the explicit $GP(7,2)$ | Proved in the frozen Lean module through the private consumed `legal` helper: degree at most three and odd girth exactly five. | A legal instance of the source class, without an added source hypothesis. |
| Uniform residual obstruction | Proved in the frozen Lean module by private `four_obstruction`, consumed by `residual_large`. | Every independent subset of this fixed labelled graph leaves four distinct connected residual vertices. |
| Failure of every required partition | Proved in the frozen Lean module by `residual_large` and public `result : Not claim`. | Full universal Question 5.4 is refuted; the existing result Describe binds this single theorem as Refuted. |
| Exhaustive finite counts | Computed in the accepted independent evaluation: 16,384 subsets, 435 independent sides, zero admissible partitions; program, hash and attributed execution are given in Evidence. | One fixed graph; no rerun asserted; immutable experiment revision ASSUMED-UNVERIFIED. |
| Surviving order-six result | Proved in the cited literature: Hausmann Lemma 4.7, attributed there to Berke–Szabó. | A source-paper result, not an additional theorem or proof dependency of this module. It gives six, not three. |
| Surviving weighted bounds | Proved in the source paper: Theorem 1.4 gives $15/19$ for triangle-free subcubic graphs; Theorem 1.5 gives $47/59$ at odd girth at least seven; Theorem 1.6 gives $4/5$ at odd girth at least nine, for nonnegative edge weights. | Literature results, not additional compiled conclusions here. Refuting the proposed partition does not refute these bounds. |
| Weighted $4/5$ conjecture on the wider triangle-free class | Open in this dossier; no proof or counterexample is supplied. | The refuted sufficient structural route does not decide the weighted inequality. |
| Question 5.3 | Open in this dossier; its exact source condition is bipartiteness of $G[V(C)\cup\{v\}]$ for every residual component $C$ and every $v\in L$, with $L$ independent in a triangle-free subcubic graph. | Its component-union condition is distinct from the order-three condition; no settlement is claimed. |
| Question 5.5 | Open; the exact external next candidate is separately registered as issue 26528. | Odd girth at least seven and residual component order at most five; no result is transferred from Question 5.4. |
| Size minimality, a classification of obstructions, and global novelty or priority | Unsettled here; novelty and priority are ASSUMED-UNVERIFIED. | The accepted result requires only this explicit counterexample. |

The exact next external source question is Hausmann Question 5.5:

> Does every subcubic graph $G$ of odd girth at least seven admit a partition
> $V(G)=L\cup R$ such that $L$ is independent and every component of $G[R]$
> has order at most five?

Thus it quantifies over every finite simple graph of maximum degree at most
three with no odd simple cycle of length less than seven, and asks for
disjoint exhaustive $L,R$, independent $L$, and at most five vertices in
every actual component of $G[R]$. The source's odd-girth-at-least classes
include bipartite graphs. This candidate belongs to
[26528](https://github.com/the-omega-institute/trureturing/issues/26528) and
remains unresolved under the supplied research premise. The present witness has a
five-cycle and supplies no counterexample to that different input class.

## ASSUMED-UNVERIFIED

The primary HTML at the exact frontmatter URL has SHA-256
`49bc3e301c8bea370cc9e9114b211a64ef529a70d268016c6e41d83254abe2d3`.
The supplied plaintext has SHA-256
`35663c84f57daddde3971e6957bb4da43eb8fdafe066016cf99a1166de52bda0`;
it is a transcription aid. Source correspondence uses Section 1,
Theorem 2.2, Lemma 4.7/Section 4.3, and Section 5 Questions 5.3–5.5.
Worldwide literature coverage, ownership clearance, novelty and priority
are ASSUMED-UNVERIFIED beyond these bounded readings and the attributed
library comparison. No such claim is needed for the explicit refutation.

The independent computation is attributed to the completed evaluator;
its immutable experiment-repository revision is ASSUMED-UNVERIFIED.
Its files remain in the private experiments repository. The Lean proof
does not depend on replaying that program. Minimality, classification of
all obstructions, the wider weighted conjecture, and Questions 5.3 and 5.5
are not settled by this result.
