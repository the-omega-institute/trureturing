---
slug: wqx-loopless-stability-refutation
bibkey: wangqinxia2025unexpectedautomorphisms
doi: 10.48550/arXiv.2509.26170
url: https://arxiv.org/abs/2509.26170v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Products/WangQinXiaLooplessStabilityRefutation.result
---

# A loopless refutation of Wang–Qin–Xia Conjecture 1.3

## Problem

Wang, Qin and Xia, *The existence of unexpected automorphisms in direct product
graphs*, arXiv:2509.26170v2, Conjecture 1.3, page 2:

> Let (Γ,Σ) be a nontrivial graph pair without loops, where Σ is bipartite.
> Then (Γ,Σ) is stable if and only if Γ is stable.

Nontrivial means connected, twin-free and coprime, with exactly one bipartite
factor. Coprimality allows all finite symmetric direct factors, including loops.
Stability of Γ means stability of its pair with the complete loopless graph K₂.
The source note is `Library/FiniteGroups/wangqinxia2025unexpectedautomorphisms.md`.
The preregistration and bounded literature screen are
[#24204](https://github.com/the-omega-institute/trureturing/issues/24204).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| All finite loopless undirected graphs Γ,Σ | `claim`: `V W : Type`, `Fintype` instances, `SimpleGraph` arguments | Full quantified domain; symmetry and no loops are in the graph type. |
| Coprime in the category permitting loops | `Coprime`, existing `RationalPositiveRealization.LoopGraph`, and `RelIso` | Common factor order is greater than one; both cofactors permit loops; `Fin` labels cover every finite carrier up to isomorphism. |
| Connected, twin-free, exactly one bipartite | `Nontrivial`, `SimpleGraph.Connected`, `TwinFree`, `SimpleGraph.IsBipartite` | Every conjunct is retained. |
| Σ bipartite | Separate hypothesis in `claim` | Retained even though the nontrivial predicate also distinguishes the bipartite side. |
| Pair stability iff Γ stability | `StablePair Gamma Sigma ↔ StableGraph Gamma` | Every product automorphism acts componentwise; `StableGraph` uses K₂. |
| Universal assertion is false | `result` has literal type `¬ claim` | The counterexample uses m=3. |

The product is the existing `DirectProductCyclePathBootstrap.dirProd`; the
auxiliary looped factors use the existing `LoopGraph`. The public predicates
retain the source conditions. No regularity or restriction on direct-prime
factors is added. The use of `Type` makes `claim` a closed, universe-free `Prop`.

## Motivation

The module
`D5/S3/Combinatorics/Graph/Products/WangQinXiaLooplessStabilityRefutation`
refutes the quantified claim. Its generality is G and its admission basis is
`escape-witness`. Its uniform family theorem is
`loopless_family_stable_nontrivially_unstable`, whose proof uses the
neighborhood-order classification and the independent-set bound. These are
private declarations in the settling module; the only public theorem is `result`.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

## Gap

The literature screen in #24204 distinguishes this loopless conjecture from
Wang–Gao, arXiv:2606.02203v1, Section 5 and Remark 5.5, whose comparison example
has loops. Their Theorem 1.3 retains the stronger hypothesis that every
direct-prime factor of the nonbipartite graph is loopless. The screen found no
settlement of the precise loopless conjecture in its inspected sources;
completeness is `ASSUMED-UNVERIFIED`.

## Route

Let R(a,b) mean a=true or b=true. For every $m\geq3$, the graph $\Gamma_m$
has vertices $(t,a,b)\in\operatorname{Fin}(m)\times\{0,1\}^2$ and adjacency
$$
(t,a,b)\sim(u,c,d)\quad\Longleftrightarrow\quad
 t\ne u\ \land\ R(a,d)\ \land\ R(c,b).
$$
Let $A_i=(i,0,0)$, $B_i=(i,0,1)$, $C_i=(i,1,0)$ and $D_i=(i,1,1)$.
The second graph has vertices $(s,i)\in\{0,1\}^2$ and adjacency
$s\ne r\land R(i,j)$; its path ordering is $(0,0),(1,1),(0,1),(1,0)$.

Neighborhood inclusion gives one diamond at each index. The private
`neighbor_subset_iff` and `diamond_action` classify its order symmetries;
`tf_diagonal` forces the two permutations of a two-fold automorphism to agree.
`gamma_stable` converts this into componentwise action on the double cover.
`independent_bound` bounds independent sets by $m+2<2m$. The private
`gamma_coprime` excludes common factors of order two using an independent
half-size slice and excludes order four by bipartiteness.

The product involution interchanges the bit coordinates by
$$
((t,a,b),(0,i))\longmapsto((t,a,i),(0,b)),\qquad
((t,a,b),(1,j))\longmapsto((t,j,b),(1,a)).
$$
Its adjacency preservation and failure to act componentwise are established by
`mix_adj` and `pair_unstable`. The family theorem supplies every hypothesis;
`result` specializes it at $m=3$.

## Falsifier

The refutation is the literal negation of the source claim, with every
nontriviality hypothesis supplied. A mismatch in the source category, omitted
looped common factors, or an invalid componentwise-action correspondence would
invalidate its interpretation as this conjecture. The statement echo retains
these conditions explicitly. Finite enumeration alone does not establish the
uniform family theorem.

## Evidence

The formal source and its Scribe mirror are
`D5/S3/Combinatorics/Graph/Products/WangQinXiaLooplessStabilityRefutation.lean`
and `Blueprint/D5/S3/Combinatorics/Graph/Products/WangQinXiaLooplessStabilityRefutation.scribe.cs`.
The designated settling declaration is `result`; the statement is `¬ claim`.

The independent exact experiment is in
[trureturing-experiments at b228129fea5136dc9fa2e77171803421d1e34df3](https://github.com/the-omega-institute/trureturing-experiments/tree/b228129fea5136dc9fa2e77171803421d1e34df3/docs/reports/wang-qin-xia-loopless-stability).
Command from an export of that revision:
`python3 docs/reports/wang-qin-xia-loopless-stability/check.py`, exit 0.
Script SHA-256: `01c18c04c2907a14d527da66b2955cba1b7398bdbbc145c1941783188ebdcefc`.
It computes independence numbers $5,6,7,8,9,10$ for $m=3,4,5,6,7,8$,
respectively, and enumerates all 12 two-fold automorphisms at $m=3$, all diagonal.
It checks the product mixer on all ordered vertex pairs for those six values.
Its family enumeration covers exactly $3\le m\le8$, with exhaustive
stability enumeration only at $m=3$. Its wording about an unproved universal
family describes the experiment's scope; the uniform theorem is supplied by
the Lean source.

## Triage

| Item | Status and evidence |
| --- | --- |
| Every $m\ge3$ gives a stable loopless graph with a nontrivially unstable $P_4$ pair | Proved in this module: private `loopless_family_stable_nontrivially_unstable`, with `gamma_connected`, `gamma_twin_free`, `gamma_coprime`, `gamma_stable`, and `pair_unstable`. |
| Universal binding claim is false at $m=3$ | Proved in this module: public `result`. |
| Every independent subset has at most $m+2$ vertices; no independent half-size slice | Proved in this module: private `independent_bound`; `gamma_coprime` uses $m+2<2m$ for $m\ge3$. This is an upper bound, not a kernel-checked equality for the independence number. |
| Exact independence numbers for $m=3,\ldots,8$; all 12 two-fold automorphisms diagonal at $m=3$ | Computed by the immutable experiment above, exit 0 and the stated SHA-256. |
| $m=1$ disconnected, bipartite, with twins; $m=2$ connected, bipartite, twin-free | Proved in prose below. The archived experiment checks $m=3,\ldots,8$ and supplies no computation of these two boundary cases. |
| Minimal counterexample order, other relations R, complete replacement classification | Open; neither the module nor the experiment settles these classifications. |
| Lean integration of WQX Theorem 1.4(a) and Wang–Gao Theorem 1.3 | Open; the read literature retains their stronger hypotheses. Neither theorem is on this module's dependency path. |

### Boundary cases

For $m=1$ the index inequality is always false. Thus the four-vertex graph is\nedgeless, disconnected, bipartite, and all four open neighborhoods coincide.
For $m=2$ the index is a proper two-coloring. The two D vertices are adjacent,
and every vertex has the D vertex of the other index as a neighbor, so the
graph is connected. At either index i, with j the other index, the four
neighborhoods are $\{D_j\}$, $\{B_j,D_j\}$, $\{C_j,D_j\}$ and
$\{A_j,B_j,C_j,D_j\}$. They are distinct; neighborhoods at different
indices are nonempty and supported on disjoint index classes. Hence there
are no twins. Neither case is nonbipartite. These are direct mathematical deductions, not new Lean declarations.

### What the settlement shows

The failure mechanism is that a looped direct factor can remain inside a
loopless product. In prose, define $\Delta$ on bit pairs by
$(a,b)\sim(c,d)$ iff $R(a,d)\land R(c,b)$. It has three loops, and the
identity on triples identifies $\Gamma_m$ with $K_m\times\Delta$ by the
adjacency formula above. This factorization is an explanatory deduction,
not a separate kernel-checked theorem. The private uniform family theorem proves stability and
nontrivial pair instability for every $m\ge3$. The independent-set bound
rules out the common one-loop two-vertex factor without imposing looplessness
on auxiliary factors. The mixer then produces an unexpected automorphism.

The read WQX Theorem 1.4(a) retains the implication from pair stability to
single-graph stability. Wang–Gao Theorem 1.3 retains its restriction on every
direct-prime factor. These are literature statements with their original
hypotheses, not additional kernel-checked results in this delivery. No
conclusion here removes hypotheses from the source's other results or settles
a replacement classification. Minimal order and broader R-families remain open.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The screen in #24204 did not
obtain the Gan–Liu–Xia full text or the cited handbook chapter; the OpenAlex
citing list was rate-limited and MathOverflow was inaccessible. These are
limits on the novelty screen, not assumptions used by the Lean proof.
The experiment is a finite check; it supplies no uniform classification beyond
its stated range. No worldwide priority claim is made.
