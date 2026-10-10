---
slug: garcia-2026-erdos64-agl29-orientation
bibkey: garcia2026erdosgyarfas
doi: 10.48550/arXiv.2609.04686
url: https://arxiv.org/abs/2609.04686v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientation.result
---

## Problem

Daniel Garcia, arXiv:2609.04686v1, §§3 and 5, leaves the order-812 affine-group orientation instance undecided after several CPU-hours. The settlement refutes the solvability of this instance, using the universal obstruction preregistered in issue #14828.

Let $V=\operatorname{AGL}(1,29)=(\mathbb Z/29\mathbb Z)^\times\times\mathbb Z/29\mathbb Z$, with $(x,y)(z,w)=(xz,xw+y)$. For each $a\in\{3,8,10,11\}$, put $t=(-1,0)$, $g=(a,1)$ and $r=g^{-1}$. Let $B_a$ be the simple undirected Cayley graph joining $x$ to $xt,xg,xr$.

The claim is: some orientation of Garcia's p = 29 instance avoids 64-cycles. Precisely, there exist one of these four multipliers, a function $\sigma:V\to\{t,g,r\}$, and bijections $\tau_x:\{t,g,r\}\to\{u,v,w\}$ with $\tau_x(\sigma(x))=u$, such that the literal $H_{15}$ replacement has no simple cycle of length 64. The closed Lean theorem `result : ¬ claim` refutes this existence assertion. Every independent assignment of the remaining incident edges to $v,w$ is included.

## Motivation

The source defines $f(k)$ as the smallest order of a cubic graph having no cycle of length $2^m$ for any $m\le k$. A successful orientation would give the proposed order $15\cdot812=12180$ construction for $f(6)$. The refutation rules out that route for the four stated bases; it does not determine $f(6)$ or settle the unrestricted Erdős–Gyárfás conjecture.

The settlement declaration is `D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientation.result`, with admission basis `open-problem-resolution`, resolution kind `Refuted`, and utility `certified-instance` through its verified `refutes` claim/result pair.

## Gap

The source leaves the orientation search open. Two classes of translated base cycles force enough visits involving port $u$, without enumerating orientations. The proof certifies the cycles, preserves their edge types under translation, counts translated visits, and expands one forced cycle in the literal replacement graph.

Literature check (2026-10-10, GPT Pro via nyxid and an orchestrator web search): arXiv lists only v1 of arXiv:2609.04686. Searches on the identifier, the title, Daniel Garcia, AGL(1,29), 12180 and "orientation" found no settlement. The citing paper arXiv:2609.28594 does not address this instance. The google-deepmind/formal-conjectures file `ErdosProblems/64.lean` states only the main conjecture, which remains open. Garcia's Lemma 5.2 counting obstruction is passed by p = 29, as §5 states; the two-cycle averaging here is sharper. These are the supplied literature-check results, not a new web search by this offline implementation seat.

The Lean theorem covers exactly $a\in\{3,8,10,11\}$ with $t=(-1,0)$ and $g=(a,1)$. The reduction of any girth-14 generating pair of the stated involution/generator form to these four is computed and derived, not formalized. For an involution $(-1,b)$ and generator $(a,e)$, conjugation by $(c,d)$ gives $(-1,cb+2d)$ and $(a,ce+(1-a)d)$. Choose $d=-cb/2$. Then $e-(1-a)b/2$ is nonzero: otherwise both generators fix $b/2$ and cannot generate the affine group. Taking $c=(e-(1-a)b/2)^{-1}$ normalizes the pair to $(-1,0),(a,1)$. Its multiplicative image generates the units only when $a$ has order 28. The finite girth computation leaves precisely $3,8,10,11$ at girth 14; the other eight order-28 multipliers have girth 10 or 12. Neither this classification nor its normalization is part of the Lean theorem.

## Route

Number the vertices of $H_7$ as $u=0,v=1,w=2,a=3,b=4,c=5,d=6$. Its nine edges are $va,ab,bw,cv,wd,ac,cu,ud,db$. The graph $H_{15}$ consists of copies $A$ and $B$ of this edge list, with labels $0,\ldots,6$ and $7,\ldots,13$, and a vertex $z=14$. Add exactly $v_Av_B,w_Az,zw_B$, represented by $(1,8),(2,14),(14,9)$. Its attachment vertices are $u=z=14,v=u_B=7,w=u_A=0$.

The replacement graph has vertices $(x,j)\in V\times\{0,\ldots,14\}$. Each fixed-$x$ copy has exactly the internal $H_{15}$ edges above. For each base edge from $x$ to $xs$, add an external edge between the attachment $\tau_x(s)$ in the $x$ copy and the attachment $\tau_{xs}(s^{-1})$ in the $xs$ copy. Here $t^{-1}=t$, $g^{-1}=r$, and $r^{-1}=g$. This is the literal vertex-replacement rule; its definition does not select or encode cycles.

The following words, read by right multiplication starting from the identity, give the two 14-cycle certificates for each multiplier. The first word has four occurrences of $t$ and the second has six.

| Multiplier | Four-$t$ word | Six-$t$ word |
| --- | --- | --- |
| 3 | `tgtggggtrrrtrr` | `tgtgtgtgtrrrtr` |
| 8 | `tggtrrrtgggtrr` | `tgtgtrrtgtgtrr` |
| 10 | `tgtrrtrrrtgggg` | `tgtgtgtgtrtrrr` |
| 11 | `tggtrrtgggtrrr` | `tgtgtrrtgtgtrr` |

The required finite checks are closure at the identity and pairwise distinctness of the 14 prefix products. Left translation preserves the incident edge labels. At each cycle vertex let $e$ be the unused incident edge type. The visit uses port $u$ precisely when $\sigma(x)\ne e$. For a 14-cycle with $k$ occurrences of $t$, the unused types occur $14-2k,k,k$ times for $t,g,r$ respectively.

Write $N=812$ and $T=\#\{x:\sigma(x)=t\}$. Summing over all left translates of the two cycles gives $S_4=10N-2T$ and $S_6=8N+4T$, hence $2S_4+S_6=28N$. If every translate of both cycles had at most nine visits using $u$, then $S_4\le9N$ and $S_6\le9N$, so $28N\le27N$, contradicting $N>0$. Some translate therefore has at least ten such visits.

The gadget supplies three-edge paths $[14,9,13,7]$ and $[14,2,6,0]$ for $u$–$v$ and $u$–$w$. It supplies five-edge paths $[14,9,11,10,12,7]$, $[14,2,4,3,5,0]$, and $[7,12,8,1,5,0]$ for $u$–$v$, $u$–$w$, and $v$–$w$. Reverse the lists for reversed endpoint pairs. Choose exactly ten visits using $u$ for the three-edge alternative and the remaining four visits for the five-edge alternative. Disjoint gadget copies and the simple base cycle ensure simplicity after expansion. Its length is $14+10\cdot3+4\cdot5=64$.

## Falsifier

A witness to the solvability claim must give one of the four multipliers, an orientation $\sigma$, a complete compatible family $\tau$, and a demonstration that the literal replacement graph has no simple 64-cycle. The refutation constructs such a cycle for every proposed witness. A failed search or timeout supplies no witness.

The proof route would fail if a word did not close, repeated a prefix vertex, had different unused-type counts, or if a gadget path repeated a vertex or used a nonexistent edge. The private kernel-checked certificates discharge these obligations.

## Evidence

The final module list is:

- `D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationBase.lean`: the shared parametric affine group, generators, gadget, paths, replacement and generic certificate theorem.
- `D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientation.lean`: the p = 29 words and finite certificates, with `claim` and `result` public.
- `D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationAveraging.lean`: the general translation-counting argument, with no certified finite instance.
- `D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationExpansion.lean`: the general simple-cycle expansion from disjoint path blocks, with no certified finite instance.

Each module has a matching Blueprint Scribe. The closed statement is literally `theorem result : ¬ claim`. For each proposed solvability witness the proof constructs a `SimpleGraph.Walk` satisfying `Walk.IsCycle` and having length exactly 64, contradicting the witness's avoidance condition. Ordinary `decide` checks the finite words and paths without `native_decide`; orientations are handled by finite-sum reindexing. Repository-wrapper builds of all three final modules pass. The source excerpt, certificates and argument were supplied by the orchestrator; the literature-check results are stated in Gap.

## Triage

[proved] The four normalized p = 29 instances are unsolvable: every orientation and compatible port assignment yields a simple 64-cycle. This refutes the proposed 12180-vertex route through these bases, rather than supplying a bound on $f(6)$.

[derived] Lemma 5.2 supplies a single counting obstruction that p = 29 passes. It does not enforce the joint constraints from the two cycle families against the same orientation. Here the unused-type histograms $(6,4,4)$ and $(2,6,6)$ give complementary visit counts $(8,10,10)$ and $(12,8,8)$. Their weighted combination is $(28,28,28)$, independent of the chosen type. Hence $2S_4+S_6=28N$, whereas avoiding ten eligible visits in both families would force $2S_4+S_6\le27N$. This common-orientation contradiction is the sharper mechanism that Lemma 5.2 misses. It uses only nonempty finite bijective translation and the two histograms; any further instance satisfying those hypotheses would face the same obstruction.

[computed and derived; not formalized] Normalization and the girth classification restrict the girth-14 generating pairs to the four multipliers above; the other eight primitive multipliers have shorter cycles. The formal refutation does not depend on claiming this classification as a Lean result.

[proved] The p = 31 instance is settled by the corresponding ThirtyOne module; p = 37 is not covered because the source states no bound there and the required four-$t$ certificate is absent for the cited multipliers. The unrestricted Erdős–Gyárfás conjecture and the value of $f(6)$ remain open.

## ASSUMED-UNVERIFIED

Forward-citation indices were not consulted by the supplied literature check.

The generating-pair normalization and accompanying finite girth classification are computed and derived, not Lean-formalized; completeness beyond the four explicit multipliers is not certified by `result`.
