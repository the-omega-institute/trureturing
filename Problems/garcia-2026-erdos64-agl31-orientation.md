---
slug: garcia-2026-erdos64-agl31-orientation
bibkey: garcia2026erdosgyarfas
doi: 10.48550/arXiv.2609.04686
url: https://arxiv.org/abs/2609.04686v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationThirtyOne.result
---

## Problem

Daniel Garcia, arXiv:2609.04686v1, §5, leaves the order-930 affine-group orientation instance open. The settlement refutes the solvability assertion preregistered in issue #14838.

Let $V=\operatorname{AGL}(1,31)=(\mathbb Z/31\mathbb Z)^\times\times\mathbb Z/31\mathbb Z$, with $(x,y)(z,w)=(xz,xw+y)$. For each $a\in\{11,17,22,24\}$, put $t=(-1,0)$, $g=(a,1)$ and $r=g^{-1}$. Let $B_a$ be the simple undirected Cayley graph joining $x$ to $xt,xg,xr$.

The claim is: some orientation of Garcia's p = 31 instance avoids 64-cycles. Precisely, there exist one of these four multipliers, a function $\sigma:V\to\{t,g,r\}$, and bijections $\tau_x:\{t,g,r\}\to\{u,v,w\}$ with $\tau_x(\sigma(x))=u$, such that the literal $H_{15}$ replacement has no simple cycle of length 64. The closed Lean theorem `result : ¬ claim` refutes this existence assertion. Every independent assignment of the remaining incident edges to $v,w$ is included.

## Motivation

The source states that a successful orientation would give the proposed order $15\cdot930=13\,950$ construction for $f(6)$. The refutation rules out that route for the four stated bases; it does not determine $f(6)$ or settle the unrestricted Erdős–Gyárfás conjecture.

The settlement declaration is `D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationThirtyOne.result`, with admission basis `open-problem-resolution`, resolution kind `Refuted`, and utility `certified-instance` through its verified `refutes` claim/result pair.

## Gap

The source leaves the orientation search open. Two classes of translated base cycles force enough visits involving port $u$, without enumerating orientations. The proof certifies the cycles, preserves their edge types under translation, counts translated visits, and expands one forced cycle in the literal replacement graph.

Literature check (2026-10-10, GPT Pro via nyxid and an orchestrator web search): arXiv lists only v1 of arXiv:2609.04686. Searches on the identifier, title, Daniel Garcia, AGL(1,31), 13,950 and orientation found no settlement. The citing paper arXiv:2609.28594 does not address this instance. The google-deepmind/formal-conjectures file `ErdosProblems/64.lean` states only the main conjecture, which remains open. Garcia’s Lemma 5.2 counting obstruction is the earlier single-family test; the two-cycle averaging here is the sharper common-orientation argument. These are the supplied literature-check results, not a new web search by this offline implementation seat.

The Lean theorem covers exactly $a\in\{11,17,22,24\}$ with $t=(-1,0)$ and $g=(a,1)$. The reduction of arbitrary girth-14 generating pairs to these normalized multipliers, and the finite girth classification, are computed and derived rather than formalized. The p = 37 case is not covered: the source states no bound for p = 37, and $a\in\{17,24\}$ have no fourteen-cycle with four occurrences of $t$.

## Route

The shared `ErdosGyarfasGarciaOrientationBase` module defines the parametric affine group, generators, Cayley base, literal $H_{15}$ gadget, ports, paths, replacement graph and generic certificate theorem. The p = 31 module supplies these word pairs, read by right multiplication from $(1,0)$:

| Multiplier | Four-$t$ word | Six-$t$ word |
| --- | --- | --- |
| 11 | `tgtrrtrrrtgggg` | `tgtgtgtgtrtrrr` |
| 17 | `tgtggggtrrrtrr` | `tgtgtgtgtrrrtr` |
| 22 | `tgtgtrrrrrtggg` | `tgtgtrtggtrrtr` |
| 24 | `tgtgtgggtrrrrr` | `tgtgtrtrrtggtr` |

Each word closes at the identity with fourteen distinct prefix products. The four-$t$ words have unused-type multiplicities $(6,4,4)$ and the six-$t$ words $(2,6,6)$. The averaging theorem forces a translate with at least ten distinguished-port visits. The explicit three-edge and five-edge gadget paths then expand ten and four visits respectively. The resulting simple cycle has length $14+10\cdot3+4\cdot5=64$.

## Falsifier

A witness to the solvability claim must give one of the four multipliers, a complete orientation $\sigma$, a compatible family $\tau$, and a demonstration that the literal replacement graph has no simple 64-cycle. The refutation constructs such a cycle for every proposed witness. A failed search or timeout supplies no witness.

The proof route would fail if a word did not close, repeated a prefix vertex, had different unused-type counts, or if a gadget path repeated a vertex or used a nonexistent edge. The private kernel-checked certificates discharge these obligations.

## Evidence

The final module list is:

- `D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationBase.lean`: the parametric affine group, generators, gadget, paths, replacement and generic certificate refutation.
- `D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationAveraging.lean`: the general translation-counting argument.
- `D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationExpansion.lean`: the general simple-cycle expansion from disjoint path blocks.
- `D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationThirtyOne.lean`: the p = 31 words, claim and result.

Each module has a matching Blueprint Scribe. The closed statement is literally `theorem result : ¬ claim`. No `sorry`, new axiom, `native_decide`, or debug declaration is used.

## Triage

[proved] The four normalized p = 31 instances are unsolvable: every orientation and compatible port assignment yields a simple 64-cycle. This refutes the proposed 13,950-vertex route through these bases, rather than supplying a bound on $f(6)$.

[derived] The common-orientation averaging argument combines the $(6,4,4)$ and $(2,6,6)$ unused-type histograms. If both cycle families had at most nine distinguished-port visits at every translate, the weighted total would be at most $27|V|$, while the histograms force $28|V|$.

[computed and derived; not formalized] Normalization and the girth classification restrict the relevant generating pairs to the listed multipliers; the formal refutation does not claim this classification. p = 37 is outside the route because the required four-$t$ fourteen-cycle certificates are absent for $a\in\{17,24\}$ and the source states no p = 37 bound.

[open] The unrestricted Erdős–Gyárfás conjecture and the value of $f(6)$ remain open.

## ASSUMED-UNVERIFIED

Forward-citation indices were not consulted by the supplied literature check.

The generating-pair normalization and accompanying finite girth classification are computed and derived, not Lean-formalized; completeness beyond the four explicit multipliers is not certified by `result`.
