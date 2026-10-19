---
slug: rather-2026-general-position-real-rooted-complete
bibkey: rather2026generalposition
doi: 10.48550/arXiv.2603.06930
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/GeneralPosition/RatherRealRootedComplete.result
url: https://arxiv.org/abs/2603.06930v3
---

# Rather's real-rootedness question for general position polynomials

## Problem

B. A. Rather, *Explicit Formulas and Unimodality Phenomena for General Position
Polynomials*, arXiv:2603.06930v3, Section 8 item 1, page 29, asks:

> For no nontrivial family is it currently known whether ψ(G) is always real-rooted. Even partial real-rootedness results for chordal graphs, bipartite graphs, or claw-free graphs (in analogy with [8, 13]) would be significant.

Section 1 says: “All graphs considered are finite, simple and undirected.”
Section 2, page 4, defines a general position set by the absence of three
distinct selected vertices $x,y,z$ with $d(x,z)=d(x,y)+d(y,z)$, and says:

> For each k ≥ 0, let α_k(G) denote the number of general position sets of size k.

> The general position polynomial of G is ψ(G) = ∑_{k≥0} α_k(G)x^k.

The settlement is **Proved**: for every nonempty finite connected simple
graph, $\psi(G)$ is real-rooted if and only if $G$ is complete.

### Statement echo

| Source clause or scope | Formal counterpart | Fidelity |
| --- | --- | --- |
| Finite, simple, undirected graphs | `V : Type`, `Fintype V`, `SimpleGraph V` | Exact finite simple-graph carrier. |
| Selected vertices avoid the distance equality | Frozen `CylinderSevenTen.IsGeneralPosition` and `OnGeodesic` | On connected graphs `SimpleGraph.dist` is shortest-path distance. |
| Number of general position sets of size $k$ | `alpha` | Cardinality of the complete finite-subset filter; each subset occurs once. |
| $\psi(G)=\sum_{k\geq0}\alpha_k(G)x^k$ | `psi` | Integer coefficients; the finite range ends at $|V|$, since larger subsets do not exist. |
| Real-rootedness | `IsRealRooted` | Every complex zero has imaginary part zero. |
| Classify connected graphs | `claim`, `result` | The nonempty connected scope is explicit; the conclusion is equivalence with `G = ⊤`. |
| Decidable equality | `DecidableEq V` | Finite-set infrastructure; it places no additional mathematical restriction on finite graphs. |

The four public definitions are the literal preregistered conventions.
`IsGeneralPosition` and `OnGeodesic` are reused from their frozen owner.
No statement about disconnected graphs under raw `SimpleGraph.dist` is part
of the formal classification.

## Motivation

The classification answers the real-rootedness question simultaneously for
all nonempty finite connected simple graphs. In particular, there is no
connected noncomplete exception among chordal, bipartite or claw-free graphs.
For the complete graph on $n$ vertices, the polynomial is $(1+X)^n$.

## Gap

The external question and the quantified connected classification are
preregistered in [#18870](https://github.com/the-omega-institute/trureturing/issues/18870).
The source still presents the question in version 3. The bounded literature
screen recorded there found no prior connected classification. Its
completeness is **ASSUMED-UNVERIFIED**; this is no claim of publication priority.

## Route

The settling module is
`D5/S3/Combinatorics/Graph/GeneralPosition/RatherRealRootedComplete`.
Its sole public theorem is `RatherGPRealRooted.result`; its other public
declarations are the four source definitions. Its 13 private theorem helpers
are used in the proof. The admission basis is
`open-problem-resolution (#18870; Proved)`; the proof shape of each theorem
is conservatively `bind-only`, with no independent escape witness claimed.

Every set of at most two vertices is in general position, giving the first
three coefficients $1,n,\binom n2$. Reflection at $n$ produces a monic
real-split polynomial with these two next-to-leading coefficients. If zero
were a root, deleting it would leave $n-1$ roots with the same first two
elementary symmetric functions. The frozen
`RealRootedCoefficientNewton.esymm_mul_esymm_le_sq_esymm` contradicts those
values. Thus the full vertex set is in general position. A connected
noncomplete graph has a distance-two triple on a shortest path, contradicting
general position of that full set. Conversely, all subsets of a complete
graph are in general position and $\psi(K_n)=(1+X)^n$.

## Falsifier

A nonempty finite connected noncomplete graph whose general position
polynomial has only real complex zeros would refute the classification.
Replacing shortest-path distance on connected graphs, counting a subset
more than once, or omitting any coefficient would fail source fidelity.

## Evidence

The kernel-checked public theorem is
`D5.S3.Combinatorics.Graph.GeneralPosition.RatherRealRootedComplete.RatherGPRealRooted.result`.
Its axiom closure is contained in
`{propext, Classical.choice, Quot.sound}`. The accompanying Scribe displays
the complete claim proposition and one `OpenProblemResolutionClaim` of kind
`Proved` on this settling node.

Escape registration is unfinished for `result`:
[#19014](https://github.com/the-omega-institute/trureturing/issues/19014).
There is no delivered Reg mirror or validated registration. A faithful
dependent-family realization, full quantified-statement reconstruction and
variation/sensitivity evidence remain missing; the fixed-state iff template
does not supply that evidence for the quantified finite-graph family.

### Experiment

[Published experiment](https://github.com/the-omega-institute/trureturing-experiments/tree/4f6a34b0aa01a7c3943f6edda0979ce8182f4b00/docs/reports/rather-2026-general-position-polynomial-real-rootedness).
Command in that directory: `python3 check.py 6`, exit 0.
`check.py` SHA-256:
`a9898800015c4c51dcc1972d3cbb07520d44aafd32bd5b8fc45c4544d24405a8`.
The experiment enumerates all 33,867 labelled graphs on one through six
vertices, including 27,476 connected graphs. It reports zero failures for
the connected classification, the componentwise-complete classification
under its finite-distance convention, the low coefficients, and full degree
when real-rooted. Roots are counted exactly. Its disconnected convention
requires all three distances in a tested equality to be finite, whereas raw
`SimpleGraph.dist` is zero between disconnected vertices. Consequently only
the connected readings test the formal classification's distance convention.

## Triage

### What the settlement shows

1. **Proved, kernel-checked.** `result` gives the exact classification for
   every nonempty finite connected simple graph under the binding
   conventions. The private helper `psi_top` proves
   $\psi(K_n)=(1+X)^n$. Substitution of the complete-graph conclusion in
   this identity gives the polynomial formula in the real-rooted case.
2. **Proved, kernel-checked.** The private helpers `alpha_of_small` and
   `degree_psi` give the coefficients $1,n,\binom n2$ and degree bound
   $\deg\psi\leq n$. `monic_coeff_zero_ne` and `full_of_real_rooted`
   prove that real-rootedness forces the full-size general position set.
   The connected source classes therefore have no noncomplete exceptions
   (`result`, specialized to each class).
3. **Proved boundary, in prose.** In the edgeless graph on three vertices,
   the raw distances between any two distinct vertices are all zero.
   Thus the three vertices satisfy $0=0+0$ and their full set fails general
   position. The experiment explicitly excludes an equality containing an
   infinite distance. Its disconnected classification is not a theorem
   about the raw-distance definition. On connected graphs every distance
   is finite and the definitions agree.
4. **Proved in prose under the source finite-distance convention.** A set
   is in general position in a disjoint union exactly when its intersection
   with every component is in general position: a finite geodesic stays
   within one component. Independent choices of subsets therefore multiply
   their generating polynomials. A product of nonzero real polynomials
   has only real complex zeros exactly when each factor does. Apply the
   connected classification to each nonempty component. This gives the
   componentwise-complete classification and $(1+X)^n$ under this convention.
   No disconnected extension under raw `SimpleGraph.dist` is asserted.
5. **Proved in prose.** The path $P_3$ belongs to the chordal, bipartite
   and claw-free classes. Its subsets of sizes zero, one and two are all
   in general position; its full three-vertex set is not. Hence
   $\psi(P_3)=1+3X+3X^2$, with roots
   $-\tfrac12\pm\tfrac{\sqrt3}{6}i$. None of those classes always has
   real-rooted polynomials. In their connected subfamilies, `result`
   identifies exactly the complete members.
6. **Computed.** The experiment entry checks all 33,867 labelled graphs
   on one through six vertices and reports zero failures in the four
   named tests. This finite computation is distinct from the universal
   kernel-checked connected classification and from the prose argument
   for the source's disconnected convention.
7. **Open.** Section 8 item 4, bounds on zeros, is not settled by `result`.
   No additional source theorem is claimed to follow from that item.

The source presents real-rootedness as a closing research question, rather
than a hypothesis of an earlier named theorem. The settlement adds the
classification; no correction of the source's earlier formulas or
unimodality results is established or required by this argument.

### Literature status

The preregistration records readings of Rather v1–v3 and Iršič, Klavžar,
Rus and Tuite, *General position polynomials*, Results Math. 79 (2024),
Art. 110, arXiv:2401.05696. Its bounded searches include OpenAlex citation
titles/abstracts, MathDB, `google-deepmind/formal-conjectures`, repository
Problems and preregistrations, the survey arXiv:2501.19385v5, and related
visibility-polynomial papers arXiv:2412.03066, 2507.01851, 2509.02509 and
2509.22571. Neither the recorded codex-cli search nor the recorded GPT Pro
literature reading found the classification in its searched scope.

## ASSUMED-UNVERIFIED

Literature-screen completeness and publication priority are unverified.
The disconnected prose classification uses the stated finite-distance
convention and has no Lean theorem in this delivery. Escape registration
remains unfinished as specified in #19014; it is separate from kernel
verification of the mathematical result.
