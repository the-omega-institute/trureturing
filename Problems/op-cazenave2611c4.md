---
slug: op-cazenave2611c4
bibkey: cazenave2026spectralgraphconjectures
doi: null
url: https://arxiv.org/abs/2611.03879v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SpectralGraph/CazenaveRandicSpectralBound.result
---

# Cazenave Conjecture 4: the adjacency–Randić–Laplacian bound

## Problem

Tristan Cazenave, *Lemmas and Conjectures in Spectral Graph Theory*,
arXiv:2611.03879v1, Section 7, p. 11, states:

> Conjecture 4 (#112951). $\lambda_1\le R+\mu_2$.

Section 1 restricts graphs to simple, undirected, connected graphs of order
at least two. The adjacency and ordinary Laplacian spectra are ordered
algebraically in decreasing order with multiplicity. In particular,
$\mu_2$ is the second largest eigenvalue of $D-A$, and
$R=\sum_{\{u,v\}\in E}(d_ud_v)^{-1/2}$ counts each unordered edge once.
Preregistration: [#26532](https://github.com/the-omega-institute/trureturing/issues/26532).

### Statement echo

| Source clause | Lean counterpart |
| --- | --- |
| Every order at least two | Natural parameter $n$ and carrier `Fin (n + 2)` in `claim` |
| Simple and undirected | `SimpleGraph` |
| Connected | `G.Connected` |
| Decreasing adjacency eigenvalues with multiplicity | `adjEig`, using Hermitian `eigenvalues₀` |
| Unordered-edge Randić sum | `randic`, using `G.edgeFinset` and `Sym2.lift` |
| Ordinary Laplacian, second largest eigenvalue | Reused `LinWangCaiBroomSpectralRatio.lapEig G 1` |
| $\lambda_1\le R+\mu_2$ | `result : claim` |
| Decidable adjacency | Instance data for the same finite graph; no graph is excluded |

No source clause is dropped. Square roots are nonnegative real square
roots. Every edge endpoint has positive degree, so no source summand uses
division by zero. The binding definitions are the preregistered expressions.

## Motivation

The settling declaration is
`D5.S3.Combinatorics.SpectralGraph.CazenaveRandicSpectralBound.result`.
Its admission basis is `open-problem-resolution (#26532; Proved)`;
`generality: I` follows its imported owner and `utility: none` records the
uniform mathematical estimates. The proof-shape classification is
`bind-only`; no independent escape witness is claimed. All five private
helpers are consumed by the settling proof or by another consumed helper.

## Gap

Equality classification and weighted-graph extensions are open in this
delivery. A separate target theorem for disconnected graphs and a Lean
formalization of the stronger classical bound $\mu_2\ge d_2$ for connected
graphs of order at least three are not delivered. The latter inequality is
literature-attested, not asserted to be an open conjecture.

## Route

Use the same graph throughout. Choose $u$ of maximum degree $\Delta$ and
$v\ne u$ of largest degree among the remaining vertices. Put
$r=\sqrt{\Delta}$ and $d=d_v$. Connectedness and order at least two imply
$\Delta\ge d\ge1$. The consumed private estimates give

$$\lambda_1\le r+d-1,\qquad r\le R,\qquad d-1\le\mu_2.$$

For the first estimate, the positive vector with value $r$ at $u$ and one
elsewhere satisfies $Ah\le(r+d-1)h$. An eigenvector coordinate maximizing
$|x_i|/h_i$ bounds every adjacency eigenvalue. For the second, charge edges
from neighbours of $u$: an edge receives total charge at most its Randić
weight, while each neighbour contributes at least $1/r$. For the third,
a nonzero vector supported on $u,v$ and orthogonal to the first Laplacian
eigenvector has Rayleigh quotient at least $d-1$; expansion in the ordered
orthonormal basis bounds it above by $\mu_2$. Composition yields the claim.

## Falsifier

A connected finite simple graph with the stated algebraic spectra and
$\lambda_1>R+\mu_2$ would contradict `result`. Changing to a normalized
Laplacian, ordering eigenvalues by absolute value or counting oriented
edges twice changes the statement.

## Evidence

Kernel evidence is the frozen settling declaration and its consumed
private helpers in `D5/S3/Combinatorics/SpectralGraph/CazenaveRandicSpectralBound.lean`.
The Scribe renders the full claim on `result` and carries one Proved
resolution claim for `op-cazenave2611c4`. The source note is
`Library/Eigenstructure/cazenave2026spectralgraphconjectures.md`.

The escape audit of the sole public theorem `result` is unfinished:
[#29101](https://github.com/the-omega-institute/trureturing/issues/29101).
A faithful dependent-family realization retaining graph order, decidable
adjacency and connectedness, and compiled bridge, variation, sensitivity
and actual observational-dependence evidence are not supplied. No Reg
registration or `declared_validated` status is claimed.

### Exact sharpness computation

Experiment source: [the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/dfa7d18bbe608edde3be2cd3f47465aeee255fd7/docs/reports/cazenave-2611-03879-conjecture-4-112951).
The referenced `check.py` exists at that immutable revision and has SHA-256
`3dcb2a458ccbdeee3de78f482d1d1866a1003b7b3c6e6347fafcebfdf1e43472`.
The command `python3 /Users/auric/.op-scratch/op/cazenave2611c4/stage-b/experiment-check.py`
exits 0. It executes the pinned script's exact fidelity checks: $K_2$
has adjacency spectrum $[1,-1]$, ordinary Laplacian spectrum $[2,0]$,
$R=1$, and slack zero; it also checks $R(K_n)=n/2$ for $2\le n\le9$.
These are computed values, not new Lean declarations. The same command checks the three sufficient certificates on all 273,192
connected unlabeled graphs of orders two through nine, with per-order
counts 1, 2, 6, 21, 112, 853, 11,117 and 261,080, and ends with
`ALL_CHECKS_OK`. The finite checks do not replace the unrestricted theorem.

## Triage

### What the settlement shows

| Item | Status and evidence |
| --- | --- |
| Mechanism | Proved; kernel-checked `result` composes `adjacency_degree_bound`, `randic_lower` and `lap_second_degree` for the same graph and the same selected vertices, giving $\lambda_1\le r+d-1\le R+\mu_2$. |
| Range | Proved; the telescope of kernel-checked `result` covers every connected simple graph on `Fin (n + 2)` for every natural $n$. It adds no graph-order cap, bipartite condition, normalized Laplacian or absolute-value ordering. |
| Sharpness example | Computed; the exact fidelity command and script hash in Evidence give $\lambda_1(K_2)=1$, $R(K_2)=1$ and $\mu_2(K_2)=0$. |
| Neighbours | Open in this delivery: equality classification, weighted-graph extension and Lean formalization of the literature-attested stronger $\mu_2\ge d_2$ bound for connected graphs of order at least three. The last mathematical inequality is not called an open conjecture. |
| Weaker helper hypotheses | Proved; the kernel-checked private helper `randic_lower` assumes a positive maximum degree; `adjacency_degree_bound` assumes a positive chosen degree, $d\ge1$ and degree at most $d$ away from that vertex; `lap_second_degree` assumes distinct vertices ordered by degree. None assumes connectedness. A separate disconnected-graph target theorem is not delivered. |

No inspected source argument uses Conjecture 4 as a proved premise. The
settlement resolves this named inequality without a claim about the
source's other conjectures.

### Literature status

The preregistration records source and companion-index checks, related
classical Randić and Laplacian bounds, journal-version discovery and
bounded external-settlement searches. Zhang's survey, arXiv:1111.2897v1,
Theorem 4.2, attests the stronger Li–Pan bound $\mu_2\ge d_2$ for connected
graphs of order at least three; this is literature evidence, not a theorem
formalized here. The source also reports the stronger classical
Bollobás–Erdős bound $R\ge\sqrt{n-1}$. These classical ingredients are not
claimed as new mathematical discoveries. No exact prior settlement was
identified in the inspected scope; literature completeness is
ASSUMED-UNVERIFIED. The module provides a formal settlement of the named
assertion, without a worldwide priority claim.

## ASSUMED-UNVERIFIED

Literature completeness, unindexed settlements and complete enumeration
of citing works are ASSUMED-UNVERIFIED. The preregistration records HTTP
429 responses from OpenAlex and Semantic Scholar, incomplete pagination
and unavailable readable search results. The registration evidence named
in #29101 is unfinished. Experiments establish exactly their displayed
finite checks and do not prove the unrestricted graph statement.
