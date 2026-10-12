---
slug: heib-bruschi-2026-conjecture-80-hidden-center-refutation
bibkey: heib2026structural
doi: 10.48550/arXiv.2601.16161
url: https://arxiv.org/abs/2601.16161v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Algebra/HeibBruschiHiddenCenterRefutation.result
---

# A hidden central direction refutes Heib–Bruschi Conjecture 80

## Problem

T. Heib and D. E. Bruschi, *On the structural properties of Lie algebras via associated
labeled directed graphs*, arXiv:2601.16161v1, attach to a minimal-graph-admissible basis of a
Lie algebra (every bracket of two basis vectors is a multiple of a basis vector) the directed
graph with an edge from $x_j$ to $x_\ell$, labelled $x_k$, whenever $[x_j,x_k]$ is a nonzero
multiple of $x_\ell$. A vertex subset has the ideal-graph-property when no edge leaves it.
Conjecture 80 (§IV.D, p. 46) states that if such an algebra has a nonzero center, then some proper
non-empty vertex subset has the ideal-graph-property and spans a solvable ideal. The verbatim
statements are in [the literature note](../Library/LieTheory/heib2026structural.md).

Issue [#15636](https://github.com/the-omega-institute/trureturing/issues/15636) fixes the
reading over every field, as the paper's convention "We denote any field with the symbol
$\mathbb F$" requires, for the given minimal graph $G(V,E)$ of the conjecture.

## Motivation

The paper reads centers, derived series and ideals off these graphs for Lie algebras that arise
in quantum dynamics. It reports that Conjecture 80 holds in dimension 3 and that "all attempts
to construct counterexamples have failed", and proposes Conjecture 82 as a refinement that
would imply it. Conjecture 83, its converse direction, is refuted in
[the affine-algebra dossier](heib-bruschi-2026-conjecture-83-affine-refutation.md).

## Gap

Issue #15636 records the literature check before any Lean:
- arXiv lists only v1 of the paper;
- the two citing works found by Semantic Scholar (arXiv 2610.04001, 2603.04916) and the first
  author's arXiv 2609.15302 contain no occurrence of "Conjecture 80" or "ideal-graph";
- Zenodo ("ideal-graph-property", "minimal-graph-admissible", the authors), Crossref,
  google-deepmind/formal-conjectures and web searches return no settlement;
- the repository had only the Conjecture 83 result.

`not-found-in-searched-scope`.

## Route

Let $L=K^4$ with standard basis $e_1,\dots,e_4$ and
$[u,v]=\big(b(r+s)-(c+d)q,\ (c+d)p-a(r+s),\ aq-bp,\ 0\big)$ for $u=(a,b,c,d)$, $v=(p,q,r,s)$.
This is the cross-product algebra $(K^3,\times)\oplus K$ written in the basis $e_1,e_2,e_3,e_3+z$
with $z$ central; the module transports the bracket along this linear isomorphism.

1. **Hypotheses hold.** The basis brackets are $[e_1,e_2]=e_3$, $[e_2,e_3]=e_1$,
   $[e_3,e_1]=e_2$, $[e_1,e_4]=-e_2$, $[e_2,e_4]=e_1$, $[e_3,e_4]=0$, so the basis is admissible
   with coefficients $\pm1$, and $e_4-e_3\neq0$ is central.
2. **Closed subsets.** The edges leaving $e_1$ reach $e_2,e_3$; those leaving $e_2$ reach
   $e_1,e_3$; those leaving $e_3$ reach $e_1,e_2$; those leaving $e_4$ reach $e_1,e_2$. A
   non-empty subset with the ideal-graph-property therefore contains $\{e_1,e_2,e_3\}$, and the
   only proper one is $\{e_1,e_2,e_3\}$.
3. **Not solvable.** Its span $I$ satisfies $e_1=[e_2,e_3]$, $e_2=[e_3,e_1]$, $e_3=[e_1,e_2]$,
   so $[I,I]=I\neq0$ and the derived series of $I$ never reaches $0$.

All coefficients are $\pm1$, so the argument is the same over every field, characteristic 2
included.

## Falsifier

The refutation would fail if the conjecture quantified over some admissible basis rather than
the given minimal graph: in the basis $e_1,e_2,e_3,z$ the subset $\{z\}$ has the
ideal-graph-property and spans the abelian ideal $Kz$.

## Evidence

The canonical source is `D5/S3/Quantum/Algebra/HeibBruschiHiddenCenterRefutation.lean` (575 lines).
Its public declarations are `conjecture80Over`, `claim` and `result`.

It imports:
- the frozen `D5/S3/Quantum/Algebra/HeibBruschiCenterlessIdealGraphRefutation`, for `IsAdmissible`, `Edge` and `IdealGraphProperty`;
- `Mathlib.Algebra.Lie.Prod`, `Mathlib.Algebra.Lie.Solvable`, `Mathlib.Algebra.Lie.TransferInstance` and `Mathlib.LinearAlgebra.CrossProduct`.

It builds the algebra from Mathlib's `Cross.lieRing` and `LieRing.ofAssociativeRing`, transported by `AddEquiv.lieRing` and `LinearEquiv.lieAlgebra`. It uses `Pi.basisFun`, `LieAlgebra.derivedSeries` and `LieAlgebra.IsSolvable`.

It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Statement identifiers:
- module: `sha256:37f06d575851cb18e5648c35cc0680c9a94b95dd40862e3888012794f710c62b`;
- `result`: `sha256:cab63d48f62efa575f924cbe083d998c51c4d71b47df888c6b5ab25e2fbd1428`;
- `claim`: `sha256:eba1d1f95566917fe277e13d21a5c4bee35ce06da3d0ec5424fd4546a36ecf09`;
- `conjecture80Over`: `sha256:9207f05543edb4860d49c1ef84a10b2d9d1b288e3cebb153bfa5f419c425953a`.

The Freeze event is `sha256:20d67870b935cdba4d4d378366e03a080fe3627e75998ea35fb2d31eae79eeee`. Its project-level prerequisite is the Conjecture 83 module's event `sha256:35ec93190d6f1ffe1019e8ade7770514b05429674e1f25e6e65e774091720cf1`.

## Triage

Tier 1 conjecture of a 2026 paper, preregistered in issue #15636 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| conjecture_fails | bind-only | none | open-problem-resolution |
| result | bind-only | none | open-problem-resolution |

The private theorems are bind-only and are used on the proof path of `result` (CLAUDE.md §3.2 「有消费的辅助声明」):
- the basis coordinates (`hiddenBasis_zero` … `hiddenBasis_three`);
- the basis brackets;
- `hiddenBasis_admissible` and `hidden_center_nonzero`;
- the edges and `hidden_graph_classification`;
- `hiddenIdeal_span` and `hiddenIdeal_not_solvable`.

Utility is `certified-instance` with basis `refutes` of `claim`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** `claim`, Conjecture 80 asserted over every field, is false. `result`
specializes the private `conjecture_fails`, which proves that Conjecture 80 fails over each field
$K$: the algebra above has a nonzero center, an admissible basis, and no proper non-empty vertex
subset with the ideal-graph-property that spans a solvable ideal.

**Argued, not formalized.**

- The counterexample depends on the basis. In the direct-sum basis $e_1,e_2,e_3,z$ the
  conclusion holds through $\{z\}$. A repaired statement — some minimal-graph-admissible basis
  exhibits a solvable coordinate ideal whenever the center is nonzero — is not contradicted by
  this example. Whether it holds in general is not decided here.
- The mechanism is general. Let $\mathfrak s$ be a perfect algebra with an admissible basis whose
  minimal graph is strongly connected (such as the cross-product algebra). In
  $\mathfrak s\oplus Kz$, replace the central basis vector $z$ by $s+z$ for a basis vector $s$
  of $\mathfrak s$. Brackets with $s+z$ equal those with $s$, so the basis stays admissible and
  $s+z$ has the same outgoing edges as $s$. Every non-empty closed subset then contains the whole
  basis of $\mathfrak s$, whose span is not solvable, while $(s+z)-s$ is central.
- Conjecture 82 is not contradicted. By the paper's Lemma 81 its hypothesis
  $\bigcap_\ell\operatorname{Ker}\alpha^{(\ell)}=\{0\}$ means the center is zero, and the
  example has a nonzero center, so it satisfies Conjecture 82 vacuously.

**Open.** Whether Conjecture 80 holds for the repaired reading above, and whether it holds for
nilpotent or solvable algebras with the given basis, is not determined by this settlement.

**Effect on the paper.** Conjecture 80 is false as stated. The paper states that Conjecture 80
holds if Conjecture 82 is valid. Since Conjecture 80 is false, that implication can hold only if
Conjecture 82 is false; the example satisfies Conjecture 82, so the argument the paper gives for
the implication (no proper subset with the ideal-graph-property forces a zero center) does not
reach it. The paper's dimension-3 verification is consistent with the example, which has
dimension 4.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty, priority, or the
absence of an independent counterexample.
