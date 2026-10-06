---
slug: heib-bruschi-2026-conjecture-83-affine-refutation
bibkey: heib2026structural
doi: 10.48550/arXiv.2601.16161
url: https://arxiv.org/abs/2601.16161v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Algebra/HeibBruschiCenterlessIdealGraphRefutation.result
---

# The affine Lie algebra refutes Heib–Bruschi Conjecture 83

## Problem

T. Heib and D. E. Bruschi, *On the structural properties of Lie algebras via associated
labeled directed graphs*, arXiv:2601.16161v1, attach to a basis of a Lie algebra in which
every bracket of two basis vectors is a multiple of a basis vector (a minimal-graph-admissible
basis) the directed graph with an edge from $x_j$ to $x_\ell$, labelled $x_k$, whenever
$[x_j,x_k]$ is a nonzero multiple of $x_\ell$. A vertex subset has the
ideal-graph-property when no edge leaves it. Conjecture 83 states that a
minimal-graph-admissible Lie algebra with trivial center either (i) has no proper non-empty
vertex subset with the ideal-graph-property, or (ii) is a direct sum of components with
trivial center whose every minimal graph has no such subset. The verbatim statements are in
[the literature note](../Library/LieTheory/heib2026structural.md).

Issue [#13676](https://github.com/the-omega-institute/trureturing/issues/13676) fixes the
reading over every field, as the paper's convention "We denote any field with the symbol
$\mathbb F$" requires, with the direct sum read as an internal direct sum of ideals over an
arbitrary index type.

## Motivation

The paper uses the graphs to read off centers, derived and lower central series and ideals,
for Lie algebras that arise in quantum dynamics. Conjecture 83 is its proposed converse to
Conjecture 80 (a nonzero center forces a proper vertex subset with the ideal-graph-property):
trivial center should force the graph to be strongly connected unless the algebra splits.
`D5/S3/Quantum/Algebra/HeibBruschiCenterlessIdealGraphRefutation.result` shows that the
converse fails already in dimension two, over every field.

## Gap

Issue #13676 records the literature check before any Lean: arXiv lists only v1 of the paper;
the first author's later papers (arXiv 2609.15302, 2610.04001) and the only forward citation
found (arXiv 2603.04916) do not discuss Conjecture 83; Zenodo phrase searches
("graph-admissible", "ideal-graph-property", the title phrase, the identifier) return no
record; web searches return no settlement; the repository had no related result. The paper
names $\mathfrak{aff}(\mathbb F)$ as an example of a solvable non-nilpotent algebra but tests
Conjecture 83 only against $\mathfrak{su}(2)\oplus\mathfrak{su}(2)$.
`not-found-in-searched-scope`.

## Route

Let $A=K\times K$ with $[(a,b),(c,d)]=(0,ad-cb)$, $X=(1,0)$, $Y=(0,1)$, so $[X,Y]=Y$.

1. **Hypotheses hold.** $(X,Y)$ is admissible with $\alpha_{12}=1=-\alpha_{21}$,
   $\delta(1,2)=\delta(2,1)=2$; the center is zero because $[aX+bY,X]=-bY$ and
   $[aX+bY,Y]=aY$.
2. **(i) fails.** The edges are $X\to Y$ (label $Y$) and $Y\to Y$ (label $X$), so $\{Y\}$ is
   a proper non-empty subset with the ideal-graph-property.
3. **Every nonzero ideal contains $Y$.** If $aX+bY\ne0$ lies in an ideal, then $Y$ does: by
   scaling when $a=0$, and from $[aX+bY,Y]=aY$ when $a\ne0$.
4. **(ii) fails.** Two different components of an internal direct sum have zero intersection,
   so at most one is nonzero; as $A\ne0$ exactly one is, and it equals $A$. The basis
   transported to it along $A\cong I_{j_0}$ is admissible and keeps the subset $\{Y\}$.

## Falsifier

The refutation would fail if the reading of (ii) admitted a decomposition of $A$ in which no
component carries $\{Y\}$, for instance a direct sum of vector spaces that are not ideals;
the paper's "direct sum" of Lie algebras requires ideals.

## Evidence

The canonical source is
`D5/S3/Quantum/Algebra/HeibBruschiCenterlessIdealGraphRefutation.lean`. Its public
declarations are `IsAdmissible`, `Edge`, `IdealGraphProperty`, `HasProperIdealGraphSubset`,
`conjectureOver`, `claim`, `conjecture_fails` and `result`; it imports only
`Mathlib.Algebra.Lie.Abelian` and uses Mathlib's `LieIdeal`, `LieAlgebra.center`,
`DirectSum.IsInternal` and `LieIdeal.topEquiv`. It uses only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
The module statement is `sha256:03f8b723eb159d4644f6d1dd6c33a7a4178d57f9b4baa65c19c6c525fdf57780`, the `result` statement `sha256:b4e0d950bf87a2ff041d6ce3d2b7db1dab3357dfee2daba85e00e2c59f35220d` and the `claim`
statement `sha256:08773a6e3d525df761e901ec5860871266cca8ff702a869cafa2f8c6c36470d4`. The Freeze event is `sha256:35ec93190d6f1ffe1019e8ade7770514b05429674e1f25e6e65e774091720cf1`; it has no project-level prerequisite.

## Triage

Tier 1 conjecture of a 2026 paper, preregistered in issue #13676 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| conjecture_fails | bind-only | none | open-problem-resolution |
| result | bind-only | none | open-problem-resolution |

The private theorems (`affineBasis_admissible`, `affine_center_zero`,
`affineBasis_proper_subset`, `ideal_contains_y`, `internal_has_top`, `admissible_map`,
`proper_subset_map`) are bind-only and are used on the proof path of `result` (CLAUDE.md
§3.2 「有消费的辅助声明」). Utility is `certified-instance` with basis `refutes` of `claim`.
There is no digestion atom.

### What the settlement shows

**Proved by `result` and `conjecture_fails`:** Conjecture 83 fails over every field; the
two-dimensional affine Lie algebra satisfies its hypotheses and neither conclusion.

**Established inside the proof.** Every nonzero ideal of $\mathfrak{aff}(K)$ contains $Y$,
so $\mathfrak{aff}(K)$ has no nontrivial decomposition as an internal direct sum of ideals
(`ideal_contains_y`, `internal_has_top`); admissible bases and proper subsets with the
ideal-graph-property are carried along Lie isomorphisms (`admissible_map`,
`proper_subset_map`).

**Argued, not formalized.**

- A vertex subset $W$ with the ideal-graph-property spans an ideal: for $w\in W$ and a basis
  vector $x_k$, $[w,x_k]$ is zero or a nonzero multiple of some $x_\ell$, and then there is an
  edge from $w$ to $x_\ell$, so $x_\ell\in W$. The conjecture therefore fails whenever a
  centerless admissible algebra has a proper ideal spanned by basis vectors and cannot be
  split into components without such ideals; a solvable radical attached to a centerless
  quotient without a complement, as $\mathrm{span}\{Y\}$ in $\mathfrak{aff}(K)$, is the
  mechanism.
- The two natural repairs of (i) also fail: restricting it to subsets that span a solvable
  ideal is still refuted by $\mathfrak{aff}(K)$, since $\mathrm{span}\{Y\}$ is abelian;
  restricting it to subsets that span a non-solvable ideal is refuted in characteristic $0$
  by $\mathfrak{sl}_2\oplus\mathfrak{aff}$ with the basis $(e,h,f,X,Y)$, where $\{e,h,f\}$ has
  the ideal-graph-property and the $\mathfrak{aff}$ part keeps $\{Y\}$.
- The conjecture holds for every Lie algebra that is a direct sum of simple ideals (in
  characteristic $0$, every semisimple algebra): each simple component has trivial center,
  and by the first item a proper non-empty subset with the ideal-graph-property in a minimal
  graph of a component would span a proper nonzero ideal of a simple algebra.

**Open.** Which corrected form the authors intend (for example, (ii) replaced by a
condition on the radical) is not determined by the paper.

**Effect on the paper.** Conjecture 83 is false as stated. Conjecture 80 (a nonzero center
forces a proper subset with the ideal-graph-property that spans a solvable ideal) and
Conjecture 82 are not affected: $\mathfrak{aff}(K)$ has trivial center, and its only proper
subset with the ideal-graph-property spans a solvable ideal.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty, priority, or
the absence of an independent counterexample.
