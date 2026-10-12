---
bibkey: dai2026crosspolytopes
authors: Ziyi Dai, Qilin Hou, Zhiyuan Liu, Warut Thawinrak and Hongyu Wang
year: 2026
title: "Counting Lattice Points in Minkowski Sums of Cross Polytopes"
doi: null
url: https://arxiv.org/abs/2608.16037v2
claim: "Equation (3) defines coordinate cross-polytope Minkowski sums; Problem 5.4 asks for their f-vectors and the ordinary h-vectors of the simple members."
strata_touched:
  - D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts
license: citation-only
triage: anchor
---

# Coordinate cross-polytope sums and their faces

## Verified locator

The versioned primary source is [arXiv:2608.16037v2](https://arxiv.org/abs/2608.16037v2), with its [HTML text](https://arxiv.org/html/2608.16037v2).
Equation (3) in the introduction defines
$Q_G(k_1,\ldots,k_m)=\sum_i k_i\diamondsuit_{I_i}$, where
$\diamondsuit_I=\operatorname{conv}\{e_j,-e_j:j\in I\}$ and the nonempty
$I_i$ are the right-neighbor sets of the left vertices of a bipartite graph.
The lattice-point setting uses nonnegative integer coefficients.
The HTML names the five authors above and states CC BY 4.0. This note
provides citation and a short quotation rather than redistributing the paper.

Section 5, Problem 5.4, concludes:

> Given their close connection to Minkowski sums of simplices, can one apply similar tools and techniques in [15] to study the faces of Minkowski sums of cross polytopes? In particular, can one give a formula for their f- and h-vectors (for those simple polytopes)?

The preceding sentences refer to their face posets and to the type A
generalized permutohedra studied by Postnikov, Reiner and Williams.
This question concerns ordinary face enumeration, not the Ehrhart
$h^*$-polynomials investigated elsewhere in the paper.

## Mathematical correspondence

The coordinate indices are represented by `Fin n` and the summand indices
by `Fin m`. The formal statement allows every nonnegative real weight,
including zero, and every nonempty coordinate support. Repeated supports,
disconnected incidence graphs, unused coordinates and empty active sets
are retained. The actual Minkowski sum is `actualQ`; its nonempty exposed
faces are counted by the real dimension of their actual affine-span
directions in `geometricFaceCount`.

The signed acyclic formula and its dimension-preserving correspondence are
repository-derived mathematical content motivated by Problem 5.4; they are
not asserted to be a theorem quoted from this source. Their unsigned data
consist of a zero block and nonempty selected coordinate sets for the
remaining positive-weight summands. Equality components retain every
active coordinate outside the zero set. Acyclicity of the strict component
relation includes the exclusion of self-loops. One global sign per selected
coordinate yields the factor $2^{|T|}$, and the face dimension is $d-c$.

## Related results and scope

Benedetti, Bergeron and Machacek, *Hypergraphic polytopes: combinatorial
properties and antipode*, arXiv:1712.08848v2, Theorem 2.18,
DOI `10.4310/joc.2019.v10.n3.a4`, gives a type A acyclic-hypergraph
face correspondence. Its independent positive coordinate vertices do
not directly provide the signed coordinate model here.
Thawinrak, *Counting Lattice Points in Generalized Permutohedra From A to B*,
arXiv:2512.01332v2, Section 2.3 and Problems 5.1–5.2, supplies the wider
type B context. The cross-polytope sums form the family treated here;
no formula for all type B generalized permutohedra is inferred.

The bounded source search recorded in
[issue 14604](https://github.com/the-omega-institute/trureturing/issues/14604)
did not find a direct settlement of this exact formula in the searched
sources. This is a search boundary, not an exhaustive priority claim.
The ordinary $h$-polynomial for a relatively $d$-dimensional simple member
is obtained by the standard transform
$h_Q(z)=\sum_{r=0}^d f_r(Q)z^{d-r}(1-z)^r$.
Determining which members are simple and enumerating Ehrhart data are
separate questions.
