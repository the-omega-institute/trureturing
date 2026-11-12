---
slug: nath2021-commuting-cn-conjecture2
bibkey: nath2021commutingcn
doi: 10.3390/sym13091651
url: https://doi.org/10.3390/sym13091651
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/CommonNeighborhood/NoncentralBound.result
---

# Common-neighborhood energy of noncentral commuting graphs

## Problem

Nath–Fasfous–Das–Shang, *Common Neighborhood Energy of Commuting Graphs of
Finite Groups*, Symmetry 13(9), 1651, Section 4, printed page 11, states:

> Conjecture 2. Γc(G) is not CN-hyperenergetic.

For every finite nonabelian group $G$, let $Z=Z(G)$, $V=G\setminus Z$ and
$n=|V|$. Vertices are individual group elements. Distinct $x,y\in V$ are
adjacent exactly when $xy=yx$. Let $C$ be the real symmetric matrix with
$C_{ii}=0$ and $C_{ij}=|N(i)\cap N(j)|$ for $i\ne j$. If its real eigenvalues,
counted with algebraic multiplicity, are $\lambda_1,\ldots,\lambda_n$, the
assertion is

$$
\sum_{i=1}^n |\lambda_i|\le 2(n-1)(n-2).
$$

The source explicitly specifies the zero diagonal and $C=A^2-D$. Its adjacent
prose sentence assigning the degree to a diagonal entry contradicts these
specifications; the assertion here uses the explicit matrix definition. The
complete-graph benchmark is the source's Lemma 1. There is no restriction to
abelian centralizers, conjugacy classes, quotients, or particular group families.
The prospective event and unchanged quantifiers are fixed in
[#29431](https://github.com/the-omega-institute/trureturing/issues/29431#issuecomment-6811765962).

## Motivation

The motivating declaration is
`D5/S3/Combinatorics/Graph/CommonNeighborhood/NoncentralBound.result`.
It retains every finite nonabelian group and the literal spectral energy.
The general graph estimate used below is prior mathematics, rather than a
separate research result of this application.

## Gap

The universal inequality is proved by `NoncentralBound.result`. The mathematical
bridge includes the actual common-neighbor entries, full real spectrum, proper
centralizers, and finite-cardinality casts. Literature completeness and independent
prefreeze review remain separate from this mathematical statement.

## Route

For any finite simple graph, entrywise counting gives $C=A^2-D$.
Both $A^2$ and $D$ are positive semidefinite. In an orthogonal eigenbasis of $C$,
write $p_i,q_i\ge0$ for their diagonal quadratic terms. Then
$|\lambda_i|=|p_i-q_i|\le p_i+q_i$. Trace invariance gives

$$
E_{CN}\le\operatorname{tr}(A^2)+\operatorname{tr}(D)
       =2\sum_v d_v=4m.
$$

The bound $E_{CN}\le4m$ is already in Jannat–Nath–Das,
arXiv:2402.15416v1, Remark 4.7, equation (6), printed page 15.
Simultaneous diagonalization of $A$ and $D$ is unnecessary.

Put $N=|G|$ and $z=|Z|$, so $n+z=N$. For each noncentral $x$, its centralizer
$K=C_G(x)$ is proper, hence has index at least two and $2|K|\le N$.
The center, the singleton $\{x\}$ and the graph neighbors of $x$ are disjoint
subsets of $K$. Therefore

$$
d_x+z+1\le|K|,\qquad 2d_x\le n-z-2,
\qquad E_{CN}\le n(n-z-2).
$$

The identity belongs to the center, so $z\ge1$. Nonabelianness supplies a
noncentral element; the last degree estimate gives $n\ge z+2\ge3$.
All small-order cases therefore satisfy the domain of the complete-graph formula.
The final comparison is

$$
2(n-1)(n-2)-n(n-z-2)=(n-2)^2+nz\ge0.
$$

The cardinality bounds are established in the natural numbers, transported to
the integers for subtraction, and then cast to the reals. The final benchmark
subtracts from the real image of $n$, without truncated natural subtraction.

## Falsifier

A finite nonabelian group whose literal zero-diagonal CN matrix has spectral
energy above this benchmark would contradict the theorem. A conjugacy-class
graph, a degree-diagonal matrix, or an energy without eigenvalue multiplicities
would test a different assertion.

## Evidence

The primary publisher PDF is
<https://mdpi-res.com/d_attachment/symmetry/symmetry-13-01651/article_deploy/symmetry-13-01651.pdf>,
SHA-256 `2f02c5ddc74678fa272ea30169d5dc75aae11bed13a64ea2031f6de60f1f000b`.
The source graph and energy are on printed pages 1–2; Conjecture 2 is on page 11.
The publisher source is CC BY 4.0. The citation-only note and this independent
exposition reproduce no source proof, code, figure or table.

The supplier PDF <https://arxiv.org/pdf/2402.15416v1> has SHA-256
`785ea16aa0bdbd4c7bb684a890497e468c0e4947bc2256b6ac131de45464eb66`.
Its Remark 4.7, equation (6), gives the general bound used in Route.

The existing `SubgroupGenerating.CyclicExtensionRefutation` owns the generic
`commonNeighbourMatrix`, `sourceMatrix`, `source_matrix_isHermitian`,
`graphSpectrum` and `graphEnergy`; those definitions are reused unchanged.
Pinned Mathlib's `Matrix.IsHermitian.roots_charpoly_eq_eigenvalues` identifies
this full eigenvalue multiset with the characteristic roots, including their
algebraic multiplicities. The CN branch has zero centering.

`NoncentralBound.result` and its private helpers prove the all-group application.
The matching typed Blueprint states the same group hypotheses, graph and real
cardinality benchmark. The intended admission basis is `open-problem-resolution`
for the prospectively registered full source assertion; independent fidelity and
proof-shape review remain required before freezing.

## Triage

- Proved: the entire universal inequality in Problem, with no spectral assumption
  or restriction on the finite nonabelian group.
- Proved within the result: proper-centralizer counting gives the intermediate
  estimate $E_{CN}\le n(n-z-2)$ and $n\ge3$, $z\ge1$.
- Prior mathematics: the arbitrary-graph estimate $E_{CN}\le4m$.
- Open here: an optimal bound for each group order, equality cases for sharper
  estimates, and the source's distinct planar/toroidal Conjecture 1. They are
  not additional conclusions of this theorem.
- The source's previously proved family cases remain valid specializations.
  Conjecture 3 concerns clique unions and has a separate literature scope.

## ASSUMED-UNVERIFIED

The inherited literature screen is bounded: six citing full texts, exact MathDB
solution pages, and the original 2011 Alwardi–Soner–Gutman PDF remain unread.
arXiv:2605.22160v1 treats clique unions and CC-ring cases; DOI
10.3390/math13111834 treats dihedral and generalized-quaternion families.
Those readings do not establish worldwide absence of an earlier all-group
settlement, global priority, or an exhaustive bibliography.

The [linked registration boundary](https://github.com/the-omega-institute/trureturing/issues/29340#issuecomment-6807007168)
remains applicable until a current source-bound registration is validated.
A compiled Reg proof alone does not imply `declared_validated`.
This dossier does not certify independent review, freeze, required CI, or merged
delivery, and does not revise the earlier unit's unresolved settlement.
