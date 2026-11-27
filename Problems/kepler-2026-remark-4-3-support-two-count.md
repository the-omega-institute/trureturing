---
slug: kepler-2026-remark-4-3-support-two-count
bibkey: kepler2026balphaspectral
doi: 10.48550/arXiv.2607.25221
url: https://arxiv.org/abs/2607.25221v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SpectralGraph/KeplerSupportTwo.graphwise_count
---

# Kepler's count of signed support-two eigenvectors

## Problem

Garrett Kepler, *Some Spectral Properties of the Bα Matrix of a Graph*,
arXiv:2607.25221v1, Remark 4.3, printed p. 8, asks

> What Theorem 4.2 does not address is how many of these types of eigenvectors a given graph has. This may be an interesting place for exploration.

“These types” have a single entry $+1$, a single entry $−1$, and zero
everywhere else. Definition 1.5, printed p. 1, sets
$B_\alpha=\alpha A+(1-\alpha)L=(1-\alpha)D+(2\alpha-1)A$ for
$\alpha\in[0,1]$. The graph is finite, simple and undirected.
[Remark 4.3](https://arxiv.org/pdf/2607.25221v1#page=8)
· [Definition 1.5](https://arxiv.org/pdf/2607.25221v1#page=1)

### Statement echo

| Source or answer clause | Lean counterpart |
| --- | --- |
| One finite simple undirected graph | `G : SimpleGraph V` on any `Fintype V`, with decidable equality and adjacency as instances |
| Definition 1.5 and the source interval | `bAlpha G α` uses Mathlib adjacency and Laplacian. The theorem quantifies over all real α |
| Exactly one $+1$, one $−1$, and zeros elsewhere | `IsSignedEigenvector` and the subtype `SignedEigenvectors G α` |
| Eigenvector for a real eigenvalue | Existential `eigenvalue : ℝ` in `IsSignedEigenvector` with `Matrix.mulVec` |
| One admissible unordered support per qualifying distinct pair | `SupportPairs G α` uses `Sym2 V` through the edges of `classGraph (classSetoid G α)` |
| Exact number of unordered supports | `Nat.card (SupportPairs G α) = classPairSum (classSetoid G α)` |
| Exact number of signed vectors | `Nat.card (SignedEigenvectors G α) = 2 * classPairSum (classSetoid G α)` |

The sum is $\sum_C\binom{|C|}{2}$. The classes are equal-degree classes at
$\alpha=1/2$ and twin classes otherwise. Twins agree in adjacency to each
vertex outside their pair. Genuine edges and nonedges within a class both
contribute. An empty or singleton graph gives zero supports and zero vectors.

## Motivation

The count provides the per-graph information asked for in Remark 4.3.
Coincidence of the outside adjacency rows and equality of the diagonal entries
at the exceptional parameter give two different partitions of the vertices.
A class of size $m$ contributes $\binom m2$ supports with two orientations
each. Eigenvalue multiplicity and linear dependence among these vectors are
separate questions.

## Gap

The Tier 1 screen in the preregistration records the checked v1 text, arXiv
history and title/author searches, citation tracing, MathDB and the repository
problem register. Pastén et al., Corollary 5, give multiplicity lower bounds
from twin classes. Monterde treats twin eigenvectors for a generalized
adjacency matrix with nonzero adjacency coefficient. The screen found no exact
fixed-graph count with both the equal-degree branch and the two orientations.
[Preregistration](https://github.com/the-omega-institute/trureturing/issues/34897)
· [Library note](../Library/Combinatorics/kepler2026balphaspectral.md)

## Route

Evaluate $B_\alpha(e_u-e_v)$ at $u$, at $v$, and off the pair. At an
outside vertex the equation is $(2\alpha-1)(A_{wu}-A_{wv})=0$.
Away from half it forces the twin relation, and twins have equal degree by
the transposition of (u,v). At half the outside equation is automatic and
the two inside rows are equivalent to equality of degrees. Inside the pair
the eigenvalue is $(1-\alpha)d-(2\alpha-1)\varepsilon$, where $d$
is the common degree and $\varepsilon$ indicates adjacency within the pair.

The quotient of the appropriate equivalence relation indexes complete
class graphs. A dart decomposes into its unique quotient class and a dart in
the complete graph on that class. Mathlib's complete-graph edge count and
dart count give the binomial sum. The realization of a dart as
(e_u-e_v) is bijective onto the signed subtype. Reversing the dart
negates the vector.

## Falsifier

Any graph and parameter with a qualifying distinct pair across classes, a
nonqualifying pair within a class, an incorrect class contribution, or a
support admitting other than its two prescribed signed vectors would refute
the proposed count. The row calculation and the two cardinality equalities
exclude those cases uniformly.

## Evidence

The author proof and independent replay used identical Lean source bytes
with SHA-256 `fa3c19aa9eb8d2394f5f02568b9319d6b48a6bedff3a6a54475243a879b4d64b`.
The transferred endpoint is
`D5.S3.Combinatorics.SpectralGraph.KeplerSupportTwo.graphwise_count`.
The one-thread replay uses Lean 4.35.0 and Mathlib at
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Its axiom closure is
`propext`, `Classical.choice` and `Quot.sound`. The typed Reg audit
retains both equalities and binds the actual doubling function in the
signed-vector equality.
[Forecasts before the probe](https://github.com/the-omega-institute/trureturing/issues/34897#issuecomment-7222052374)
· [Settlement](https://github.com/the-omega-institute/trureturing/issues/34897#issuecomment-7222718681)

## Triage

| Item | Status |
| --- | --- |
| Remark 4.3 for every finite simple graph and each real α | Proved in Lean, including the full class sum and exact factor of two |
| Equal-degree exception at $1/2$, twin condition elsewhere, and pair eigenvalue | Proved by the row equations and checked in the scoped Lean replay |
| Orders zero and one and parameter landmarks $0,1/2,1$ | Checked in Lean |
| Theorem 4.1's description using an internal $K_2$ | Separate source correction. The fixed-graph characterization admits false twins, for example the two leaves of $P_3$, and has a separate half-parameter branch |
| Theorem 4.2's labeled-graph proportion and limit | Separate source correction. Preregistration explains that the product counts pair–graph incidences, with a proposed bound $\binom n2 2^{-(n-2)}$ away from half and an equal-degree pigeonhole argument at half. The counting bijection, union bound, limit and all-graphs argument are outside the compiled result |

## ASSUMED-UNVERIFIED

Literature completeness and priority beyond the bounded records above remain
unverified. The separate labeled-graph and limiting claims about Theorem 4.2
have no compiled proof in this package.
