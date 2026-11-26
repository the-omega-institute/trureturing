---
slug: pineda-montoya-et-al-2026-separating-weights-question-7-5
bibkey: pinedamontoya2026separatingweights
doi: 10.48550/arXiv.2611.21979
url: https://arxiv.org/abs/2611.21979v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation.result
---

# Separating weights for three graph operators

## Problem

Santiago Pineda Montoya, Edisson Gallego González, Jaiberth Porras Barrera
and Johan Heriberto Rúa Muñoz, *Laplacian Eigenvectors of Generically
Weighted Graphs Have Pairwise Distinct Coordinates*, Question 7.5, ask:

> Do the analogues of Theorem 1.2 hold for normalized Laplacians, for adjacency matrices with a fixed support, and for directed graphs with a spanning diverging tree, the setting in which simple spectrum is generic by [4, Theorem 6.6]? The Krylov certificate of Section 3 adapts to any family of symmetric matrices; the construction of a witness is the part that depends on the operator.

[Question 7.5](https://arxiv.org/html/2611.21979v1#S7.Thmtheorem5) ·
[Definition 1.1 and Theorem 1.2](https://arxiv.org/html/2611.21979v1#S1.SS2) ·
[Preregistration #33474](https://github.com/the-omega-institute/trureturing/issues/33474)

Each analogue asks for every order $n\ge 2$ and every admissible support
on $\mathrm{Fin}(n)$ whether there are a degree $d\in\mathbb N$ and a
nonzero homogeneous $P\in\mathbb Z[w_e:e\in E]$ of degree $d$ such that
separation is equivalent to $P(w)\ne 0$ for every strictly positive
weight function $w$. Here $E$ is the type of actual edges or arcs. The
degree is existential because the question gives no analogue degree.
The three propositions form the disjunction `claim` in
`D5.S3.Combinatorics.SpectralGraph.PinedaSeparatingWeightsRefutation`.

### Statement echo

| Source clause and convention | Lean counterpart |
| --- | --- |
| Fixed connected simple support, actual unordered edges | `NormalizedClaim` and `AdjacencyClaim` quantify over `SimpleGraph (Fin n)`, `G.Connected`, and weights indexed by `G.edgeSet`. |
| Loopless directed support with a spanning diverging tree | `DirectedClaim` uses `Digraph (Fin n)`, irreflexive adjacency and a spanning subdigraph with a native out-arborescence. Its weights are indexed by the subtype of ordered arcs. |
| Symmetric normalized Laplacian | `normalizedSep` uses the pinned `normLap` on weighted adjacency with row degrees and inverse square-root factors. |
| Weighted adjacency on the fixed support | `adjacencySep` uses the symmetric weighted adjacency, zero off the support. |
| Directed Laplacian | `directedSep` uses the complexification of the receiving-degree diagonal minus the receiving adjacency, with arcs from column to row. |
| S1 and S2 | `Separating` requires a separable characteristic polynomial and every coordinate of every nonzero right eigenvector to be nonzero, including at eigenvalue zero. The two undirected branches use real vectors and the directed branch uses complex vectors. |
| S3 | `Separating` requires injectivity of the coordinate function on the chosen modes. The branches use orthogonality to square-root degrees, eigenvalues below the top adjacency eigenvalue, and nonzero directed eigenvalues, respectively. |
| Nonzero homogeneous integer polynomial on the positive orthant | Each branch keeps `P ≠ 0`, `P.IsHomogeneous degree`, positivity at every actual edge or arc, and the separation iff real nonvanishing. |
| Each universal analogue fails | The three branch theorems refute their respective propositions. The closed theorem `result` has type `Not claim`. |

## Motivation

The combinatorial Laplacian has a constant zero mode, and the theorem
controls the remaining modes on every connected support. Question 7.5
asks how much of that separation survives the change of operator. In the
directed setting the question cites generic simplicity, which addresses
S1. [Poignard, Pereira and Pade, Theorem 6.6](https://arxiv.org/pdf/1704.01677v1#page=13)

## Gap

Section 6.4 treats paths for the combinatorial Laplacian. The literature
screen in #33474 records antecedents for the bipartite block-rank
argument and the directed path matrix. Its bounded search identified no
explicit exact settlement of all three polynomial-bearing analogues.
The SIAM endpoint was unavailable in that screen, which checked the
versioned arXiv copy of the cited directed paper. [Preregistration #33474](https://github.com/the-omega-institute/trureturing/issues/33474)

## Route

The path on vertices $0,1,2,3,4$ has four consecutive edges with weights
$a,b,c,d>0$. Weighted adjacency annihilates
$x=(bd,0,-ad,0,ac)$. For the normalized Laplacian, its degree vector is
$(a,a+b,b+c,c+d,d)$, and multiplying $x$ coordinatewise by the square
roots gives an eigenvector at $1$. Both vectors vanish at vertices $1$
and $3$ and have nonzero first coordinate.

The directed path $0\to1\to2$ is itself a spanning out-arborescence. Its
receiving adjacency has entries $p$ at $(1,0)$ and $q$ at $(2,1)$ and zero
elsewhere. Its receiving-degree Laplacian therefore has rows
$(0,0,0)$, $(-p,p,0)$ and $(0,-q,q)$. The last coordinate vector is a
complex right eigenvector at $q$ with zero first and second coordinates.

In each case S2 fails at every positive weighting. A certificate would
force its real evaluation to be zero throughout the positive orthant.
The product of infinite coordinate intervals determines a multivariate
polynomial by `MvPolynomial.funext_set`. Injectivity of the integer
coefficient map gives $P=0$, contradicting the certificate.

## Falsifier

A witness would fail if its support were inadmissible, the operator
entries differed from the indicated weight convention, or the proposed
nonzero vector failed the eigenvector equation at any positive weighting.
The support and entry proofs discharge these obligations. The polynomial
contradiction needs both the nonzero-polynomial premise and the
nonvanishing-to-separation implication for every positive weighting.

## Evidence

The Lean declarations `normalized_refuted`, `adjacency_refuted` and
`directed_refuted` establish the three branch negations. The designated
`result` eliminates their disjunction. The real polynomial identity
uses the actual weight subtypes. It applies uniformly in the degree and
in the mode predicate for S3.

## Triage

| Item | Result |
| --- | --- |
| Universal normalized Laplacian analogue | Refuted in Lean on the five-vertex path for every positive weighting. |
| Universal adjacency analogue | Refuted in Lean on the same path. Its eigenvalue-zero witness is covered by S2. |
| Universal receiving-degree Laplacian analogue | Refuted in Lean on the three-vertex directed path. The eigenvector identity holds for all real arc weights and the refutation uses the positive orthant. |
| Generic simple spectrum and combinatorial Laplacian Theorem 1.2 | Separate source results. The obstruction here is a support-wide failure of S2 for the three other operators. |
| Minimum-order witnesses, operator variants and a classification of supports with separating weights | Open in this dossier. |

### What the settlement shows

**Proved in Lean.** On the two path supports in the route, S2 fails at
every positive weighting. The weighted adjacency and normalized
Laplacian have nonzero right eigenvectors with interior zero
coordinates. In the receiving-degree convention, the directed
out-path is admissible and its last coordinate vector $e_2=(0,0,1)$
satisfies $Le_2=qe_2$, with $e_2(0)=e_2(1)=0$. A nonzero polynomial
cannot vanish throughout the positive orthant, so no certificate can
exclude all the failed weightings. The exact result GIDs are

- `D5/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation.normalized_refuted`
- `D5/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation.adjacency_refuted`
- `D5/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation.directed_refuted`
- `D5/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation.result` (the negation of the disjunction)

**Symbolic calculation.** The receiving-degree Laplacian on the
out-path is lower triangular, so $\det(tI-L)=t(t-p)(t-q)$.
For positive real weights $p$ and $q$ with $p\ne q$, its complex spectrum
consists of the three distinct roots $0$, $p$, and $q$, so S1 holds over
$\mathbb{C}$. If $p=q$, the root $p$ is repeated. The same $e_2$ still
violates S2 at eigenvalue $q$, since its first two coordinates vanish.

**Literature.** Generic simplicity for directed graphs with a spanning
diverging tree is the S1 result of Poignard, Pereira and Pade,
Theorem 6.6, under the receiving-degree convention. [Theorem 6.6](https://arxiv.org/pdf/1704.01677v1#page=13)

**Literature.** Pineda Montoya et al.'s Theorem 1.2 gives generic
separation for the weighted combinatorial Laplacian of a connected
simple support. Proposition 6.7 gives simple spectrum and strict
monotonicity of the Fiedler vector for that Laplacian on positively
weighted paths. Both concern the combinatorial Laplacian and apply
within their original hypotheses. [Theorem 1.2](https://arxiv.org/html/2611.21979v1#S1.Thmtheorem2) · [Proposition 6.7](https://arxiv.org/html/2611.21979v1#S6.Thmtheorem7)

**Open here.** Question 7.3 asks for the minimum degree and components
of the combinatorial Laplacian's exceptional hypersurface. Question
7.4 asks for quantitative gaps between coordinates of its unit Fiedler
vector under random weights with bounded density. Both questions remain
in the combinatorial-Laplacian setting. [Question 7.3](https://arxiv.org/html/2611.21979v1#S7.Thmtheorem3) · [Question 7.4](https://arxiv.org/html/2611.21979v1#S7.Thmtheorem4)

## ASSUMED-UNVERIFIED

The completeness and priority of the literature screen remain unverified.
The operator-specific S3 conventions are the stated analogues, and the
refutation uses S2 alone for every such choice of S3.
