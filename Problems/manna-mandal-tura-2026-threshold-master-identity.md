---
slug: manna-mandal-tura-2026-threshold-master-identity
bibkey: mannamandaltura2026thresholdmasteridentity
doi: null
url: https://arxiv.org/pdf/2610.22838v1#page=18
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraDegreeMatrixRefutation.not_degreeMatrix_master_identity_criterion
---

# The degree matrix refutes the threshold master-identity criterion

## Problem

Pallabi Manna, Santanu Mandal and Fernando C. Tura, *The Spectral Theory of
Threshold Graphs: A Survey*, arXiv:2610.22838v1, Section 13.4, printed p. 18,
state Conjecture 13.9.

> **Conjecture 13.9 (Master-identity criterion).** A graph matrix $M(G)$ is both always-integral and spectrally determining for threshold graphs if and only if $M(G)$ is an affine function of $L(G)$ and $J$ alone (i.e. $M(G)=\alpha L(G)+\beta J+\gamma I$ for scalars $\alpha,\beta,\gamma$, as is the case for $L$ itself and, via Proposition 7.3, for $D^L$).

[Library note](../Library/QuadraticForms/mannamandaltura2026thresholdmasteridentity.md) · [Issue #34363](https://github.com/the-omega-institute/trureturing/issues/34363)

| Source clause | Lean counterpart |
| --- | --- |
| Finite connected threshold graphs | Arbitrary base-universe finite vertex types with `IsThreshold G` and `G.Connected`. Section 1's singleton and isolated or dominating additions are transported by graph isomorphism. |
| Graph matrix | Specialize to the ordinary real diagonal degree matrix `G.degMatrix ℝ`, named $\operatorname{Deg}(G)$ in Section 2. |
| Always integral | Every member of `degreeSpectrum G` is the real image of an integer, for every graph in the class. |
| Spectrally determining | Equality of the multiset of real characteristic roots implies isomorphism for any pair of graphs in the class. The vertex types may differ. |
| Affine form | For each graph, there exist real $\alpha,\beta,\gamma$ with $\operatorname{Deg}(G)=\alpha L(G)+\beta J+\gamma I$. Here $L=\operatorname{Deg}-A$, $J$ is all ones and $I$ is the identity. |
| Outcome | The theorem `not_degreeMatrix_master_identity_criterion` has literal type `Not claim`, where `claim : Prop` is the closed expanded biconditional at this matrix specialization. |

## Motivation

Section 13.4 compares the integral spectra of $L$ and $D^L$ with the arithmetic
conditions for the other surveyed matrices. The conjecture phrases the
proposed explanation as a criterion for a graph matrix $M(G)$. The diagonal
degree matrix is already part of the paper's notation in Section 2.

## Gap

The necessity direction says that any matrix family with both properties
has the affine form. A counterexample must establish both properties over
the full class of connected threshold graphs and exclude the affine form
on a member of that class.

## Route

The characteristic polynomial of the real degree matrix is
$\prod_{v\in V(G)} (X-\deg_G(v))$. Each vertex contributes one root to the
multiset. The roots are integral, and injectivity of the natural-to-real
cast transfers equality of root multisets to equality of degree multisets.

The classical reconstruction of Chvátal and Hammer recovers the last
creation choice from whether the multiset contains zero. Its cardinality
gives the order. Delete the contribution of the newest vertex, then subtract
one from each remaining degree after a dominating addition. Induction works
for the disconnected intermediates and transfers the resulting isomorphism
to the original vertex types.

For the three-vertex path, first add an isolated vertex to the singleton and
then add a dominating vertex. Label the center $0$ and the two leaves $1,2$.
The $(1,2)$ entry forces $\beta=0$. The $(0,1)$ entry forces $\alpha=0$.
The $(0,0)$ and $(1,1)$ entries would then require $\gamma=2$ and
$\gamma=1$. This contradiction applies to coefficients chosen for this
particular graph.

The primary reference for the classical reconstruction is Václav Chvátal
and Peter L. Hammer, *Aggregation of inequalities in integer programming*,
Annals of Discrete Mathematics **1** (1977), 145–162, source reference [21].

## Falsifier

Equality of degree multisets for nonisomorphic threshold graphs would defeat
the reconstruction step. A coefficient triple satisfying the four specified
entries on $P_3$ would defeat the obstruction. The Lean proof discharges both
obligations through the characteristic-root bridge, reconstruction and
entry equations.

## Evidence

The result is in
`D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraDegreeMatrixRefutation.lean`.
Its proof uses the pinned Mathlib interface for the real matrices,
characteristic roots and simple graph isomorphisms. The private reconstruction
and spectral lemmas allow unrelated finite vertex types at independent
universe levels. The named biconditional is closed over `Type`.
The result is the public theorem and the designated §3.9 refutation result.
The $P_3$ instance serves the refutation.

## Triage

### What the settlement shows

| Item | Status and evidence |
| --- | --- |
| The real degree spectrum carries multiplicities and is integral on every finite connected threshold graph | Proved in Lean by factoring the characteristic polynomial and identifying its multiset of roots with the real-cast degree multiset. |
| That spectrum determines every finite connected threshold graph up to isomorphism | Proved in Lean by recovering the creation sequence from the degree multiset. |
| A connected threshold $P_3$ excludes the affine form even for coefficients chosen for $P_3$ | Proved in Lean by the four entry equations. |
| Conjecture 13.9 | Refuted by the Lean theorem for $M(G)=\operatorname{Deg}(G)$. |
| Open Problem 15.6, printed p. 21 | Separate open question in the dossier. It asks for a structural predictor of spectral determination. |

## ASSUMED-UNVERIFIED

The quoted statement, connectedness convention and attribution are tied to
the supplied v1 text. The completeness of the wider literature search is
unverified in this staging record.
