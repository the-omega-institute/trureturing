---
bibkey: cruzortegamenendezconde2023fiedlerresistance
authors: A. Cruz Ortega; F. Menéndez-Conde
year: 2023
title: Conectividad algebraica máxima para caminos con resistencia total fija
doi: 10.15381/pesquimat.v26i2.24218
url: https://arxiv.org/abs/2306.08187v1
claim: "Section 5 conjectures that the maximum algebraic connectivity at fixed total effective resistance is attained at automorphism-invariant edge weights."
strata_touched:
  - D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.15381/pesquimat.v26i2.24218

Source: https://arxiv.org/abs/2306.08187v1

Journal: *Pesquimat* 26(2) (2023), 11–24. The arXiv version is the English
text, *Maximal algebraic connectivity for paths with fixed total resistance*.
Page numbers below refer to that version.

## Definitions

Section 2, page 3, states: “The laplacian of a weighted graph $(G;\omega)$ is
the operator on $\ell(V)$ given by”

$$
(L_{G,\omega}x)_i=\sum_{\{v_i,v_j\}\in E}\omega_{i,j}(x_i-x_j).
$$

Section 3, page 4, states: “By the Courant-Fischer-Weyl theorem, the algebraic
connectivity of a weighted graph is”

$$
\lambda_2(G;\omega)=\min_{x\perp J}
\frac{\langle L_{G,\omega}x,x\rangle}{\langle x,x\rangle}.
$$

The quotient requires $x\ne0$; `lambda2` excludes zero explicitly and takes
the infimum of the Rayleigh values.

Section 4, page 5, describes the harmonic extension by zero Laplacian outside
the boundary set. Its effective resistance definition states: “Given two
vertices $v_i\neq v_j$ of the weighted graph $(G;\omega)$, let
$U=\{v_i,v_j\}$. For $h\in\ell(V)$ the harmonic extension of the function
in $\ell(U)$ given by $h_i=1$, $h_j=0$, define”

$$
r(v_i,v_j)=\langle L_\omega h,h\rangle^{-1}=(L_\omega h)_i^{-1}.
$$

The same page states: “The total effective resistance of $(G,\omega)$ is”

$$
R(G;\omega)=\sum_{\{v_i,v_j\}}r(v_i,v_j).
$$

The sum includes every unordered pair of distinct vertices, including
nonadjacent pairs. The unweighted reference is $R(G)=R(G;1)$.

## Section 5 conjecture

On page 7, equation (3) defines

$$
\breve a(G)=\max\{\lambda_2(G;\omega)\mid R(G;\omega)=R(G)\}.
$$

The following sentence is verbatim:

> We conjecture that – in the same fashion of what happens with the absolute algebraic connectivity – the maximal value of (3) is attained always for weight distributions that are invariant under automorphisms of the graph.

The Lean `claim` quantifies over connected simple graphs on `Fin n`, with
$n\ge3$, and positive edge weights. It asserts an invariant feasible
assignment whose algebraic connectivity dominates every feasible assignment.
It does not assume existence of a maximum separately.

## Path solutions and scope

The source's Theorem 5.1 proves that equal weights optimize $P_3$, with
algebraic connectivity $1$ at the unweighted resistance. Its Theorem 5.5
gives the $P_4$ optimum $2-4\sqrt3/5$ at total resistance $10$, attained with
equal conductances on the two end edges. These path results are source
results, not statements proved by the settling Lean module.

The module refutes the universal conjecture on $K_{2,3}$. Conductances
$32/23$ on the edges from one hub and $16/23$ from the other give
$R=23/3=R(K_{2,3})$ and $\lambda_2=48/23>2$. Automorphism invariance and
feasibility force conductance one on every edge and hence $\lambda_2=2$.
The refutation leaves the source's separately proved path results intact.

## Encoding conventions

`harmonicExt` chooses a harmonic vector when one exists and returns zero
otherwise; `effRes` is zero on the diagonal. For the positive $K_{2,3}$
assignments used in the proof, harmonic existence and uniqueness hold for
every pair contributing to `totalRes`. `pairRes` uses the `min`/`max`
orientation of each unordered pair. Positivity and automorphism invariance
constrain edges only; the Laplacian, algebraic connectivity and total
resistance depend only on edge values. These conventions make the source's
definitions total without changing the positive connected witness.
