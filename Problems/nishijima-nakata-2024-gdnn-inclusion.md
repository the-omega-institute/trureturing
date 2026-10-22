---
slug: nishijima-nakata-2024-gdnn-inclusion
bibkey: nishijimanakata2024generalizations
doi: 10.15807/jorsj.67.84
triage: theorem
motivation_gids:
  - D5/S3/QuadraticForms/ConicGDNN/Result.result
url: https://arxiv.org/abs/2204.12119
---

# Generalized doubly nonnegative cone inclusion

## Problem

The cited article, arXiv:2204.12119v4, Section 5.1, Conjecture 5.1, asks for
the inclusion of the NN-type generalized doubly nonnegative cone in the
BD-type cone for products of a nonnegative orthant and second-order cones.
The statement reads verbatim: “If K is a direct product of a nonnegative
orthant and second-order cones, DNN^NN(K) ⊆ DNN^BD(K) holds.” The article
notes that the case of a single second-order cone follows from its
Proposition 4.12 and that the general inclusion relationship is unknown.

### Formal reading

Let $p,r\ge0$ and $k_j\ge1$ for $1\le j\le r$, and put

$$K=\mathbb R_+^p\times\prod_{j=1}^r
\{(t,z)\in\mathbb R\times\mathbb R^{k_j}:\|z\|_2\le t\}.$$

Let $q$ square each orthant coordinate and send each Lorentz block $(t,z)$
to $(t^2+\|z\|_2^2,2tz)$. Write $\Sigma_{n,4}$ for the convex hull of
squares of homogeneous quadratic polynomials. With the standard coordinate
pairing and $n=p+\sum_j(k_j+1)$, define

$$\mathcal K_{\mathrm{NN},0}(K)
=\{A\in\mathbb S^n:q(x)^\mathsf{T}Aq(x)\in\Sigma_{n,4}\}.$$

Every $X\in\mathbb S^n$ satisfying
$\operatorname{tr}(XA)\ge0$ for every $A\in\mathcal K_{\mathrm{NN},0}(K)$
is positive semidefinite and satisfies $Xs\in K$ for every extreme ray
generator $s$ of $K^*$. Thus $\mathrm{DNN}^{\mathrm{NN}}(K)\subseteq
\mathrm{DNN}^{\mathrm{BD}}(K)$.

| Source object | Lean counterpart | Correspondence |
| --- | --- | --- |
| Orthant and Lorentz product | `Defs.Idx`, `Defs.cone` | Orthant coordinates and a time coordinate plus $k_j$ spatial coordinates per block. |
| Jordan square | `Defs.jsq` | Homogeneous quadratic polynomials with the displayed block formula. |
| Quartic SOS cone | `Defs.sos4` | Real convex hull of homogeneous quadratic squares. |
| Zeroth approximation | `Defs.quartic`, `Defs.knn0` | Symmetric matrices with SOS quartic pullback. |
| NN-type dual | `Defs.dnnNN` | Symmetric trace dual of exactly this approximation. |
| BD-type cone | `Defs.dualCone`, `Defs.extremeRays`, `Defs.dnnBD` | Positive semidefiniteness and preservation of every dual extreme ray generator. |
| All product dimensions | `Defs.claim`, `Result.result` | All $p,r$ and all positive spatial dimensions; no factor is omitted. |

## Motivation

The settling GID is `D5/S3/QuadraticForms/ConicGDNN/Result.result`.
The source note is `D5/L/QuadraticForms/nishijimanakata2024generalizations`.
The result compares the two specified approximations for the full
orthant and Lorentz product family.

## Gap

Status: **Proved** for the stated inclusion. Preservation holds for the
entire cone, and the intermediate theorems also allow $k_j=0$. Products
with positive semidefinite cone factors and the strictness question in
Triage are outside the formal claim.

## Route

Every rank-one symmetric matrix $ww^\mathsf{T}$ supplies the single-square
quartic $(w\cdot q(x))^2$, so trace positivity implies $X\succeq0$.
For $u,v\in K=K^*$, the quadratic polynomials $h_u=u\cdot q$ and
$h_v=v\cdot q$ have homogeneous linear-square certificates. Their product
is a sum of squares of homogeneous quadratics, so
$(uv^\mathsf{T}+vu^\mathsf{T})/2$ belongs to $\mathcal K_{\mathrm{NN},0}(K)$.
Trace positivity gives $u^\mathsf{T}Xv\ge0$. Self-duality then yields
$Xv\in K$ for every $v\in K$.

The structural argument needs only a finite-dimensional self-dual closed
cone and a homogeneous quadratic map $q$ taking values in it. For any
$u$ in that cone, $u\cdot q(x)\ge0$ for all $x$. A nonnegative real
homogeneous quadratic polynomial is a sum of squares of linear forms:
diagonalize its positive semidefinite symmetric coefficient matrix and
absorb the square roots of its nonnegative eigenvalues. Multiplication
gives the quadratic-square certificate above; no further Jordan identity
is used in the rank-one or trace-duality steps. The Lean development
specializes this argument to the stated products and constructs the
linear-square certificates explicitly; it does not state an abstract
theorem for arbitrary cones or quadratic maps.

## Falsifier

A symmetric matrix in the specified trace dual that is not positive
semidefinite, or that sends some dual extreme ray generator outside $K$,
would contradict `Result.result`. A cone vector $v$ with $Xv\notin K$
would already contradict `Duality.mulVec_mem_cone`.

## Evidence

`D5/S3/QuadraticForms/ConicGDNN/Result.result` proves exactly `Defs.claim`.
The principal dependencies are `Lorentz.dualCone_cone`,
`Lorentz.pullback_eq_sum_sq`, `Duality.quartic_rankOne`,
`Duality.posSemidef_of_mem_dnnNN`, `Duality.sym_mem_knn0`, and
`Duality.mulVec_mem_cone`. The accepted axiom closure of the result is
contained in `{propext, Classical.choice, Quot.sound}`.

The source statement and definitions were read in arXiv:2204.12119v4
(Section 2, Theorem 3.5, Definitions 3.6 and 3.7, Conjecture 5.1). In the
bounded literature screen, the later articles 2402.12964, 2502.04006, 2510.27160,
2602.23725 and 2608.27062 contain no reported settlement in that screen.
This is not an exhaustive citation-index or priority certification.

## Triage

- **PROVED.** The stronger conclusion $XK\subseteq K$ holds
  for every cone vector, beyond extreme ray generators of $K^*$, by
  `Duality.mulVec_mem_cone`. No positive spatial-dimension hypothesis is
  needed for this stronger conclusion.
- **PROVED in prose.** The mechanism uses only that the
  Jordan square is a homogeneous quadratic map into a self-dual closed
  cone, by the nonnegative-quadratic SOS argument in Route. The abstract
  generalization is a mathematical derivation; the Lean theorem concerns
  the pinned orthant and Lorentz products.
- **PROVED in prose.** The same inclusion for products with
  positive semidefinite cone factors, as in the article's Section 4.2,
  admits the same argument: the matrix-square map is homogeneous
  quadratic and takes values in the self-dual positive semidefinite
  cone under the trace pairing. Its coordinate model and SOS certificate
  are not formalized in this development.
- **PROVED in prose.** When every Lorentz block has $k_j=1$, each
  block is a rotated copy of $\mathbb R_+^2$: the orthogonal change
  $(t,z)\mapsto((t+z)/\sqrt2,(t-z)/\sqrt2)$ turns the Jordan square into
  coordinatewise squaring with positive weights, and the two cones coincide
  with the ordinary doubly nonnegative cone.
- **OPEN.** Which products, with at least one block of spatial dimension
  $k_j\ge2$, give a strict inclusion.

## ASSUMED-UNVERIFIED

Literature completeness, priority and exhaustive coverage
of subsequent papers are unverified. The abstract generalization and the
positive semidefinite factor extension have no general Lean theorem in
this development.
