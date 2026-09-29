---
slug: kade-2025-box-six-vertex-determinant-refutation
bibkey: kade2025boxsixvertex
doi: 10.18452/33769
url: https://arxiv.org/abs/2509.03416v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.result
---

# The box partition function of the six-vertex model

## Problem

Kade (arXiv:2509.03416v1, section 2.3) puts the six-vertex model in a square
box with arrow-reflecting walls: `2M` horizontal spectral lines, in pairs
`x_i, 1/x_i`, run from the right wall to the left wall, and `2M` vertical lines,
in pairs `y_j, 1/y_j`, run from the top wall to the bottom wall. The bulk
weights are `a = p t − 1/(p t)`, `b = t − 1/t`, `c = p − 1/p` with `t = x/y`, and
the walls carry the diagonal K-matrices
`K_L(x) = diag(b(xξ_L), b(x/(qξ_L)))`, `K_R(x) = diag(b(xξ_R), b(xq/ξ_R))`,
`K_U(y) = diag(b(yξ_U), b(yq/ξ_U))`, `K_D(y) = diag(b(yξ_D), b(y/(qξ_D)))`.
The thesis proposes

> Z_M({x_i}|{y_i}) = ∏_{i,j} (x_i/y_j − y_j/x_i) W(x_i, y_j) / ∏_{i<j} (x_j/x_i − x_i/x_j)(y_i/y_j − y_j/y_i)
> · det[ c² a(x_i y_j) a(1/(x_i y_j)) F^LU(x_i) F^DR(y_j) / ((x_j/y_i − y_i/x_j) W(x_i, y_j)) ]

with `W(x, y) = a(xy) a(1/(xy)) a(x/y) a(y/x)`,
`F^LU(x) = b(xξ_L) b(xq/ξ_U) + b(x/(qξ_L)) b(xξ_U)` and
`F^DR(y) = b(yξ_D) b(yq/ξ_R) + b(y/(qξ_D)) b(yξ_R)`, and its concluding chapter
says that the conjecture "has to be proven or discarded".

Issue #10444 fixes the readings: the absolute arrow conventions of the six
vertices and of the diagonal wall components are those of the thesis's figures
(`6Vvertices`, `KLeft_mat`, `KRight_mat`, `KUp_mat`, `KDown_mat`); rows carry
`x_1, 1/x_1, x_2, 1/x_2, …` from the top and columns `y_1, 1/y_1, …` from the
left; `q` is the crossing parameter `p`, the only value among those tried at
which the `2 × 1` box partition function is symmetric in its two horizontal
spectral parameters, as integrability requires; the parameters are complex and
the formula is asserted wherever none of its printed denominators vanishes.

## Motivation

The six-vertex model is the square-ice model of statistical mechanics, and the
box boundary conditions are an integrable way to close the lattice on all four
sides; a closed determinant for the box partition function would play the role
of the Izergin–Korepin determinant for domain-wall boundaries. The frozen
declaration
`D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.result`
shows that the proposed determinant is already wrong for the smallest box.

## Gap

Issue #10444 preregisters the statement, the readings and the counterexample
before any formalization. The arXiv API lists only v1 (2025-09-03). Web
searches for box boundary conditions of the six-vertex model found only
domain-wall and single reflecting-end results. These readings are
`not-found-in-searched-scope`; they do not establish an exhaustive worldwide
literature search or priority.

## Route

1. At `M = 1` both products in the prefactor are over a single pair or empty,
   and the determinant is the single entry, so the formula reads
   `(x/y − y/x) W(x, y) · c² a(xy) a(1/(xy)) F^LU(x) F^DR(y) / ((x/y − y/x) W(x, y))`.
2. At `p = 2`, `x = 2`, `y = 3` and all four boundary parameters `1`,
   `W(2, 3) = −4004/81` and `2/3 − 3/2 = −5/6` are nonzero and the formula
   gives `−7150`.
3. The partition function of the `1 × 1` box, the sum over the `2^12`
   configurations of arrows on the twelve edge segments of the product of the
   four wall weights and the four crossing weights, is `−400400/81` at this
   point.

## Falsifier

A reading of the arrow conventions, of the line parameters or of `q` under
which the formula holds at `M = 1` would undo the refutation. Among the sixteen
labelings of the wall states, both orientations of the crossing ratio and
`q ∈ {p, 1/p, 5/11}`, the twenty-four combinations that satisfy the thesis's
recursion at `x = y` all violate the formula at `x ≠ y`.

## Evidence

An independent exact computation over the rationals reproduces the thesis's
recursion `Z_1|_{x=y} = c² a(x²) a(x^{−2}) F^LU(x) F^DR(x)` under the figure
conventions and gives `Z_1 = −400400/81` against the formula's `−7150` at the
point above. Arranging `Z_1` as a 4 × 4 matrix over the (left, top) wall states
and the (bottom, right) wall states gives rank 4 at `(p, x, y) = (2, 2, 3)` and
`(7/5, 13/4, 5/9)`, while the formula corresponds to a rank-one matrix.

The canonical source is
`D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation.lean`. Its
public declarations are `HArrow`, `VArrow`, `a`, `b`, `c`, `vertexWeight`,
`leftWall`, `rightWall`, `topWall`, `bottomWall`, `rowParam`, `colParam`, `Z`,
`W`, `FLU`, `FDR`, `formula`, `claim`, and `result`. The frozen module state
has statement identity
`sha256:0f601c5f1faf3c63e3f6dd8c3724b23f2df5afb8d82eb4f6994c349d3664bcaf`.
The result declaration has statement identity
`sha256:7af843566fe215ba6bc10924ede01da51151820b4748bbbc50a0d9829b4ef044`.
The Freeze event is
`sha256:bf8503b8cc172add2c1e9568e142ee8c4395c144d5c7bb57b047f14dc24f5a3e`
and has no project-level frozen prerequisites. The proof uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

`theorem`; resolution `refuted`, for the conjecture as read in #10444. The
public theorem has `proof_shape: content`: the kernel evaluation of the box
partition function over the rationals and its transfer to the complex numbers
through the rational cast are new propositions on the live path of the proof.
`admission_basis: open-problem-resolution` under preregistration issue #10444;
utility `kind=certified-instance; basis=refutes` with typed `claim` and
`result`. There is no atom and no digestion coverage edge.

## ASSUMED-UNVERIFIED

The arrow conventions of the wall components are read from the thesis's
figures; the thesis does not state `q` in section 2.3, and `q = p` rests on the
symmetry check above. The bounded literature check does not establish
exhaustive worldwide novelty, priority, or the absence of an independent
refutation.
