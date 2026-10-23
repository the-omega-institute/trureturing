---
slug: wei-yang-2024-associated-mersenne-cube-polynomial
bibkey: wei2024associatedmersenne
doi: 10.1007/s00373-025-02936-3
url: https://arxiv.org/abs/2407.08237v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Hamming/AssociatedMersenneCubePolynomial.result
---

# Cube polynomial of the associated Mersenne graphs

## Problem

Wei and Yang, *Associated Mersenne graphs*, arXiv:2407.08237v1, Section 6,
Question 6.3 asks:

> What is cube polynomial for Associated Mersenne graph $\mathcal{M}_n$?

The associated Mersenne graph has the circular run constrained Boolean words as
vertices, with Hamming distance one as adjacency. Its cube polynomial is
$C_n(x)=\sum_k c_n(k)x^k$, where $c_n(k)$ counts induced copies of $Q_k$.

## Motivation

The question is preregistered in
[#14961](https://github.com/the-omega-institute/trureturing/issues/14961).
The settling declaration is
`D5/S3/Combinatorics/Hamming/AssociatedMersenneCubePolynomial.result`,
with an `OpenProblemResolutionClaim` recorded as Proved. The supporting
declaration is
`D5/S3/Combinatorics/Hamming/InducedSubcubes.induced_cube_iff`.

## Gap

Let
$$
D=1-z-z^2-xz^3-x(1+x)z^5,\qquad
N=z+2z^2+3xz^3+5x(1+x)z^5.
$$
With $S(z)=\sum_{n\ge1}C_n(x)z^n$, AMC-1 is
$$
S(z)(1-z^2)D=N(1-z^2)-2z^2D.
$$
The Lean definitions `amGraph`, `cubeCount`, `cubePoly`, `x`, `z`,
`amcDen`, `amcNum`, and `cubeSeries` use the source conventions and state
this identity as `claim`; `result` proves it for every natural length.

## Route

1. Every induced Boolean-hypercube copy is a unique coordinate down-cube
   `downCube v S`, with $S\subseteq\operatorname{support}(v)$. The
   construction and uniqueness are supplied by `cube_map_image`,
   `induced_cube_iff`, and `downCube_unique`.
2. For an admissible top word, exactly the run endpoints may be deleted while
   retaining admissibility. Thus its contribution is a power of $1+x$
   indexed by the endpoint set.
3. Circular block decomposition and the marked double count reduce the
   weighted cube enumeration to the transfer resolvent. The settling module
   reuses the frozen Associated Mersenne word and transfer owners, including
   the declarations on the endpoint and transfer dependency paths.
4. Resolvent algebra clears the denominator and gives AMC-1, including the
   source conventions at the small lengths.

## Falsifier

A counterexample is an admissible length $n$, an induced cube count, or a
formal-power-series coefficient that violates AMC-1. A publication that
settles Question 6.3 within the preregistered literature boundary would also
remove the open-problem status.

## Evidence

The experiment entry
[docs/reports/wei-yang-2024-associated-mersenne-cube-polynomial/check.py](https://github.com/the-omega-institute/trureturing-experiments/tree/1cc346255c34dbb92065118f43b796218b0a41ba/docs/reports/wei-yang-2024-associated-mersenne-cube-polynomial)
is pinned to commit
`1cc346255c34dbb92065118f43b796218b0a41ba`. It was run as `python3 check.py 13`,
exited 0, and ended with `ALL_OK`. The script SHA-256 is
`f279680430f166101c32e9a976dc0dc9141bb3cb04587f1bc9dbb27efc5c6730`.
For lengths 1 through 13 it independently enumerates admissible words,
vertices, edges and induced 4-cycles and matches every coefficient of AMC-1.

The axiom closure of every public declaration is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
No Reg file is shipped. The four-slot escape audit for `result`,
`cube_map_image`, `induced_cube_iff`, and the newly public owner declarations
remains unfinished under
[#15283](https://github.com/the-omega-institute/trureturing/issues/15283);
the issue inventory includes `erase_empty`, `top_mem_downCube`, the other new
public supporting theorem, and every retained owner publication.

## Triage

| Item | Status | Evidence and boundary |
| --- | --- | --- |
| Induced-cube characterization, coordinate directions, uniqueness, and converse | proved | `InducedSubcubes.cube_map_image`, `downCube_unique`, and `induced_cube_iff`; the general Boolean-hypercube statement is frozen. |
| Endpoint deletion and endpoint-weight cube enumeration | proved | The settling module proves the endpoint-removal and weighted count steps on the live path to `result`. |
| Marked double count, block series, transfer resolvent, and cleared-denominator identity | proved | The settling proof reuses the frozen Associated Mersenne word and transfer owners and proves `result : claim`. |
| Vertex specialization $x=0$ | proved | Paper argument from `cubePoly_endpoint_sum`: evaluating each $(1+x)^{m}$ at zero gives one, so $C_n(0)=\#\mathbf M_n$. The coefficient identity and endpoint-weight formula are kernel checked; evaluation is an algebraic consequence. |
| Edge specialization, coefficient of $x$ | computed | The pinned `python3 check.py 13` calculation matches the independent edge count at every length 1 through 13 (exit 0, script SHA-256 given above). The same neighbour relation underlies #14818; its degree sum counts each undirected edge twice. A uniform Lean comparison with the degree series is not delivered. |
| Finite examples at lengths 5, 8 and 13 | computed | The pinned experiment checks all coefficients through length 13. |
| Question 6.1 (Hamiltonicity) | open | No Hamilton cycle is asserted. |
| Distance cube polynomial | open | No distance-refined counting identity is delivered. |
| Asymptotics of the largest induced cube dimension | open | No uniform asymptotic estimate is delivered. |

## ASSUMED-UNVERIFIED

The inspected arXiv source states Question 6.3 as open. The journal full text
and worldwide priority are outside the kernel proof and remain
ASSUMED-UNVERIFIED. Numerical agreement is finite evidence and does not
replace the universal Lean theorem.
