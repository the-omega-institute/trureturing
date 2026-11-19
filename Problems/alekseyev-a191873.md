---
slug: alekseyev-a191873
bibkey: alekseyev2022a191873
doi: null
url: https://oeis.org/A191873
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Incidence/AlekseyevA191873ZeroDiagonal.result
---

# Alekseyev's zero-diagonal Zarankiewicz conjecture

## Problem

> Conjecture: for n >= 3, a(n) = A072567(n) = A001197(n) - 1 (per above comment). - _Max Alekseyev_, Jan 29 2022

The statement is in the COMMENTS of [OEIS A191873](https://oeis.org/A191873). Write $D(n)$ for the greatest attained rectangle-free weight with zero main diagonal, $Z(n)$ for the unrestricted greatest attained rectangle-free weight, and $K(n)$ for the least physically possible number of ones that forces a rectangle. The assertion is $D(n)=Z(n)=K(n)-1$ for every natural $n\ge 3$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Every $n\ge 3$ | `claim`, natural dimension $n$ with $3\le n$ | The same positive integer range. |
| Binary $n\times n$ matrix | `HasRectangle`, `diagonalWeights`, `forcingCounts` | Both index types are `Fin n` and the entry type is `Fin 2`. |
| Four ones forming a rectangle | `HasRectangle` | Two distinct rows, two distinct columns and four entries equal to one. The rows and columns can be nonadjacent. |
| A191873, maximum with zero main diagonal | `IsGreatest` on `diagonalWeights` | The count is the cardinality of positions equal to one. Every diagonal entry is zero. The maximum belongs to the attainable set. |
| A072567, unrestricted maximum | `SimpleGraph.zarankiewicz n n 2 2` | The proof identifies one-positions with edges and rectangles with copies of $K_{2,2}$. |
| A001197, least count that forces a rectangle | `IsLeast` on `forcingCounts` | The quantifier covers every matrix with exactly the given count. A binary entry is nonzero exactly when it is one. |
| $D(n)=Z(n)=K(n)-1$ | The last two conjuncts of `claim` | The attained witnesses $d,k$ satisfy $d=Z(n)$ and $d+1=k$. |
| Attainment and the cap $k\le n^2$ | Witness binders and membership in `forcingCounts` | These express existence of the extrema and ensure the forcing count can occur. |

## Motivation

This external conjecture is preregistered in [#23717](https://github.com/the-omega-institute/trureturing/issues/23717). The settling declaration is `D5/S3/Combinatorics/Graph/Incidence/AlekseyevA191873ZeroDiagonal.result`. Its Scribe has one `OpenProblemResolutionClaim` of kind `Proved`. The module has `generality: G`, `utility: none` and `admission_basis: open-problem-resolution (#23717; Proved)`. The source is recorded in the [Library note](../Library/FiniteGeometry/alekseyev2022a191873.md).

## Gap

The existing Zarankiewicz maximum describes unrestricted supports. The source conjecture requires an attained extremizer whose diagonal is zero. The preregistration's screen covered the three OEIS entries, D5, pinned Mathlib, arXiv metadata and selected full texts, citation indexes and related literature. It located the unrestricted Zarankiewicz formulation and elementary threshold shift. It located no prior settlement of the diagonal equality in that scope. Literature-search completeness is `ASSUMED-UNVERIFIED`.

## Route

The cyclic matrix whose row $i$ has ones in columns $i$ and $i+1\pmod n$ has weight $2n$. A rectangle would force two cyclic successors to return an index to itself, which is impossible for $n\ge 3$. A rectangle-free matrix with a full row has weight at most $n+(n-1)=2n-1$, since every other row has at most one one. Transposition gives the column bound. An unrestricted extremizer therefore has a zero in every row and column.

For a row set $S$, let $N(S)$ be the columns containing a zero in at least one of its rows. The empty and singleton cases satisfy Hall's inequality. For all rows, $N(S)$ contains every column. For any other $S$, a Hall deficiency gives at least two rows of $S$ and at least two columns outside $N(S)$, hence a forbidden rectangle of ones. Finite Hall yields a permutation of columns selecting one zero in every row. Reindexing the columns keeps the weight and puts the selected zeros on the diagonal. Trimming the support of an avoiding extremizer realizes every smaller weight, so the successor of the unrestricted maximum is the least forcing count.

## Falsifier

A dimension $n\ge 3$ where every unrestricted extremizer fails to admit a diagonal of zeros under column permutation would contradict the construction. A rectangle-free matrix with exactly $Z(n)+1$ ones, or a forcing count $k\le Z(n)$, would contradict the threshold argument.

## Evidence

The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}. The four-slot escape audit of the settling result and the published two-step rotation lemma is unfinished. [#29985](https://github.com/the-omega-institute/trureturing/issues/29985)

### Experiment

[Exact checker](https://github.com/the-omega-institute/trureturing-experiments/tree/ae532160459806cdb67f3763cf65d6722d792bb2/docs/reports/alekseyev-a191873), commit `ae532160459806cdb67f3763cf65d6722d792bb2`. Command `python3 docs/reports/alekseyev-a191873/check.py` from the experiments repository root exited 0 with `ALL_CHECKS_OK`. Script SHA-256 `ca5a634358b495bf1129ec985eb516f77218238765a1495c6bdfecb308c054c1`.

## Triage

| Item | Status | Evidence |
| --- | --- | --- |
| For every $n\ge 3$, the zero-diagonal maximum and the least physically possible forcing count exist and equal $Z(n)$ and $Z(n)+1$. | Proved | Kernel-checked by `result`. |
| For every natural dimension, a rectangle-free square binary matrix with a zero in every row and column has a permutation of zero entries. | Proved | Kernel-checked by private `zero_transversal`, used by `result`. |
| For $n\ge 3$ there is a weight-$2n$ avoiding matrix. A full row or column gives weight below $2n$, so an extremizer has neither. | Proved | Kernel-checked by private `cycle_matrix`, `full_row_bound`, `transpose_weight`, `transpose_free` and the argument in `result`. |
| Any avoiding matrix can be trimmed to any smaller nonnegative weight. Attainment and trimming give the exact forcing threshold. | Proved | Kernel-checked by private `trim_matrix`, `extremizer` and `result`. |
| At $n=1,2$, the unrestricted maxima are $1,3$ and the zero-diagonal maxima are $0,2$. At $n=3,4$, both maxima are $6,9$ and the forcing counts are $7,10$. | Computed | Exact checker in Evidence. |
| The two predicates agree on every binary matrix of dimensions $1$ through $4$. The cyclic construction and explicit zero-transversal permutation hold for each $3\le n\le 64$ tested. | Computed | Exact checker in Evidence, with $2$, $16$, $512$ and $65536$ matrices at the four exhaustive dimensions. |
| The separate symmetric-extremizer conjecture in A072567. | Open in this settlement | Column reindexing has no symmetry hypothesis or symmetry-preservation conclusion. |
| Attainability of arbitrary prescribed diagonal patterns. | Open in this settlement | `result` selects the all-zero pattern. |

### What the settlement shows

The Hall argument applies to every square dimension once each row and column has a zero, as proved by `zero_transversal`. The weight argument supplies this condition for extremizers in the full domain of `result`. The computed cases $n=1,2$ show that the lower dimension bound is sharp for the equality. The three OEIS entries therefore share the same extremal data for $n\ge3$, with the forcing count shifted by one. Knuth's broader question about prescribed diagonals and the separate symmetric-extremizer conjecture remain open in this settlement.

## ASSUMED-UNVERIFIED

Completeness of the literature screen remains unverified. The preregistration identifies unavailable full text and rate-limited search surfaces. [#23717](https://github.com/the-omega-institute/trureturing/issues/23717)
