---
slug: lillo-rosas-2026-priority-lattice-principal-ideals
bibkey: lillo2026prioritylattice
doi: 10.48550/arXiv.2603.28905
url: https://arxiv.org/abs/2603.28905v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/PriorityLattice/PrincipalIdeals.result
---

# Principal ideals of the priority lattice

## Problem

Adrián Lillo and Mercedes Rosas, *The Priority Lattice*, arXiv:2603.28905v1, Section 6, item 3, p. 24, ask how many principal ideals are isomorphic to $\Pi(m)$, initially with $1\le m\le n$ and then with $m\le n$. They give $2,4,8,14,22,32,44,\ldots$ and conjecture OEIS A014206, displaying $n^2+n+2$.

The [Library note](../Library/GraphInvariants/lillo2026prioritylattice.md) quotes their interval-component, increasing-tree and edge-inclusion definitions. The binding claim is [#14857, comment 6090966050](https://github.com/the-omega-institute/trureturing/issues/14857#issuecomment-6090966050): natural subtraction is ordered as `n ^ 2 + 2 - 2 * n`, and both counts include the principal ideal of the greatest element.

## Motivation

`D5/S3/Combinatorics/PriorityLattice/PrincipalIdeals.result` proves `claimGamma`: for every natural $n\ge1$,

$$\gamma_n=n^2-n+2,\qquad\gamma_n^+=n^2+2-2n.$$

`gamma` counts all `x : Pi n` for which `Set.Iic x` is order-isomorphic to `Pi m` for some natural $m\le n$. `gammaPos` additionally requires $1\le m$. These literal cardinalities use the public parent-function priority forest, edge-inclusion order and adjoined greatest element. The formulas do not assert the uncorrected natural-subtraction expression `(n ^ 2 - 2 * n) + 2`, which disagrees at $n=1$.

## Gap

The source leaves the interval count and OEIS interpretation open. The bounded source, OEIS, MathDB and repository searches in #14857 found no prior settlement; absence of every prior publication is `ASSUMED-UNVERIFIED`. The source's data, printed quadratic and strict-proper-ideal wording have different readings, stated separately below.

## Route

An ideal below a forest with $k$ edges has rank $k$, hence its target parameter is $m=k-1$. `lower_covers_card_le` bounds the number of lower covers by $k$. Comparing with the $(k-1)!$ coatoms of $\Pi(k-1)$ gives $m\le2$.

`idealCodeOrderIso` compresses the ideal to the poset of closed subsets of its ordered support. `forest_ideal_shape_iff` classifies the qualifying forests: one edge, or two or three edges with the `OneLong` property. There are $n$ single-edge forests, $n-1$ three-vertex stars, and $(n-1)(n-2)$ rank-three shapes. The last family comprises a three-vertex star disjoint from a consecutive edge, in either order, and the two four-vertex trees with relative parent lists $(0,0,2)$ and $(0,1,1)$.

The top element contributes one more ideal. The formulas follow from this disjoint enumeration; removing the $n$ ideals isomorphic to $\Pi(0)$ gives the positive-parameter count. `gamma_transfer` and `gammaPos_transfer` connect the internal counts to the public definitions.

## Falsifier

A qualifying forest of rank greater than three, or a low-rank forest outside the compressed-code classification with the required order isomorphism, would contradict the classification. An exact cardinality mismatch would contradict the enumeration. The tests distinguish $m\ge0$, $m\ge1$, and exclusion of the greatest element.

## Evidence

The settling declaration and its supporting modules are Lean kernel checked. Their public axiom closures are contained in `{propext, Classical.choice, Quot.sound}`. The Scribe settling node has one `OpenProblemResolutionClaim`, `ResolutionKind.Proved`, for this dossier.

The four-slot escape audit is unfinished: [#14955](https://github.com/the-omega-institute/trureturing/issues/14955) records the targets, delivered-head DTR readings and missing evidence. Utility is `none`; this proof result has no refutation exemption.

## Triage

### What the settlement shows

- Proved, by `lower_covers_card_le`, `ideal_iso_rank` and `forest_ideal_index_le_two`: a $k$-edge forest has at most $k$ lower covers, while $\Pi(k-1)$ has $(k-1)!$ coatoms; thus $m\le2$.
- Proved, by `forest_ideal_shape_iff`, `single_edges_card`, `long_two_card` and `long_three_card`: the qualifying shapes number $n$, $n-1$ and $(n-1)(n-2)$ respectively. The rank-three count includes the two four-vertex shapes and the disjoint star-and-edge shapes; truncated factors cover the small sizes.
- Proved, by `gamma_formula`, `gammaPos_formula` and `result`: $\gamma_n=n^2-n+2$ and $\gamma_n^+=n^2+2-2n$ for every $n\ge1$. The latter is the literal positive-parameter reading, with natural subtraction evaluated after the addition.
- Proved by the displayed formulas and paper arithmetic: $n^2+n+2$ exceeds $n^2-n+2$ by $2n>0$ for every $n\ge1$. The data are A014206 shifted by one, rather than the printed quadratic at the same index.

The decisive mechanism is the lower-cover obstruction, compressed-code classification and disjoint shape enumeration. No additional hypothesis restricts the increasing interval forests. These formulas add the interval enumeration; the other final-section questions remain open.

### Principal filters

- Proved, by `filter_iso_singleton_prefix`, `filter_iso_rank` and `filter_atoms_card`: rank forces $m=c-1$, and the atom count is $\sum_{i<c}s_i$; exactly the singleton-prefix forests qualify. Proved, by `principalFilterContraction`: contracting the last tree gives their order isomorphism.
- Proved, by `increasing_tree_card`, `theta_sum` and `result`: the count is $\sum_{k=0}^{n}k!$, the left factorial $!(n+1)$, uniformly for $n\ge1$. The internal `theta_sum` also treats $n=0$.
- Proved as a paper arithmetic comparison: the displayed $\sum_{i=0}^{n-1}k!$ has a mismatched variable and bound; interpreting it as $\sum_{k=0}^{n-1}k!$ omits the strictly positive term $n!$. The displayed data instead agree with $\sum_{k=0}^{n}k!$. The source's OEIS interpretation is therefore settled with its data-compatible indexing.

### Strict proper-ideal reading

Proved in scratch, not delivered as a new theorem: the source says “We do not consider $\Pi(n)$ to be a principal ideal” (Section 3, p. 7; source line 191). The greatest element qualifies in both binding counts for $n\ge1$. Its ideal is unique, so removing it decreases each count by exactly one and gives $n^2-n+1$ and $n^2+1-2n$. The probe's `PriorityLattice.proper_ideal_formulas` kernel-checks this subtraction, including $n=1$, where the counts are $1$ and $0$. This conclusion also follows directly as a paper cardinality argument from `result` and the unique top ideal; it is not part of the delivered module.

The delivered convention follows the binding cardinality definitions and source data, which include the top element. It does not silently impose the strict-proper-ideal convention.

### Computed interval readings

Computed: the [experiment entry](https://github.com/the-omega-institute/trureturing-experiments/tree/b22108dae35f49ed44629a59f3e98d2440d7c82a/docs/reports/lillo-rosas-2026-priority-lattice-intervals/) contains the independent Hasse-diagram isomorphism check. Command: `python3 docs/reports/lillo-rosas-2026-priority-lattice-intervals/check.py 6`, with `networkx` installed; exit code 0. Script SHA-256: `b71ca8894f15984e5eca4712f947556f024d3d2ddfc7ebe68142090fc7f562ec`. The tested scope is every principal filter and ideal of $\Pi(n)$ for $1\le n\le6$, against $\Pi(m)$ for $0\le m\le n$.

| $n$ | $\lvert\Pi(n)\rvert$ | $\theta_n$ | $\gamma_n$ | $\gamma_n^+$ |
| --- | --- | --- | --- | --- |
| 1 | 3 | 2 | 2 | 1 |
| 2 | 6 | 4 | 4 | 2 |
| 3 | 16 | 10 | 8 | 5 |
| 4 | 55 | 34 | 14 | 10 |
| 5 | 236 | 154 | 22 | 17 |
| 6 | 1238 | 874 | 32 | 26 |

### Other questions

Open: whether $\Pi(n)$ is sublattice dismantlable for every $n$; the authors report checks for $n\le5$, not a uniform proof. Open: its flag quasi-symmetric function. Open: a map from maximal chains to minimal cycle factorizations. Open: which intervals $[x,y]$ with $x\ne\hat0$ and $y\ne\hat1$ are isomorphic to some $\Pi(m)$. The interval counts do not settle these questions or change the hypotheses of the source's other results.

## ASSUMED-UNVERIFIED

The bounded literature search does not certify absence of every previous publication. Uniform conclusions are about the binding definitions; the exact enumerations through $n=6$ are finite computed corroboration. Classifying proper-ended intervals and the source's other final-section questions is open.
