---
slug: lillo-rosas-2026-priority-lattice-principal-filters
bibkey: lillo2026prioritylattice
doi: 10.48550/arXiv.2603.28905
url: https://arxiv.org/abs/2603.28905v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/PriorityLattice/PrincipalFilters.result
---

# Principal filters of the priority lattice

## Problem

Adrián Lillo and Mercedes Rosas, *The Priority Lattice*, arXiv:2603.28905v1, Section 6, item 3, pp. 24–25, ask for the number of principal filters $[P,\hat1]$ isomorphic to a priority lattice $\Pi(m)$ with $m\le n$. Their data $2,4,10,34,154,874$ suggest the left factorials, OEIS A003422. The displayed formula is $\theta_n=\sum_{i=0}^{n-1}k!$, whose summation variable and bound do not match the data.

The question and its source conventions are [preregistered in #14857](https://github.com/the-omega-institute/trureturing/issues/14857). The [Library note](../Library/GraphInvariants/lillo2026prioritylattice.md) quotes the source definitions: increasing rooted trees with consecutive label sets, ordered by their root labels; edge inclusion; and an adjoined greatest element.

## Motivation

`D5/S3/Combinatorics/PriorityLattice/PrincipalFilters.result` proves `claimTheta`: for every natural $n\ge1$,

$$\theta_n=\sum_{k=0}^{n}k!=!(n+1).$$

`PriorityForest` uses the binding parent-function construction, with `none` at each root and a smaller parent at each other vertex; `Relation.EqvGen` defines connectivity and the interval condition. `Pi n` is `WithTop (PriorityForest n)`. `theta n` is the cardinality of all qualifying `Set.Ici` carriers, with an existential natural $m\le n$. The extra top element is also tested; `top_filter_not_iso` rules it out.

## Gap

The source poses the OEIS interpretation as an open question. The bounded source, OEIS, MathDB and repository searches recorded in #14857 found no earlier settlement. Absence of every prior publication is `ASSUMED-UNVERIFIED`.

## Route

Let a forest have $c$ components of sizes $s_1,\ldots,s_c$. Rank preservation forces $m=c-1$. Its upper covers number $\sum_{i<c}s_i$, whereas $\Pi(c-1)$ has $c-1$ atoms. Every $s_i$ is positive, so all components before the last must be singletons. Conversely, contraction of the last increasing tree gives the order isomorphism.

`filter_iso_singleton_prefix` establishes this characterization and `principalFilterContraction` constructs its isomorphism. `increasing_tree_card` counts increasing trees on $L$ consecutive labels by $(L-1)!$. Enumerating the possible last-root positions gives the sum from $0$ through $n$. `coreOrderIso` connects the interval-forest carrier used in the construction to the literal public priority-forest definition, and `result` transfers the count to `theta`.

## Falsifier

A priority forest without a singleton prefix whose upper interval is isomorphic to some $\Pi(m)$ would contradict the rank-and-atom characterization. A singleton-prefix forest with no contraction isomorphism, or a mismatch in an exact enumeration, would contradict the construction or count. These are checks of the specified objects and order, including $m=0$.

## Evidence

The settling declaration and its supporting modules are Lean kernel checked. Their public axiom closures are contained in `{propext, Classical.choice, Quot.sound}`. The Scribe settling node carries one `OpenProblemResolutionClaim` with `ResolutionKind.Proved` for this dossier.

The four-slot escape audit is unfinished: [#14955](https://github.com/the-omega-institute/trureturing/issues/14955) records the targets, delivered-head DTR readings and missing evidence. Utility is `none`; the proof result has no refutation exemption.

## Triage

### What the settlement shows

- Proved, by `filter_iso_singleton_prefix`, `filter_iso_rank` and `filter_atoms_card`: rank forces $m=c-1$, and the atom count is $\sum_{i<c}s_i$; exactly the singleton-prefix forests qualify. Proved, by `principalFilterContraction`: contracting the last tree gives their order isomorphism.
- Proved, by `increasing_tree_card`, `theta_sum` and `result`: the count is $\sum_{k=0}^{n}k!$, the left factorial $!(n+1)$, uniformly for $n\ge1$. The internal `theta_sum` also treats $n=0$.
- Proved as a paper arithmetic comparison: the displayed $\sum_{i=0}^{n-1}k!$ has a mismatched variable and bound; interpreting it as $\sum_{k=0}^{n-1}k!$ omits the strictly positive term $n!$. The displayed data instead agree with $\sum_{k=0}^{n}k!$. The source's OEIS interpretation is therefore settled with its data-compatible indexing.

The decisive mechanism is rank-and-atom rigidity followed by an explicit contraction. It applies to every size, without replacing the source's interval-component condition by a certificate predicate.

### Principal ideals

- Proved, by `lower_covers_card_le`, `ideal_iso_rank` and `forest_ideal_index_le_two`: a $k$-edge forest has at most $k$ lower covers, while $\Pi(k-1)$ has $(k-1)!$ coatoms; thus $m\le2$.
- Proved, by `forest_ideal_shape_iff`, `single_edges_card`, `long_two_card` and `long_three_card`: the qualifying shapes number $n$, $n-1$ and $(n-1)(n-2)$ respectively. The rank-three count includes the two four-vertex shapes and the disjoint star-and-edge shapes; truncated factors cover the small sizes.
- Proved, by `gamma_formula`, `gammaPos_formula` and `result`: $\gamma_n=n^2-n+2$ and $\gamma_n^+=n^2+2-2n$ for every $n\ge1$. The latter is the literal positive-parameter reading, with natural subtraction evaluated after the addition.
- Proved by the displayed formulas and paper arithmetic: $n^2+n+2$ exceeds $n^2-n+2$ by $2n>0$ for every $n\ge1$. The data are A014206 shifted by one, rather than the printed quadratic at the same index.

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

The bounded literature search does not certify the absence of every previous publication. The general kernel-checked conclusion concerns the binding priority-forest and edge-inclusion convention. No conclusion is claimed for the other final-section questions.
