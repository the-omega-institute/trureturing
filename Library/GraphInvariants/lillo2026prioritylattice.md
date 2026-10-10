---
bibkey: lillo2026prioritylattice
authors: Adrián Lillo and Mercedes Rosas
year: 2026
title: The Priority Lattice
doi: 10.48550/arXiv.2603.28905
url: https://arxiv.org/abs/2603.28905v1
claim: "Section 6, item 3 asks for the principal filters and principal ideals isomorphic to a priority lattice and conjectures left-factorial and quadratic counts."
strata_touched:
  - D5/S3/Combinatorics/PriorityLattice/PrincipalFilters
  - D5/S3/Combinatorics/PriorityLattice/PrincipalIdeals
license: citation-only
triage: anchor
---

# Principal intervals of the priority lattice

## Verified locator

DOI: 10.48550/arXiv.2603.28905

Source: https://arxiv.org/abs/2603.28905v1

## Definitions

Section 2.1, pp. 3–4:

> a *priority forest* (labeled with $[n]_0$ and with $m$ edges) is a rooted forest $(T_0, T_1, \ldots, T_{n-m})$ with all component trees increasing and ordered according to the root's labels, and where for all $j<k$, every label in $T_j$ is smaller than every label in $T_k$. Thus, the vertex set of each tree is an interval of integers

Section 3.1, p. 4:

> The underlying set of $\Pi(n)$ consists of all priority forests labeled with $[n]_0$, together with an extra element $\hat 1$. The order relation $\le$ on $\Pi(n)$ is defined as follows. Given two priority forests $P$ and $P'$, $P \le P'$ if and only if $E(P) \subseteq E(P')$. On the other hand, $\hat 1$ is set to be the top element of $\Pi(n)$.

A parent function on `Fin (n + 1)` records a root by `none` and a non-root by its unique smaller parent. `Relation.EqvGen` records connected components, and their convexity records the interval condition. The forest order is edge inclusion; `WithTop` adjoins the extra greatest element.

## Final-section question

Section 6, item 3, pp. 24–25:

> How many principal ideals of $\Pi(n)$ are isomorphic to $\Pi(m)$, for some $1\le m\le n$? Let $\gamma_n$ denote the number of principal ideals of $\Pi(n)$ that are isomorphic to $\Pi(m)$ with $m \le n$. The sequence $(\gamma_n)_{n\geq 1}$ begins as $2, 4, 8, 14, 22 ,32, 44, \dots$ This sequence seems to be https://oeis.org/A014206, which is given by the formula $\gamma_n = n^2 + n + 2.$ We could also modify this question and ask the number $\theta_n$ of principal filters of $\Pi(n)$ (this is, intervals of the form $[P, \hat 1]$) that are isomorphic to $\Pi(m)$ with $m \leq n$. This sequence begins as $2, 4, 10, 34 ,154 ,874, \dots$ and seems to be https://oeis.org/A003422, the sequence of left factorials, given by $\theta_n = \sum_{i=0}^{n-1} k!.$

## Counting conventions and conclusions

The filter data give $\theta_n=\sum_{k=0}^{n}k!$, the left factorial $!(n+1)$ (OEIS A003422). The printed sum has mismatched indices and its upper bound disagrees with the displayed data.

The ideal data give $\gamma_n=n^2-n+2$, OEIS A014206 with its index shifted by one. The displayed $n^2+n+2$ is false for every $n\ge1$. Allowing only $1\le m\le n$ deletes the $n$ ideals isomorphic to $\Pi(0)$ and gives $n^2+2-2n$. In natural-number arithmetic this is encoded as `n ^ 2 + 2 - 2 * n`.

The counts include the principal ideal of the greatest element. Section 3, p. 7 says, “We do not consider $\Pi(n)$ to be a principal ideal”. Excluding that ideal decreases each ideal count by one. The delivered counts follow the source's numerical data and the convention in issue [14857](https://github.com/the-omega-institute/trureturing/issues/14857), including its natural-subtraction correction.

A principal filter qualifies precisely when every component except the last is a singleton. Its last tree contracts to give the required order isomorphism. An ideal below a forest has rank equal to the edge count and at most that many lower covers. Comparing with the factorial coatom count forces the target parameter to be at most two. Compression to closed edge subsets then enumerates the possible shapes.

## Computed evidence and open boundary

The independent experiment entry is [priority-lattice intervals](https://github.com/the-omega-institute/trureturing-experiments/tree/b22108dae35f49ed44629a59f3e98d2440d7c82a/docs/reports/lillo-rosas-2026-priority-lattice-intervals/). Its `check.py 6` command returned exit code 0; the program SHA-256 is `b71ca8894f15984e5eca4712f947556f024d3d2ddfc7ebe68142090fc7f562ec`. This is finite computed evidence, distinct from the general Lean proofs.

The source's questions on sublattice dismantlability, the flag quasi-symmetric function, and a maximal-chain map to minimal cycle factorizations remain open. The enumeration does not alter the source's other proved results, which do not require these conjectural interval counts. Classifying intervals with both endpoints proper remains open.

Absence of every prior published settlement remains `ASSUMED-UNVERIFIED`; the bounded literature search in issue 14857 found none. The general interval enumerations are repository-derived conclusions, while the source definitions and increasing-tree/permutation correspondence are literature background.
