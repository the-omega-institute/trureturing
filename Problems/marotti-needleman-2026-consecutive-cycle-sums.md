---
slug: marotti-needleman-2026-consecutive-cycle-sums
bibkey: marotti2026consecutive
doi: 10.48550/arXiv.2610.08889
url: https://arxiv.org/abs/2610.08889
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/CycleSums/ConsecutiveCycleSums.result
---

# Sublinear edge completion for consecutive cycle sums

## Problem

Marotti and Needleman, *Consecutive Cycle Sums*, arXiv:2610.08889, Section 5, final paragraph on printed page 6, ask whether the cycle with labels 1, …, n can eventually be completed using at most n/a added edges for every positive integer a. A graph is complete when every integer from 1 through T_n = n(n + 1)/2 is the label sum of a nonempty vertex set inducing a connected subgraph. The label order remains fixed, and mEC(n) is the minimum number of edges added to this cycle to make it complete.

The precise target is: for every integer a ≥ 1, there exists N such that, for every integer n ≥ N, a complete graph containing the original n-cycle has an added-edge count e satisfying ea ≤ n.

## Motivation

Preregistration #14954 identifies the eventual sublinear edge-completion question as an unsettled named problem from Section 5. An explicit construction gives a uniform bound of order square root of n, resolving the stated eventual n/a question without determining the exact minimum.

## Gap

The literature check supplied with preregistration #14954 reports that arXiv has only version v1 and that searches on the title, the identifier and the problem terms found no later work resolving the question. This is a bounded literature check, not an exhaustive priority claim. The source's request to determine the exact value of mEC(n) remains separate from its eventual sublinear-growth question.

## Route

For n ≥ 8, let k ≥ 4 be least with T_k ≥ n + 4. Then k < n. Add the edges joining label 1 to labels 3, …, k + 1; this uses at most k − 1 new edges.

For every k ≥ 4, subsets of {2, …, k} realize every integer in [2, T_k − 3]. The base k = 4 is explicit. At the induction step, the old subsets cover [2, T_k − 3], while adjoining k + 1 covers [k + 3, T_{k+1} − 3]. These integer intervals overlap or abut because T_k ≥ k + 5. Adjoining label 1 makes every such subset connected and realizes [3, T_k − 2].

For k ≤ j ≤ n, put P_j = ∑_{v=k+1}^j v. Adjoining the tail labels k + 1, …, j preserves connectivity and realizes [3 + P_j, T_k − 2 + P_j]. Consecutive intervals overlap or abut since their shift is j ≤ n ≤ T_k − 4. Their union therefore covers [3, T_n − 2]. The values 1, 2, T_n − 1 and T_n are realized by {1}, {2}, {2, …, n} and {1, …, n}, respectively.

Minimality gives T_{k−1} < n + 4 and consequently (k − 1)² < 2n + 8. For a ≥ 1 choose N = max(8, 4a²). Then n ≥ N implies 2n + 8 ≤ 3n and 3a² ≤ n, so (k − 1)a ≤ n. This proves the eventual edge budget and hence mEC(n) = o(n).

## Falsifier

Failure of the bounded subset-sum representation, a gap between consecutive tail-prefix intervals, or a constructed vertex set whose induced graph is disconnected would invalidate the construction. A counterexample to the universal target would require a positive a and arbitrarily large n for which every complete supergraph of the fixed labelled n-cycle uses more than n/a new edges. Reordering the labels or replacing induced connectivity by a different notion would change the problem.

## Evidence

The formal target uses `SimpleGraph.cycleGraph n` on `Fin n`, with vertex v carrying label v.val + 1. Completeness uses the connectedness of the induced graph on each witness set and the exact natural label sum. The added-edge budget is the natural cardinality of the edge-set difference multiplied by a.

The designated declaration is `D5/S3/Combinatorics/CycleSums/ConsecutiveCycleSums.result : claim`. The arithmetic and graph helper modules supply the subset-sum intervals, tail-prefix witnesses, edge bound and induced-connectivity arguments. The mathematical construction proves the stronger integer estimate that, for every n ≥ 8, some complete supergraph uses at most k − 1 edges with (k − 1)² < 2n + 8. The targeted Lean build `make lean LEAN_TARGETS="D5.S3.Combinatorics.CycleSums.ConsecutiveCycleSums"` exited 0; the arithmetic and graph dependencies were checked by the same explicit-target build. This is scoped evidence and does not assert a whole-repository build or freeze status.

## Triage

- [proved] For n ≥ 8, mEC(n) < √(2n + 8), and therefore mEC(n) = o(n). The eventual n/a question is resolved by N = max(8, 4a²).
- [open] The exact mEC(n) and a matching lower bound.

## ASSUMED-UNVERIFIED

The implementation seat has no online literature access. The version and literature-gap statements rely on the supplied preregistration #14954 check and have not been independently refreshed here. The correspondence between the paper's wording and the fixed-label connected-subset formal target is a source interpretation rather than a Lean theorem. No exact minimum or optimal asymptotic lower bound is claimed.
