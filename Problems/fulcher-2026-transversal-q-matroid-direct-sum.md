---
slug: fulcher-2026-transversal-q-matroid-direct-sum
bibkey: fulcher2026cyclicflatembedding
doi: 10.48550/arXiv.2603.13550
url: https://arxiv.org/abs/2603.13550v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Matroids/QTransversalDirectSum.fulcher_conjecture_4_8
---

# Fulcher Conjecture 4.8 on transversal q-matroid direct sums

## Problem

> Let \(M_1\) and \(M_2\) be transversal \(q\)-matroids with presentations
> \(\mathcal X_1\) and \(\mathcal X_2\). Then \(M_1\oplus M_2\) is a
> transversal \(q\)-matroid with presentation
> \(\mathcal X_1\oplus\mathcal X_2\).

Theorem 4.7 handles coordinate presentations. Conjecture 4.8 covers
arbitrary presentations. The target uses all finite fields in Lean's
Type universe, arbitrary finite dimensions and slot counts, and every
subspace \(U\) of the sum. Each slot keeps its index, including when
several slots carry the same subspace. [Fulcher, arXiv:2603.13550v1](https://arxiv.org/html/2603.13550v1#S4.Thmtheorem8)

## Gap

The preregistered search found the coordinate case and narrower uniform
cases. Its coverage is bounded to the sources and searches recorded in
the issue. [Preregistration #35130](https://github.com/the-omega-institute/trureturing/issues/35130)

## Route

Let \(f_X(T)\) count the slots of \(X\) that do not contain \(T\). The
one-presentation rank is the minimum of \(f_X(T)+\dim U-\dim T\) over
\(T\le U\). The proof first minimizes the Hall bounds indexed by slot
subsets. For the lower bound, dimension inequalities for restricted
annihilators give representatives of the required rank by padding the
linear Rado problem and projecting. Lifting the representatives to
annihilators on the ambient space gives a partial q-transversal of
sufficient dimension. Intersecting a set of selected slots with \(U\),
and taking the slots containing a given \(T\), transfer the minimum
between the two indexing sets.

For a common \(W\le U\), take minimizers \(A\le \pi_1 W\) and
\(B\le \pi_2 W\). Their simultaneous preimage \(T\) inside \(W\)
satisfies both projection constraints and
\[
\dim W-\dim T
\le (\dim\pi_1 W-\dim A)+(\dim\pi_2 W-\dim B).
\]
The two slot counts add on \(T\). Comparing the cost at \(T\) with
the two projected costs gives the upper bound on the concatenated rank.
For the lower bound, a minimizing subspace for the concatenated
presentation serves as \(W\), and each factor rank is bounded by the
count of its slots that do not contain its projection of \(W\).

## Falsifier

A disagreement between the indexed lifted slots and the two product
families, or a failure of either rank inequality for some common
\(W\le U\) in its applicable comparison, would invalidate the
corresponding step.

## Evidence

The Lean statement uses the original every-basis
IsPartialQTransversal and the associated supremum rank
qTransversalRank. Its concatenated slots are the pullbacks of the
factor slots under the two coordinate projections. Thus they are
\(X_i\oplus E_2\) and \(E_1\oplus Y_j\) under the coordinate
equivalence. The right side is the minimum in Fulcher's
Definition 2.7 and Ceria–Jurrius Definition 38, with the same
\(W\le U\) in both projection terms. [Direct-sum rank](https://arxiv.org/html/2603.13550v1#S2.Thmtheorem7)

## Triage

**Proved.** The concatenated family presents the direct sum on every
subspace, including those that mix coordinates of both factors. The
preimage estimate shows how related projected minimizers control rank
on such a subspace even when it is not the product of its projections.
