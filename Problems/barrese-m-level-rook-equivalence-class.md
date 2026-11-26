---
slug: barrese-m-level-rook-equivalence-class
bibkey: barrese2015bijections
doi: 10.1016/j.ejc.2016.03.005
url: https://arxiv.org/abs/1508.05944v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Partitions/RookClassCandidate.universal_formula
  - D5/S3/Combinatorics/Partitions/BarreseSourceNormalization.lOperator_count
---

# Counting all Ferrers boards in an m-level rook-equivalence class

## Problem

Barrese, Loehr, Remmel and Sagan ask in §6.2 of *Bijections on m-level Rook Placements* (arXiv:1508.05944v1, p. 21):

> However, it is an open problem to count the total number of Ferrers boards in a given $m$-level rook equivalence class.

For $m\ge 1$, a $k$-rook placement is a subset of $k$ cells with at most one cell in each column and each bottom-aligned block of $m$ rows. Count every shape $A$ with the same placement counts as $B$ for every $k\ge 0$. Each shape is represented once by its weakly increasing list of positive column heights, including the empty list. Auxiliary leading zeros align the shapes at the lower right. [Source, §§4.1 and 6.2](https://arxiv.org/html/1508.05944v1#S6.SS2)

## Motivation

The following sentence of §6.2 asks for the number of boards with one prescribed ordered level list. The existing Gaussian recurrence evaluates each such fiber. To count an entire class, one needs all its eligible ordered lists, with each represented exactly once. [Prescribed-level dossier](barrese-prescribed-ordered-level-enumeration.md) · [Whole-class registration](https://github.com/the-omega-institute/trureturing/issues/31465)

## Gap

The factorization in §6.1, Theorem 26 gives a root-multiset invariant. Proposition 4.4 of the earlier paper characterizes admissible singleton root vectors. The remaining counting step is to identify the complete native class of arbitrary boards with the disjoint union of the ordered-level fibers selected by these vectors. The preregistration reports a bounded literature search across the source papers and later work on rook graphs and file placements. [Theorem 26](https://arxiv.org/html/1508.05944v1#S6.SS1) · [Proposition 4.4](https://arxiv.org/html/1308.4081v1#S4) · [Literature screen](https://github.com/the-omega-institute/trureturing/issues/31465)

## Route

Let $N\ge |B|+1$, where $|B|$ is the cell count. Write $d$ for the ordered top-down level totals of $B$, padded on the left with zeros to length $N$. Put $z_i=mi-d_i$ for $0\le i<N$. Enumerate the distinct sequences $a$ with the same multiset as $z$. Retain those with $a_0=0$, nonnegative weakly increasing heights $mi-a_i$, and the adjacent floor condition: if neither $a_i$ nor $a_{i+1}$ is divisible by $m$, require $\lfloor a_{i+1}/m\rfloor\le\lfloor a_i/m\rfloor$. Strip the leading zeros from the decoded heights to obtain $C_a$. The class size is

$$
K_m(B)=\sum_{a}W_m(C_a).
$$

For the weight, return zero for a list containing a nonpositive entry. Otherwise put $b=\operatorname{reverse}(C_a)$ and take $U$ to be its first entry, or zero for an empty list. Given $0\le u,v\le U$, set $T_h(u,v)=0$ unless $v\le u$ and $mv\le h$. In the allowed case $T_h(u,v)$ is the coefficient of $q^{h-mv}$ in the Gaussian polynomial $G(u-v+m-1,m-1)$. Use $G(n,0)=1$, $G(0,k+1)=0$ and $G(n+1,k+1)=G(n,k+1)+q^{\max(n-k,0)}G(n,k)$. Then $F([],u)=1$, $F(h::b,u)=\sum_{v=0}^{U} T_h(u,v)F(b,v)$ and $W_m(C_a)=F(b,U)$.

## Falsifier

Two identical normalized shapes counted through different root sequences would invalidate the disjoint sum. So would an equivalent shape whose own ordered levels failed the index test, or an indexed fiber containing a shape with a different rook count. All three conditions concern the same native placement carrier for every allowed common length.

## Evidence

The native completion bijections give the integer polynomial identity at $x=mt$ on the original board. Linear independence in the falling-factorial basis recovers every rook coefficient. The roots of the product recover each multiplicity. The one-rook count recovers the area, so one choice of $N$ works across the entire class. Conversely, the ordered-level list of a board in an indexed fiber recovers the indexed roots and the common area. The theorem `RookClassCandidate.universal_formula` applies the resulting equivalence of carriers and the fixed-fiber recurrence. [Independent mathematical evaluation](https://github.com/the-omega-institute/trureturing/issues/31465#issuecomment-6982080488)

## Triage

The registered theorem covers arbitrary normalized Ferrers shapes and every positive level size. Theorem 26 supplies the factorization in the source. The proof in Lean constructs its completion bijections directly.

### What the settlement shows

The invariant determines which fibers to count, including when equal roots occur. `RookRootIndex.index_family` bounds the number of indices by $N!/\prod_t\nu_t!$, where $\nu_t$ is the multiplicity of root $t$. The common padding bound in `universal_formula` gives the same answer for every $N\ge |B|+1$, with the empty shape contributing one. Singleton input, a prescribed width, and a bound on horizontal positions are unnecessary. The separate prescribed-level question supplies the fiber weights through `BarreseSourceNormalization.lOperator_count`.

## ASSUMED-UNVERIFIED

The literature screen establishes no claim to worldwide priority. The empty-list convention extends Definition 4 to the empty board. Four-slot registration remains unfinished under CLAUDE §3.9. The two retained registration attempts are declared unresolved, and the other listed targets lack complete records. The prior supplier audit is tracked separately. [Registration disclosure](https://github.com/the-omega-institute/trureturing/issues/31465#issuecomment-6981764189) · [Supplier audit](https://github.com/the-omega-institute/trureturing/issues/23540)
