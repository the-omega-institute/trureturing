---
slug: tyagi-2026-divisor-nim-sharper-sg-bound
bibkey: tyagi2026divisornim
doi: 10.48550/arXiv.2610.06925
url: https://arxiv.org/abs/2610.06925v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Games/DivisorNimBound.result
---

# Tyagi's sharper Sprague–Grundy bound for Divisor Nim

## Problem

Satyam Tyagi, “Removing m from m-pile Divisor Nim”, arXiv:2610.06925v1,
§5, printed p. 23, states:

> For every nonempty position P, g(P) ≤ 2hmin(P).

A position is a finite multiset of positive natural numbers. A move chooses
one occurrence of a heap h and a positive integer d ≤ h, requires d to divide
every other heap, and replaces h by h − d, omitting a zero remainder. The
removal need not divide h. The Grundy value is the mex of follower values.

The Lean proposition `claim` states that every positive nonempty multiset P
and every member m that is at most every member of P satisfy g(P) ≤ 2m.
The theorem `result : claim` preserves these quantifiers and the literal move
rule, including repeated heaps and singletons.

## Motivation

The source proves g(P) ≤ 2hmin(P) + ⌊log₂ hmin(P)⌋, independently of the
number and sizes of the other heaps. The sharper conjecture removes the
remaining logarithmic term. A bound for every board containing a distinguished
heap remains usable when a follower acquires a smaller heap.

## Gap

Tier 1: the conjecture closes arXiv:2610.06925v1 (submitted 2026-10-03), the
only version arXiv lists. A literature check on 2026-10-10 searched the
identifier, the title, Divisor Nim with Sprague–Grundy bounds, and the author
name. It found no later version, citing work, or other proof of the bound
g(P) ≤ 2h_min(P).

The additive logarithmic allowance in the source's universal ceiling does not
give the conjectured bound. Lower-valuation moves can either preserve the
distinguished heap or change it. Their separate ceilings, together with a
divisor count for exceptional removals, close this gap.

## Route

Let k be the minimum 2-adic valuation and let r count heaps at that valuation.
Induction on total stones gives g(P) = 0 exactly when r is even. If at least
two heaps are odd, the Grundy value is at most one. Mex counting gives a ceiling
B + a + 1 whenever all follower values except at most a distinct exceptions
are at most B.

For a positive reference heap at most H, define

$$
U_k(H)=\sum_{j=0}^{k}\left\lfloor\frac{H}{2^j}\right\rfloor+k+1.
$$

Depth induction bounds the Grundy value by U_k(H). Write a distinguished heap
as m = 2^v u with u positive and odd. Its presence implies k ≤ v. When
u ≥ v + 1, the identity
U_k(m) + m/2^k = 2m + k + 1 implies U_k(m) ≤ 2m.

For the remaining odd parts u ≤ v, let t be the number of positive divisors
of u, and define

$$
\begin{aligned}
D_0&=(v+1)t+1,\\
E_j&=2m-m/2^j-2^{j+1}+j+2,\\
a_k&=\begin{cases}(v-k+1)t,&k<v,\\u,&k=v,\end{cases}\\
D_k&=\max(D_{k-1},E_0,\ldots,E_{k-1})+a_k+1.
\end{aligned}
$$

For v ≥ 1, every board containing m and having depth k has Grundy value at most D_k.
An unchanged distinguished heap permits the earlier D ceiling. When it changes
under a valuation-j removal, its positive remainder is at most m − 2^j,
and U_j(m − 2^j) = E_j. The exceptional removals act on a unique minimum-depth
heap. Their number is bounded by a_k.

For v ≥ 16 put A = v(v + 1)/2. Integer induction proves
v(A + 2v + 1)² ≤ 2^(v+3) and A + 2v + 2 ≤ 2^(v+1).
The product of m/2^j and 2^(j+1) is 2m. The arithmetic mean-geometric mean
inequality therefore gives

$$
Au+2v+1\le m/2^j+2^{j+1}\qquad(j<v).
$$

This pays for the changed-reference ceiling and the total recurrence increment,
which is at most Au + v. The initial ceiling plus the same increment is at most
2m as well. Thus D_v ≤ 2m.

For 1 ≤ v ≤ 15, odd 1 ≤ u ≤ v, and excluding (1,1), (2,1), and (3,1),
there are exactly 61 pairs. Kernel decisions establish D_v ≤ 2m for every pair.
The three remaining heaps m = 2, 4, and 8 satisfy the bounds 4, 8, and 16
by direct follower classifications. The argument applies to any distinguished
heap; choosing a smallest one proves the stated claim.

## Falsifier

A failure would be a positive nonempty multiset whose literal-move Grundy value
exceeds twice a smallest member. The proof must retain the requirement on every
unchanged heap, distinguish repeated occurrences, omit empty heaps, and decrease
total stones in the recursion. The distinguished-heap recurrence must cover
boards containing that heap even when another heap is smaller. These obligations
are incorporated in the compiled definitions and the proof of `result`.

## Evidence

`D5/S3/Combinatorics/Games/DivisorNimBound.result` has Lean type `claim`.
The game recursion is well-founded on multiset sum. Its supporting modules prove
the mex facts, the valuation-parity outcome criterion, the coarse and
distinguished-heap recurrences, the universal small-heap bounds, and the integer
estimates. The 61 finite recurrence checks use kernel decisions; they do not
enumerate possible game positions to infer the universal theorem. No `sorry`,
new axiom, or `native_decide` occurs in these modules.
The axiom closure of `result` is `propext`, `Classical.choice`, and `Quot.sound`.

## Triage

- [proved: D5/S3/Combinatorics/Games/DivisorNimBound.result]
  Every positive nonempty board satisfies g(P) ≤ 2hmin(P).
- [computed: supplied numerical check, 8 872 boards with one through five heaps]
  The maximum of g(P) − 2hmin(P) is zero, so the bound is attained in that
  finite collection. An independent literal-move recursion also gives
  g(1,4,10) = 2 = 2hmin(1,4,10). Numerical checks are separate from the
  universal Lean proof.
- [open]
  The source's second conjecture remains unsettled: for every nonempty fixed
  board A, its least eventual Grundy period divides
  2·lcm(1,…,hmax(A)), where the varying heap is excluded from hmax(A).

## ASSUMED-UNVERIFIED

The 8 872-board count and its one-through-five-heap scope are supplied numerical
evidence; the original board list is not available here for independent
reproduction. The equality example (1,4,10) was recomputed independently.
The literature check is an indexed web search. Forward-citation indices were not consulted.
