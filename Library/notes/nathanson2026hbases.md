---
bibkey: nathanson2026hbases
authors: Melvyn B. Nathanson
year: 2026
title: "Problems in additive number theory, VII: The structure of additive h-bases for n"
doi: null
url: https://arxiv.org/abs/2605.26425v3
claim: "Problem 12 asks whether negative elements force ell_h(A) <= n-flat_h(k), or even the strict inequality ell_h(A) < n-flat_h(k). Problem 15 asks which prescribed intervals can occur in an iterated sumset, and how many generators suffice."
strata_touched:
  - D5/S3/Arith/NathansonAdditiveHBasisRefutation
  - D5/S3/Arith/Additive/NathansonProblem15
license: citation-only
triage: anchor
---

# Negative elements in finite additive segment bases

For an integer set `A`, the paper defines `hA` as the set of sums of exactly
`h` not necessarily distinct elements of `A`. It calls `A` an additive
`h`-basis for `n` when `[0,n]` is contained in `hA`, and defines
`ell_h(A)` as the largest such `n`. The quantity is undefined when `0` is
not in `hA`.

For positive `h` and `k`, the paper defines `n-flat_h(k)` as the largest
covered endpoint among all `k`-element sets of nonnegative integers. Problem
12 asks, for `h >= 2`, `k >= 2`, and a `k`-element integer set with negative
minimum, whether `ell_h(A) <= n-flat_h(k)` and whether the strict inequality
`ell_h(A) < n-flat_h(k)` holds. Only the strict statement is addressed by the
associated result.

The reflection example on printed page 7 gives `B={-1,1,2}` and
`2B={-2,0,1,2,3,4}`. The source uses this set to illustrate reflection of
interval bases, not as a stated answer to Problem 12.

Problem 15 asks for a finite integer set whose `h`-fold sumset contains
intervals of length `n+1` exactly at the prescribed starts and whose consecutive
pairs all lie within one of those prescribed intervals. The starts are ordered
with consecutive differences at least `N_q ≥ n+2`, where `h,q ≥ 2` and `n ≥ 1`.
It also asks for the size of the witnessing set. The bound `2q(n+1)` is the
formal result's estimate. Theorem 7 concerns one prescribed interval for `h=2`.

## Verified locator

- Source: https://arxiv.org/abs/2605.26425v3
- Definitions of `hA`, additive `h`-basis, and `ell_h(A)`: printed page 2.
- Definition of `n-flat_h(k)`: printed pages 7-8.
- Problem 12: printed page 9.
- Problem 15: §5, https://arxiv.org/html/2605.26425v3#Thmproblem15
- Theorem 7: §5, https://arxiv.org/html/2605.26425v3#Thmtheorem7
