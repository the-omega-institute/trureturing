---
bibkey: rowlandsistosbarron2025powers
authors: Eric Rowland and Jesús Sistos Barrón
year: 2025
title: Complexity of powers of a constant-recursive sequence
doi: 10.48550/arXiv.2501.14643
url: https://arxiv.org/abs/2501.14643v1
claim: Section 1 conjectures finitely many rank sequences for each fixed initial rank.
strata_touched:
  - D5/S1/Recurrence/RowlandSistosBarronRankSequences
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2501.14643

Source: https://arxiv.org/abs/2501.14643v1

## Source statements

Section 1, page 2: “We say that a sequence of integers is a rank sequence if it
arises as (rank s(n)^M)_{M≥1} for some constant-recursive integer sequence
s(n)_{n≥0}. For each r ≥ 1, we conjecture that there are only finitely many rank
sequences associated with sequences s(n)_{n≥0} of rank r, and we are interested
in enumerating them.”

Section 2, page 3: “First, a constant-recursive sequence is one which satisfies
a recurrence equation of the form s(n + r) = c_{r−1} s(n + r − 1) + · · · +
c_1 s(n + 1) + c_0 s(n). for any sufficiently large n, where the coefficients
(c_{r−1}, . . . , c_0) are all constants and c_0 ≠ 0. Every constant-recursive
sequence satisfies infinitely many recurrences, but there is only one of
minimal size, that we define to be the rank of s(n), and denote it by rank s.”

The Lean encoding uses integer sequences, rational constant-coefficient
recurrences on a tail, the least recurrence order, and positive natural
exponents. Equality of rank sequences means equality at every positive
exponent, rather than eventual equality. The rational coefficient field is
the field fixed by the statement on issue
[#19942](https://github.com/the-omega-institute/trureturing/issues/19942).

## Result and scope

The family s_p(n) = p·8^n − 4^n − 2^n has rank three for p ≥ 3.
The rank of its M-th power is the number of nonzero coefficients of
(1 + X − pX²)^M. For each fixed M, only finitely many natural parameters
have a zero coefficient in degrees 0 through 2M. At M = 2p + 1 the
coefficient of X² vanishes. These two facts make every parameter fibre
of the rank-sequence map finite, and yield infinitely many rank sequences
of initial rank three.

This refutes the unrestricted Section 1 conjecture. Finiteness restricted to
general rank sequences, Conjecture 5.3 on eventual polynomial or
pseudo-polynomial behaviour, and the exact first cancellation for each
parameter remain open here. The proof does not assert that the first
cancellation occurs at 2p + 1.

The experiment cited on #19942 is in
`the-omega-institute/trureturing-experiments`, commit `ec0476c9`, file
`docs/reports/rowland-sistos-barron-2025-rank-sequences/check.py`, SHA-256
`544161d3a2d4295dfa4e074ec2f4bb89a5891980d4ca579b7bc5cc1f0955fdb6`.
Its recorded exit code is 0; in particular R_3(7) = 13 and R_11(7) = 15.
These computations are separate from the symbolic Lean proof.

The source and literature screen are recorded on #19942. Completeness of
the literature screen is ASSUMED-UNVERIFIED; repository priority is
repo-prior-exposed.
