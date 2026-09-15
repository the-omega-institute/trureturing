---
slug: oeis-a339621-fibonacci-divisor-sum-even-index
bibkey: lagneau2020a339621
doi: null
url: https://oeis.org/A339621
triage: theorem
motivation_gids:
  - D5/S1/Scale/Fibonacci
---

# Fibonacci divisor sums at square-plus-one arguments have even index

## Problem

OEIS A339621 records these lines verbatim:

```text
%N Sum of Fibonacci divisors of n^2 + 1.
%C A Fibonacci divisor of a number k is a Fibonacci number that divides k. (The divisor 1 is only counted once.)
%C Conjecture: If the sum of the Fibonacci divisors of m^2 + 1 is a Fibonacci number, then this number belongs to the sequence A001906(n) = F(2n) where F(n) is the Fibonacci sequence.
%A _Michel Lagneau_, Dec 10 2020
```

Formally, let `FibValues(N)` be the finite set of distinct positive Fibonacci
values dividing `N`, so the value 1 occurs once. For every natural `m`, if
`sum(FibValues(m^2 + 1)) = F_r` for some positive index `r`, then there is a
positive integer `q` such that `sum(FibValues(m^2 + 1)) = F_(2q)`.

## Motivation

The conjecture asks whether a divisibility-defined set can sum to a Fibonacci
number of odd index. Carlitz's classification answers the stronger question
for every finite set of distinct Fibonacci values that contains 1, without
using the square-plus-one form.

## Gap

The OEIS comment labels the statement a conjecture, but Leonard Carlitz's 1968
Theorem 2 already classifies every representation of a Fibonacci number as a
sum of distinct Fibonacci values. The A339621 statement is therefore
literature-attested as an immediate corollary rather than an open target.

## Route

Carlitz proves `R(F_r) = floor(r/2)` and lists all representations as
`S_(r,k) = {F_(r-2k)} union {F_(r-2j-1) : 0 <= j < k}`.
The A339621 divisor set is finite, has distinct Fibonacci values, and contains 1.
If its sum is `F_r`, it is therefore one of Carlitz's sets `S_(r,k)`.
Among those sets, a representation contains the value 1 exactly when `r` is even.
Hence `r = 2q` for some positive `q`, which is precisely membership in A001906.
No property special to `m^2 + 1` is needed.

## Falsifier

A counterexample would be a natural `m` whose distinct Fibonacci divisors of
`m^2 + 1`, counting 1 once, sum to `F_r` for an odd positive index `r`. Such a
set would contradict Carlitz's complete representation classification.

## Evidence

- OEIS source: `Library/notes/lagneau2020a339621.md`.
- Published classification: Leonard Carlitz, "Fibonacci Representations",
  *The Fibonacci Quarterly* 6(4) (1968), 193-220, Theorem 2,
  DOI `10.1080/00150517.1968.12431213`.
- Sam Chow and Tom Slattery, "On Fibonacci partitions", *Journal of Number
  Theory* 225 (2021), 310-326, equation (1.1), reproduces Carlitz's count.

## Triage

`theorem`, literature-attested. The deduction above resolves the OEIS
statement at the literature layer. This dossier does not introduce or retain a
Lean theorem.

## ASSUMED-UNVERIFIED

No exhaustive historical priority claim beyond the cited Carlitz, Chow-Slattery,
and OEIS records is made. No Lean formalization of this corollary is claimed.
