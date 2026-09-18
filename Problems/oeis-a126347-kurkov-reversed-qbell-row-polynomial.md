---
slug: oeis-a126347-kurkov-reversed-qbell-row-polynomial
bibkey: kurkov2025a126347
doi: null
url: https://oeis.org/A126347
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Algebraic/KurkovReversedQBellRowPolynomial.result
---

# Kurkov's reversed q-Bell row polynomial

## Problem

OEIS A126347 has offset `%O 0,6`. Its coefficient data begins (`%S`,
verbatim):

> 1,1,1,1,1,2,1,1,1,3,3,4,2,1,1,1,4,6,10,9,7,7,4,2,1,1,1,5,10,20,25,26,

Its NAME line (`%N`, verbatim) is:

> Triangle, read by rows, where row n lists coefficients of q in B(n,q) that satisfies: B(n,q) = Sum_{k=0..n-1} C(n-1,k)*B(k,q)*q^k for n>0, with B(0,q) = 1; row sums equal the Bell numbers: B(n,1) = A000110(n).

Mikhail Kurkov's conjecture (`%F`, verbatim) is:

> Conjecture: R(n,n) is the (n+1)-th reversed row polynomial where R(0,0) = 1, R(n,k) = R(n-1,n-1) + x^n * Sum_{j=0..k-1} R(n-1,j) for 0 <= k <= n. - _Mikhail Kurkov_, Jul 06 2025

The AUTHOR line (`%A`, verbatim) is:

> _Paul D. Hanna_, Dec 31 2006, May 28 2007

The referenced Bell-number entry A000110 has NAME line (`%N`, verbatim):

> Bell or exponential numbers: number of ways to partition a set of n labeled elements.

The exact formal statement is:

```lean
forall n : Nat, kurkovR n n = (qBell (n + 1)).reverse
```

Here `qBell` uses Wagner's q-Bell recurrence. The formal reversal is
reflection about the natural degree. The locally proved facts that `qBell n`
is monic of degree `Nat.choose n 2` ensure that this is the fixed-row
coefficient reversal meant by the source.

## Motivation

Kurkov's recurrence builds each row from the preceding diagonal and its
prefix sums. The theorem identifies its diagonal with the reversed q-Bell
coefficient rows for every natural index, upgrading the printed conjecture
from numerical evidence to a kernel-checked unbounded identity.

## Gap

The OEIS text endpoint still labels the line "Conjecture". Wagner's 2004
paper establishes the q-Bell recurrence but predates Kurkov's triangular
recurrence. Pan and Yu, arXiv:2302.03643v4, identify the degree-based
reversal of q-Bell polynomials and thereby attest their degree and monicity,
but their text contains neither Kurkov's recurrence nor the conjectured
identity. No dominating theorem was found in the repository or pinned
Mathlib searches recorded in issue #8219.

The load-bearing new proposition is `kurkovR_pascal_expansion`: it expands a
Kurkov row prefix into a binomial Pascal row. This proposition is neither a
restatement of the final diagonal identity nor a direct instance of the
available polynomial library, and it remains on the final proof path.

The result formalizes only Kurkov's quoted conjecture and no other formula
or comment line from the A126347 entry.

## Route

1. Prove by strong induction that `qBell n` is monic of triangular degree.
2. Prove the Pascal expansion of `kurkovR n k` by induction on the row and
   column, using Pascal's identity for the binomial weights.
3. Reflect Wagner's recurrence about the triangular degree and identify the
   reflected convolution with the Pascal expansion.
4. Induct on the diagonal and conclude with Mathlib's degree-based reverse.

## Falsifier

Any natural `n` for which `kurkovR n n` differs from the coefficient reversal
of `qBell (n+1)` contradicts the theorem. A failure of monicity or triangular
degree would also invalidate the identification of Mathlib's natural-degree
reverse with the source's fixed-row reversal.

## Evidence

- `qBell_monic_degree` proves monicity and degree `Nat.choose n 2` for every row.
- `kurkovR_pascal_expansion` proves the binomial expansion of every in-range
  Kurkov row entry and is used in the diagonal induction.
- `result` has exactly the universal statement displayed in the Problem section.
- Wagner 2004 and Pan--Yu 2024 attest the q-Bell recurrence and reversal degree,
  while neither contains Kurkov's later triangular identity.

## Triage

`theorem`; resolution `proved`.

## ASSUMED-UNVERIFIED

Historical priority outside the named OEIS, Wagner, Pan--Yu, repository, and
pinned-library surfaces is unverified. No exhaustive novelty or priority claim
is made; this boundary does not affect the formal universal identity.
