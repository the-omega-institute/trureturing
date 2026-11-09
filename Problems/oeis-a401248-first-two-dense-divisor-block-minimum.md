---
slug: oeis-a401248-first-two-dense-divisor-block-minimum
bibkey: pol2026a401248
doi: null
url: https://oeis.org/A401248
triage: theorem
motivation_gids:
  - D5/S3/Factorization/TwoDenseDivisorBlocksPalindrome
---

# First two-dense divisor block has minimum length

## Problem

> Conjecture 1: a(n) = A384222(n,1).

Omar E. Pol, OEIS A401248. The source defines a(n) as the smallest
number in row n of A384222. For each positive natural n, list every
positive divisor once in increasing order, and cut exactly at each
adjacent pair a,b with b>2a. If B is any resulting maximal contiguous
block and Bfirst is the first one, the assertion is |Bfirst|<=|B|.
The equality case b=2a remains joined, and n=1 has its singleton block.
There is no parity, squarefree, size or finite-cutoff restriction.
Only Conjecture 1 is included; Conjecture 2 is outside this problem.

## Motivation

This is a first-tier recent OEIS conjecture, dated October 28, 2026,
with an elementary unrestricted proof route. The existing palindromic
row and maximum formula concern the same divisor partition but do not
supply first-block minimality. The exact event and literature
qualification are preregistered in issue
https://github.com/the-omega-institute/trureturing/issues/27188.

## Gap

The bounded qualification found no complete prior resolution in the
inspected sources. Dense/rough factorization is known mathematics;
its relation to every actual maximal block requires a cardinality
argument. Global literature absence and discovery priority remain
unverified.

## Route

Call u interval-dense if for every integer 0<x<u some divisor d of u
satisfies x<d<=2x. One is interval-dense. If p is positive and p<=2u,
then up is interval-dense: use an old divisor for x<u, use p for
u<=x<p, and otherwise scale a divisor above floor(x/p).

Choose a largest interval-dense divisor u of n and put v=n/u.
A prime p dividing v cannot satisfy p<=2u, since up would then be a
larger eligible divisor. Thus every prime factor of v exceeds 2u and
u,v are coprime. Interval coverage makes the sorted divisor list of
u two-dense. All divisors of n outside D(u) exceed 2u, so D(u) is
exactly the first block.

For any divisor d in any block B of n=uv, coprimality gives
d=gcd(d,u)gcd(d,v). The whole scaled list gcd(d,v)D(u) consists of
divisors of n, is two-dense and contains d. A strict separating gap
in the complete divisor list cannot split this copy. Multiplication
by the positive gcd(d,v) is injective, proving |D(u)|<=|B|. The first
block has length |D(u)|, giving the unrestricted event.

## Falsifier

A positive integer whose first actual block is longer than another
actual block would refute the conjecture. A finite table, a restricted
family or an assumed dense-factor existence premise cannot establish
the universal assertion.

## Evidence

`D5/S3/Factorization/TwoDenseDivisorBlockMinimum.result : claim`
constructs the dense factor internally. The claim uses the complete
Mathlib sorted divisor list and its actual splitBy partition; its
first length is the existing palindrome module's row head. Thus the
formal event compares that first length with every actual block
length for every positive integer.

The mathematical argument is unbounded and symbolic. It uses neither
finite enumeration nor an assumed dense-factor existence premise.
The matching Scribe identifies this result with the single externally
named A401248 Conjecture 1.

## Triage

The decisive structure is the dense coprime divisor copy contained
in every actual maximal block. The first block attains the common
lower bound, so the first row value is its least element. At n=1 the same construction takes u=v=1, and equality
at ratio two is retained throughout. These are consequences inside
the universal theorem, not additional retained finite certificates.

Divisibility of all block lengths by the first length, other density
thresholds and A401248 Conjecture 2 are not settled by this result.
They require their own exact statements and qualification. Neither
this theorem nor the source search establishes global priority.

## ASSUMED-UNVERIFIED

The correspondence between the OEIS words and the formal block model
requires independent semantic review. The source and literature
qualification is bounded and cannot exclude all unindexed equivalents.
The formal theorem and its identification with the source conjecture
do not establish global priority.
