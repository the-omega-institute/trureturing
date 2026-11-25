---
slug: dfl512-even-odd-power
bibkey: dietzflowerslockard2026cmp
doi: 10.13069/jacodesmath.v13i3.393
url: https://jacodesmath.com/index.php/jacodesmath/article/download/393/304
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Partitions/OddPowerSelfConjugateCMP
---

# The smallest odd power admitting a self-conjugate CMP at an even base

## Problem

Dietz, Flowers and Lockard, *A study of m-ary partitions whose conjugates are q-ary*, Question 5.12 (printed p. 404, publisher PDF p. 20, arXiv:2609.08799v1 Question V.18), asks:

> When $m$ is even, is $m^{m+1}$ the smallest odd power of $m$ that posseses a self-conjugate CMP?

The base is a natural number at least two. A conjugate m-ary partition (CMP) has all positive row and column lengths equal to natural powers of $m$. Self-conjugacy means that transposing the finite Young diagram gives that same diagram. [Definition 1.1 and source locator](../Library/FiniteGeometry/dietzflowerslockard2026cmp.md)

## Motivation

At a fixed base $m\ge 2$, the powers of $m$ strictly increase with the exponent. The least odd exponent therefore identifies the smallest odd power by cardinality. [Preregistration #33753](https://github.com/the-omega-institute/trureturing/issues/33753)

## Gap

Discussion 5.11(1) gives an attaining diagram of size $m^{m+1}$ through $(MR)^m$, also given by Flowers and Lockard's Lemma 4.2. The question asks whether there is a self-conjugate CMP of size $m^e$ for some odd $e<m+1$. [Flowers and Lockard, Lemma 4.2](https://ajc.maths.uq.edu.au/pdf/81/ajc_v81_p458.pdf#page=10)

## Route

Write $N=m^e$ for the area and $L=m^K$ for the first row length. The first row and first column together have $2L-1$ cells. The whole diagram is inside an $L\times L$ square, so $2L-1\le N\le L^2$. An odd positive exponent and $m\ge2$ imply $K<e<2K$. The imported `square_modulus` gives $(m-1)^2\mid N-(2L-1)$. Expanding $m^e$ and $m^K$ with Mathlib's `sq_dvd_add_pow_sub_sub` and cancelling one factor of $m-1$ gives $(m-1)\mid (2K-e)$. Consequently $m-1\le 2K-e\le e-2$ and $m+1\le e$.

The published diagram is the union of rectangles with heights $m^j$ and widths $m^{m-j}$ for $0\le j\le m$. Transposition takes the rectangle indexed by $j$ to the one indexed by $m-j$. Row zero has width $m^m$, and the rows with indices in $[m^{j-1},m^j)$ have width $m^{m-j}$ for $1\le j\le m$. The band has $m^m-m^{m-1}$ cells, so the area with the top row included is $m^{m+1}$. At even $m$, its exponent $m+1$ is odd.

## Falsifier

A self-conjugate CMP of size $m^e$ at any even $m\ge2$ and odd $e<m+1$ would refute the lower bound. Failure of the stated cell set to be self-conjugate, to have power row lengths, or to have the claimed area would refute the corresponding property of the proposed witness.

## Evidence

The [Lean endpoint](../D5/S3/Combinatorics/Partitions/EvenBaseOddPowerSelfConjugateCMP.lean) proves `IsLeast` on the exponents $e$ satisfying `Odd e` and admitting a `YoungDiagram` of card $m^e$ with the existing `IsCMP` predicate and equality to its transpose. Its conclusion includes membership at $m+1$. The binary witness has rows $(4,2,1,1)$ and area eight. The lower bound excludes exponent one. [Blueprint](../Blueprint/D5/S3/Combinatorics/Partitions/EvenBaseOddPowerSelfConjugateCMP.md)

## Triage

### What the settlement shows

The endpoint `D5/S3/Combinatorics/Partitions/EvenBaseOddPowerSelfConjugateCMP.result` answers Question 5.12 for every even base $m\ge2$, including even composite bases. The divisibility of the positive exponent gap gives the lower bound without an evenness assumption, and evenness admits the attaining exponent. Question 5.13 and classification of all possible sizes remain open here. Question 5.14 has its own [settlement](dfl514-selfconj.md).

## ASSUMED-UNVERIFIED

Worldwide publication priority and completeness of the literature search are unverified.
