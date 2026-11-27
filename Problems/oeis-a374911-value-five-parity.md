---
slug: oeis-a374911-value-five-parity
bibkey: oeis2024a374911
doi: null
url: https://oeis.org/A374911
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/PowerResidueRecursionFive
---

# Parity of the indices at value five in OEIS A374911

## Problem

[OEIS A374911, revision 26](https://oeis.org/A374911/internal), submitted by Bryle Morga, defines

> a(n) = a(2^n mod n) + a(3^n mod n), with a(0) = 1.

The comments ask

> Most solutions to a(n) = 5 seem to be divisible by 5 and all of them seem to be even. Why?

The parity question is whether every natural index \(n\) with \(a(n)=5\) satisfies \(2\mid n\). The Lean statement uses the original `PowerResidueRecursionFour.seq`, whose zero branch gives one and whose positive branch uses the two specified remainders in order. [Preregistration #34793](https://github.com/the-omega-institute/trureturing/issues/34793)

## Motivation

This is a Tier 1 question about the level set at five. The classifications at one through four constrain the two recursive values and reduce the parity question to an arithmetic condition on the index.

## Gap

The preregistration reports no proof in its bounded screen of the source and directly related OEIS entries A000079, A015910 and A066601, arXiv, Crossref, and repository and issue searches. Some search pages were inaccessible. The closure of that literature screen is `ASSUMED-UNVERIFIED`.

## Route

At value five, the two positive recursively evaluated terms sum to five. A left value of one would force a positive power of two as the index, where the sequence takes value three. A right value of one makes the index divide the power of three. Its least prime factor is then three. The left value would be four, making its remainder three or nine and implying that three divides the power of two.

For \(n>1\), if \(a^n\equiv 1\pmod n\), the order of \(a\) modulo the least prime factor \(p\) of \(n\) divides \(n\) and \(p-1\). These numbers are coprime, so \(a\equiv1\pmod p\). Applying this to base two rules out left value two. The sole remaining pair is \((3,2)\). The existing classifications give the residue characterization and its converse. The base-three congruence forces \(p\mid 2\), so \(p=2\).

## Falsifier

A single odd natural index at which the original recursion takes value five would falsify the claim. The two smallest indices have values one and two, respectively.

## Evidence

`D5/S3/Arith/Congruence/PowerResidueRecursionFive.oeisA374911_valueFive_even` proves the literal parity assertion. Its admission basis is `open-problem-resolution` under #34793. The proof uses the forward direction of the residue characterization. The Lean target uses pinned Mathlib.

## Triage

| Source question | Status |
| --- | --- |
| Parity of every index with value five | Proved by `oeisA374911_valueFive_even` |
| “Most” indices with value five are divisible by five | The source specifies no frequency or density threshold |
| Surjectivity onto the positive integers | Open in this settlement |

### What the settlement shows

The private residue characterization proves that value five occurs exactly when \(3^n\bmod n=1\) and \(2^n\bmod n=2^k\) for some positive natural exponent \(k\). The parity implication uses the first residue condition. The source's observation about multiples of five and its conjecture that every positive value occurs remain separate questions.

## ASSUMED-UNVERIFIED

Completeness of the bounded literature screen.
