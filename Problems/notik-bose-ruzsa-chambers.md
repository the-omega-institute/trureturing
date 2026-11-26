---
slug: notik-bose-ruzsa-chambers
bibkey: notik2026singergolomb
doi: 10.48550/arXiv.2611.22656
url: https://arxiv.org/abs/2611.22656v1
triage: theorem
motivation_gids:
  - D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber.result
---

# Shorter rulers in the Bose and Ruzsa chambers

## Problem

Notik's [arXiv:2611.22656v1, §10, page 8](https://arxiv.org/pdf/2611.22656v1#page=8) asks:

> Prove the conjecture of Section 7 for all prime powers, for instance by structured dual certificates as for the Conway–Guy and Bohman sets in [12]; and ask the same for the rulers of Bose [4] and Ruzsa [15].

For each family, consider every allowed field and generator and each coprime multiplier. Cut the multiplied residue set at a largest cyclic gap and translate the first retained mark to zero. The question asks whether each resulting ruler is the unique shortest real ruler in the chamber determined by the order of its labelled positive differences. In §2 a real candidate preserves that order, with minimum distance and consecutive distance increments at least one.

## Motivation

Singer's cyclic difference property yields a complete prefix of small positive differences after the cut. The affine Bose and CRT Ruzsa constructions also have distinct ordinary differences. Their difference sets omit some small residues, so their chambers can behave differently.

## Gap

The original paper poses the analogous questions in §10. The arXiv version record lists v1. A bounded query for each family alongside Golomb rulers and chambers found no settlement. The [Ruzsa construction, Theorem 4.4](https://doi.org/10.4064/aa-65-3-259-282) specifies the CRT residues. It concerns distinct sums modulo the modulus.

## Route

Use gap coordinates from the source. Sums over intervals give all labelled ordinary differences. Certify the field or CRT construction, the normalization after a maximal cut, and the complete order and separation of the rational alternative in each instance. Rational gap vectors cast to real gap vectors with the same inequalities and objective.

## Falsifier

A certified largest-gap cut and a strictly shorter point in its order chamber refute the corresponding universal assertion. Both families admit such a pair.

## Evidence

For Bose, take the affine line through $1+X$ over the base field in $\mathbf F_7[X]/(X^2+4)$. The generator has order $48$. Its line exponents are $1,6,18,20,21,27,31$. Multiplication by $5$ gives cyclic residues $4,5,9,11,30,39,42$. After the cut from $11$ to $30$ of size $19$, the reference marks are $(0,9,12,22,23,27,29)$. The alternative $(0,17/2,23/2,21,22,26,28)$ has length $28$.

For Ruzsa, use $p=5$, primitive root $2$ and multiplier $1$. The CRT residues modulo $20$ are $3,14,16,17$. Cutting from $3$ to $14$ gives reference marks $(0,2,3,9)$. The alternative $(0,2,3,8)$ has length $8$.

The checked declaration `D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber.result` proves the negation of the disjunction of the two universal assertions. Each assertion therefore has its own refutation. [Exact witnesses](https://github.com/the-omega-institute/trureturing/issues/31490#issuecomment-6980867457)

## Triage

### What the settlement shows

Both failures are strict improvements. The witnesses omit ordinary differences $8$ for Bose and $4$ for Ruzsa, both below the corresponding cut gap. Their absence allows the alternatives to shorten the ruler while preserving the order and unit separation. The two alternative lengths above are feasible chamber lengths. Their optimality is open here. The corresponding Singer result uses the complete difference property and applies to its own family.

## ASSUMED-UNVERIFIED

Completeness and priority beyond the bounded literature reading are unverified.
