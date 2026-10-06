---
slug: egecioglu-gaiser-yin-rotation-wilf-classes
bibkey: egecioglu2026rotations
doi: 10.48550/arXiv.2607.20750
url: https://arxiv.org/abs/2607.20750v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/RotationAvoidance/RotationAvoidance.result
---

# Wilf Classes of Rotation Avoidance for Patterns of Length Four

## Problem

Ömer Eğecioğlu, Collier Gaiser and Mei Yin, *Pattern avoidance in permutations and their rotations*,
arXiv:2607.20750v1, Section 6, Open Question 6.1: for k ≥ 4, are the Wilf classes of S_n^{(k)}(q), the permutations
of [n] whose first k rotations all avoid q, over the patterns q ∈ S_4 exactly the eight complement–reverse orbits?
Writing a(n,k;q) for the number of such permutations, the statement is: for every k ≥ 4 and q, s ∈ S_4,
a(n,k;q) = a(n,k;s) for every n ≥ k if and only if s lies in the orbit of q under complement and reverse.

## Motivation

The theorem `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidance.result` establishes the equivalence for every
k ≥ 4 and every pair of patterns of length four, so rotation avoidance has exactly the eight classes represented by
1234, 1243, 1324, 1342, 1423, 1432, 2143 and 2413.

## Gap

Pre-registration issue 12488 records the literature screen: the arXiv record has only version 1, author pages and
title searches show no answer, and the repository had no claim on it. This is a bounded negative finding.

## Route

1. Complement and reverse preserve a(n,k;q), which gives the direction from orbits to equal counts.
2. For k ∈ {n − 1, n}, a(n,k;q) reduces to counting circular arrangements and words with a unique bad cut, so the
   counts for k ≥ 4 are governed by the cases k = n and k = n − 1.
3. An endpoint test classifies the bad cuts, and exact normal forms describe the unique-bad-cut words for seven
   orbit representatives; contraction at consecutive endpoints reduces the remaining slices.
4. The resulting counts involve the classes Av(213, 231), Av(132, 213), Av(231, 2134, 4213), Av(213, 4132) and
   Av(123, 3412), counted by 2^{n−1}, 2^n − n, odd-index Fibonacci numbers and an explicit shuffle formula.
5. Five uniform strict inequalities for n ≥ 7, together with small n, separate every pair of distinct orbits.

## Falsifier

The classification would fail if two distinct orbits had equal counts for every n ≥ k at some k ≥ 4, or if a bad cut
escaped the endpoint test.

## Evidence

An exhaustive enumeration of a(n,k;q) for all q ∈ S_4, k ≥ 4 and n ≤ 12 agrees with the formulas, and an independent
referee implementation checked the endpoint test and normal forms on the same range.

## Triage

`theorem`; the statement is Open Question 6.1 of arXiv:2607.20750v1, quantified over every k ≥ 4 and every pair of
patterns of length four.

- Proved (formalized): exactly eight Wilf classes, the complement–reverse orbits, for every k ≥ 4.
- Proved (formalized): exact counts of unique-bad-cut words for the eight representatives and the counts
  |Av_n(213, 4132)| = F_{2n−1}, |Av_n(231, 2134, 4213)| = 2^n − n.
- Open: the analogous classification for patterns of length five and for 1 ≤ k ≤ 3.

## ASSUMED-UNVERIFIED

The literature screen is limited to the arXiv record of arXiv:2607.20750, author pages, web and GitHub searches and
the repository checks.
