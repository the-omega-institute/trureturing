---
slug: dyson-mckay-cycle-clique-optimality
bibkey: dyson2026regularinduced
doi: 10.48550/arXiv.2604.08215
url: https://arxiv.org/abs/2604.08215v3
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/RegularInduced/DysonMcKay.result
---

# Optimal Cycle–Clique Unions Without Regular Induced Subgraphs of Prime Order

## Problem

Paul W. Dyson and Brendan D. McKay, *Ramsey numbers for regular induced subgraphs*, arXiv:2604.08215v3, Section 4:
after Theorem 4.2 the authors write that they believe the graphs G_p of Theorem 4.2 are optimal for p ≥ 13 within the
class of disjoint unions of lexicographic products of cycles and cliques. Precisely: for every prime p ≥ 13, every
disjoint union of products C_r[K_s] (r ≥ 3, s ≥ 1) with no induced regular subgraph on exactly p vertices has at most
9(p−1)²/8 vertices when p ≡ 1, 5 (mod 12), (p−1)(9p−7)/8 when p ≡ 7 (mod 12) and (p−1)(9p−11)/8 when p ≡ 11 (mod 12),
and G_p attains the bound.

## Motivation

The theorem `D5/S3/Combinatorics/RegularInduced/DysonMcKay.result` establishes the optimality for every prime p ≥ 13.

## Gap

Pre-registration issue 13060 records the literature screen: the assertion is stated without proof in version 3 of the
paper, and no later proof was found; the repository had no claim on it. This is a bounded negative finding.

## Route

1. The connected induced regular subgraphs of C_r[K_s] for r ≥ 4 are cliques of order at most 2s and subgraphs meeting
   every bag whose bag counts are periodic of period three; this gives the exact order spectrum of each component at
   each degree.
2. An induced regular subgraph of a union is a union of induced regular subgraphs of the components of one common
   degree, so the absence of an induced regular p-subgraph is a condition on the combined spectra.
3. Independence and clique numbers are at most p − 1, which bounds each component; triangles of selected vertices
   are packed into the components, and the argument splits into small and large triangle supply.
4. An integer optimization over the component parameters, by the residue of p modulo 12, gives the bound; the
   explicit unions G_p of Theorem 4.2 attain it.

## Falsifier

The assertion would fail if, for some prime p ≥ 13, a union of products C_r[K_s] with more vertices avoided every
induced regular subgraph of order p, as happens for p = 7 and p = 11.

## Evidence

An independent referee implementation recomputed the component spectra by brute force on small products and searched
exactly for larger avoiding unions at p = 13, 17, 19 and 23 without finding any.

## Triage

`theorem`; the statement is the Section 4 assertion of arXiv:2604.08215v3, quantified over every prime p ≥ 13.

- Proved (formalized): the optimum equals the order of G_p for every prime p ≥ 13 within the class of disjoint unions
  of products C_r[K_s].
- Proved (paper): the same bound holds when arbitrary clique components are allowed.
- Open: the general Ramsey numbers for regular induced subgraphs of prime order outside this class.

## ASSUMED-UNVERIFIED

The literature screen is limited to the arXiv record of arXiv:2604.08215, web and GitHub searches and the repository
checks.
