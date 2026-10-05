---
slug: biswas-shankar-sivasubramanian-p1-matchings
bibkey: biswas2026matchingtriples
doi: 10.48550/arXiv.2609.08562
url: https://arxiv.org/abs/2609.08562v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchings.result
---

# Generating Function of Perfect Matchings Avoiding {123, 132, 213}

## Problem

Sucharita Biswas, Umesh Shankar and Sivaramakrishnan Sivasubramanian, *Matchings and shape-Wilf-Equivalence of sets
of patterns of length three I: Triples*, arXiv:2609.08562v1, Section 6, Question 1: "Can we enumerate the matchings
that avoid the set of patterns P1 = {123, 132, 213} and P13 = {132, 213, 321}?" Matching patterns follow Section 4
and Figure 1: three arcs form an occurrence only when all three left endpoints precede all three right endpoints, and
the label records the complement of the order of the right endpoints. This dossier settles the P1 clause.

## Motivation

The theorem `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchings.result` proves that the number a_n of
perfect matchings of [2n] avoiding P1 satisfies Σ a_n z^n = (1 − zH(z)) / (1 − z − zH(z)) with
H(z) = Σ_{k≥0} Cat_k F_{k+3} z^k, equivalently a_0 = 1 and a_{n+1} = a_n + Σ_{k<n} Cat_k F_{k+3} a_{n−k}.

## Gap

Pre-registration issue 13176 records the literature screen: the authors state that the P1 and P13 classes were the
only triples not enumerated, the follow-up paper arXiv:2610.01996v1 on quadruples and quintuples does not treat them,
and the sequence 1, 3, 12, 55, 271, 1400, 7471, 40841 has no entry in the OEIS.

## Route

1. Scanning the 2n positions from left to right, a P1-avoiding matching can only close the oldest or the second-oldest
   open arc; closing a third-oldest or newer arc creates the forbidden closing order 312 or 321.
2. After the second-oldest arc closes while at least three arcs are open, the next closure must be the oldest arc,
   otherwise the order 231 appears; with exactly two open arcs there is no constraint. Conversely every scan obeying
   these rules avoids P1.
3. These rules define an automaton on states N_h and F_h, and P1-avoiding matchings are in bijection with its accepted
   words of length 2n.
4. Above height two the down-steps act by D = ((1,1),(1,0)), so a Dyck excursion with k down-steps contributes
   Cat_k shapes weighted by e_Nᵀ D^k (2,1)ᵀ = F_{k+3}; the height-one and root decompositions give the formula.

## Falsifier

The formula would fail if some n gave a different number of P1-avoiding matchings; it agrees with the paper's table
through n = 8 and with exhaustive enumeration through n = 9.

## Evidence

The proof seat and an independent referee implementation enumerated all perfect matchings of [2n] for n ≤ 9 and
compared the counts with the formula and with the paper's tables for all twenty triple classes.

## Triage

`theorem`; the statement is the P1 clause of Question 1 of arXiv:2609.08562v1.

- Proved (formalized): the generating function of P1-avoiding perfect matchings is (1 − zH)/(1 − z − zH).
- Computed: the P13 counts 1, 3, 12, 54, 258, 1276, 6449 agree with the paper; their enumeration remains open.
- Open: the enumeration of the P13 clause.

## ASSUMED-UNVERIFIED

The literature screen is limited to the arXiv records of arXiv:2609.08562 and arXiv:2610.01996, the OEIS, web and
GitHub searches and the repository checks; the full text of Hessas, Goubi and Benkhemmou (IJMOR 32(3), 2025) was not
available.
