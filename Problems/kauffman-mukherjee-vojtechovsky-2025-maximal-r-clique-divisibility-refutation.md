---
slug: kauffman-mukherjee-vojtechovsky-2025-maximal-r-clique-divisibility-refutation
bibkey: kauffman2026multivirtual
doi: 10.1016/j.jalgebra.2026.03.018
url: https://arxiv.org/abs/2504.09368v1
triage: theorem
motivation_gids:
  - D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.result24
---

# Kauffman–Mukherjee–Vojtěchovský Problem 5.24

## Problem

Printed page 21 of arXiv:2504.09368v1, section 5.5, states:

> Problem 5.24. Does there exist a finite connected rack Q and a maximal R-clique C of Q such that |C| does not divide |Q|?

The printed question is existential. The preregistered claim24 is its negation: every inclusion-maximal R-clique in every finite connected rack has cardinality dividing the carrier cardinality. The result refutes this universal divisibility assertion; it answers the printed existence question Yes.

## Motivation

The source presents this as one of several open problems about finite connected racks. The result settles the stated question with a finite conjugation-rack counterexample. Preregistration: https://github.com/the-omega-institute/trureturing/issues/9420.

## Gap

This is a first-tier externally named problem. The bounded literature checks recorded in issue #9420 and Library/Certificates/kauffman2026multivirtual.md found no settlement in the searched scope. The 2026-09-30 check of five citing arXiv TeX sources and MathDB is orchestrator-reported. It does not establish exhaustive publication priority.

## Route

Use the conjugation rack of the 70 three-cycles in S₇, indexed by Fin 70, with x ∗ y = y⁻¹xy. The subset {(1 2 3),(1 3 2),(4 5 6),(4 6 5)}, indexed by {40,45,2,4}, is an inclusion-maximal R-clique of size 4. Since 4 does not divide 70, result24 supplies the existence requested by Problem 5.24.

The right-rack convention is literal: every right translation x ↦ mul x y is bijective, and multiplication is right self-distributive. RCommute means pointwise commutation of right translations; it is not replaced by commutation of the corresponding group elements. IsRClique includes all pairs, including equal members. IsMaximalRClique uses inclusion, rather than maximum size.

Connected means that a finite word of right translations sends any x to any y. On a finite carrier each bijective right translation has finite order, so its inverse is a nonnegative power of that translation. Consequently positive words, allowing the empty word, give exactly the orbits of the right multiplication group from printed page 17. The proof supplies explicit forward and return words for every index.

Fintype provides the finite carrier, and Finset represents every subset of it. DecidableEq is classically available and imposes no extra mathematical restriction. There are no additional rack hypotheses.

## Falsifier

Failure of connectedness, pairwise R-commutation or inclusion-maximality, an incorrect carrier cardinality, or divisibility of 70 by 4 would invalidate this witness. The local checks in result24 discharge these conditions using the pointwise conjugation table, its injective permutation embedding, right-translation words, and finite clique tests.

## Evidence

`D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.result24` has Lean type `¬ claim24`. Its kernel-checked axiom closure is `propext`, `Classical.choice`, and `Quot.sound`. Finite tests use `decide +kernel`; no native-decide axiom is used. All intermediate proof steps are local haves. The 17 authored private definitions contain witness data; there are no authored private theorem or lemma declarations.

## Triage

`theorem`. The result settles Problem 5.24 as quoted from arXiv v1. Problem 5.25, minimality of the witness, and exhaustive classification of connected racks are outside this conclusion.

### What the settlement shows

- The universal divisibility assertion is false, which answers the printed existential Problem 5.24 Yes under its stated finite-rack and connectedness hypotheses. [proved: D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.result24]

- The witness is a connected, faithful quandle, so neither idempotence nor distinct right translations repairs divisibility. Its seventy three-cycles generate A₇ with trivial centre; R-commutation, group-element commutation and centralization of the class by the commutator give identical pairwise tests. [computed: python3, reconstruct the conjugation table, enumerate the generated group and centre, and compare the three pairwise tests; output |Q|=70, |generated group|=2520, |centre|=1, connected=True, idempotent=True, distinct right translations=70, 0 discrepancies among 4900 pairs]

- On this class, two three-cycles commute precisely when they are equal, are inverses on the same support, or have disjoint supports. A maximal clique therefore contains both orientations on each of two disjoint three-point supports, leaving one point unused. The settling clique generates C₃ × C₃ of order nine, but only four elements of that subgroup belong to the three-cycle class: clique cardinality is an intersection size, not the subgroup order to which Lagrange's theorem applies. [computed: python3, test the support rule on all class pairs and close the four settling cycles under multiplication; output 0 support-rule discrepancies among 4900 pairs, 2 supports of size 3, 1 unused point, generated subgroup order=9, subgroup intersection with Q=4, 2520%9=0]

- All maximal cliques in this witness have size four, yet 70=4·17+2. The carrier counts both orientations on all thirty-five three-point supports, while each maximal clique selects only two supports. The seventy maximal cliques cover every element four times rather than partitioning Q; this explains why equal sizes do not impose divisibility and supplies a second overlap example for 5.23. [computed: python3, enumerate the three-cycle class and all maximal R-cliques and tally element incidences; output 35 supports, |Q|=70, 70 maximal cliques of size 4, incidence=4 at every element, 70%4=2]

- In the neighbouring three-cycle classes tested, equal size survives throughout, and divisibility survives at n=5,6,8,9; the n=7 case is the sole failure in this range. Partition holds at n=5,6, but fails at n=8,9 even though divisibility holds there, so overlap alone does not force a nondividing clique size. [computed: python3, build three-cycle conjugation tables and enumerate maximal R-cliques for n=5,6,7,8,9; output carrier sizes=(20,40,70,112,168), clique sizes=(2,4,4,4,6), clique counts=(10,10,70,280,280), carrier remainders=(0,0,2,0,0), incidences per element=(1,1,4,10,10)]

- For every n≥5, do the maximal R-cliques in the S_n three-cycle class consist of both orientations on floor(n/3) disjoint supports, giving size 2·floor(n/3) and divisibility exactly when floor(n/3) divides binomial(n,3)? This would turn the finite witness into an arithmetic classification, but the general statement is not proved by this module. [open]

- For the finite affine families tested, a stronger conclusion survives: every maximal R-clique is a singleton, so equal size, partition and divisibility all hold. The cyclic operation is x ∗ y = tx + (1−t)y on Z/n, with both t and 1−t units; the binary-vector operation is x ∗ y = Tx + (I−T)y, with T and I−T invertible. [computed: python3, enumerate all eligible t for 2≤n≤20 and all eligible binary matrices in dimensions 2 and 3, test connectedness and enumerate right-translation cliques; output 67 cyclic models, 2 models on 4 points, 48 models on 8 points, all connected with only singleton maximal cliques]

- The refutation is compatible with Proposition 5.15 and Corollaries 5.18–5.19 in the witness: all seventy maximal cliques are proper trivial four-element subquandles with singleton internal orbits. The §5.5 family retains equal-size partition blocks and divisibility in every tested parameter case, so the settlement does not invalidate those finite instances of its construction. The largest witness ratio is 4/70=2/35, while the tested source-family ratio is exactly 1/3; neither exceeds the thresholds of 5.25. [computed: python3, restrict every S7 maximal clique table and enumerate Q_m(e) from the three-case source operation for m=1,2,3,4 and all e; output 70 trivial four-element restricted tables; 30 connected source-family cases, 3 blocks each, (carrier size, clique size)=(6,2),(12,4),(24,8),(48,16), ratios=2/35 and 1/3]

## ASSUMED-UNVERIFIED

The journal full text was not read. Equality of its numbering and wording with arXiv v1 is unverified; this dossier cites arXiv v1. Literature priority beyond the bounded searched scope is unverified. 逃逸审计未完成：no existing enrolled template directly supplies the faithful realization bridge for these typeclass-quantified universal rack claims; no Reg registration is delivered. This boundary is disclosed with issue #9420.
