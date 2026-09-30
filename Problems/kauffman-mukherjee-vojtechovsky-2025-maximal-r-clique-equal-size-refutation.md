---
slug: kauffman-mukherjee-vojtechovsky-2025-maximal-r-clique-equal-size-refutation
bibkey: kauffman2026multivirtual
doi: 10.1016/j.jalgebra.2026.03.018
url: https://arxiv.org/abs/2504.09368v1
triage: theorem
motivation_gids:
  - D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.result22
---

# Kauffman–Mukherjee–Vojtěchovský Problem 5.22

## Problem

Printed page 21 of arXiv:2504.09368v1, section 5.5, states:

> Problem 5.22. Do all maximal R-cliques in a finite connected rack have the same size?

The affirmative reading says that any two inclusion-maximal R-cliques C and D have equal cardinalities. The formal claim22 quantifies over every Q : Type with Fintype Q and DecidableEq Q, every binary operation mul, and both cliques, with IsRack mul and Connected mul as premises.

## Motivation

The source presents this as one of several open problems about finite connected racks. The result settles the stated question with a finite conjugation-rack counterexample. Preregistration: https://github.com/the-omega-institute/trureturing/issues/9420.

## Gap

This is a first-tier externally named problem. The bounded literature checks recorded in issue #9420 and Library/Certificates/kauffman2026multivirtual.md found no settlement in the searched scope. The 2026-09-30 check of five citing arXiv TeX sources and MathDB is orchestrator-reported. It does not establish exhaustive publication priority.

The paper's Example 5.11 on printed page 18 already answers Problem 5.23 negatively: ConnectedQuandle(10,1) has [R_0,R_1] = [R_1,R_3] = 1 but [R_0,R_3] ≠ 1, and maximal R-cliques partition a rack exactly when R-commutation is transitive. This delivery does not claim a settlement of Problem 5.23.

## Route

Use the conjugation rack of the 105 fixed-point-free involutions in S₈, indexed by Fin 105, with x ∗ y = y⁻¹xy. On points 0 through 7, let C₇ contain the seven translations x ↦ x XOR a for a = 1,…,7. Let C₉ contain the nine permutations pₐᵦ for a,b ∈ {1,2,3}, acting by x XOR a on the lower four-point block and by 4 + ((x−4) XOR b) on the upper block. Their index sets are {0,16,32,52,68,88,104} and {0,1,2,15,16,17,30,31,32}. Both are inclusion-maximal R-cliques; their cardinalities are 7 and 9. Problem 5.22 is answered No.

The right-rack convention is literal: every right translation x ↦ mul x y is bijective, and multiplication is right self-distributive. RCommute means pointwise commutation of right translations; it is not replaced by commutation of the corresponding group elements. IsRClique includes all pairs, including equal members. IsMaximalRClique uses inclusion, rather than maximum size.

Connected means that a finite word of right translations sends any x to any y. On a finite carrier each bijective right translation has finite order, so its inverse is a nonnegative power of that translation. Consequently positive words, allowing the empty word, give exactly the orbits of the right multiplication group from printed page 17. The proof supplies explicit forward and return words for every index.

Fintype provides the finite carrier, and Finset represents every subset of it. DecidableEq is classically available and imposes no extra mathematical restriction. There are no additional rack hypotheses.

## Falsifier

Either clique failing pairwise R-commutation or inclusion-maximality, the rack failing connectedness, or equality of the two cardinalities would invalidate this witness. The local checks in result22 discharge these conditions using the pointwise conjugation table, its injective permutation embedding, right-translation words, and finite clique tests.

## Evidence

`D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.result22` has Lean type `¬ claim22`. Its kernel-checked axiom closure is `propext`, `Classical.choice`, and `Quot.sound`. Finite tests use `decide +kernel`; no native-decide axiom is used. All intermediate proof steps are local haves. The 11 authored private definitions contain witness data; there are no authored private theorem or lemma declarations.

## Triage

`theorem`. The result settles Problem 5.22 as quoted from arXiv v1. Problem 5.25, minimality of the witness, and exhaustive classification of connected racks are outside this conclusion.

### What the settlement shows

- The universal equal-size assertion in Problem 5.22 is false under its stated finite-rack and connectedness hypotheses. [proved: D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.result22]

- The failure already occurs in a connected, faithful quandle, so restricting from racks to quandles or requiring distinct right translations does not repair it. The 105 fixed-point-free involutions generate A₈, whose centre is trivial; on this class R-commutation agrees exactly with group-element commutation, including the test that the group commutator centralizes the class. [computed: python3, reconstruct the literal conjugation table, enumerate the generated permutation group and its centre, and compare both commutation tests on all ordered pairs; output |Q|=105, |generated group|=20160, |centre|=1, distinct right translations=105, connected=True, idempotent=True, 0 discrepancies among 11025 pairs]

- The two clique sizes arise from different maximal elementary abelian subgroup actions. The seven XOR translations generate (C₂)³ acting regularly on eight points; all seven nonidentity elements are fixed-point-free. The nine blockwise XOR permutations generate (C₂)⁴ acting on two four-point orbits; precisely nine of its fifteen nonidentity elements move every point. Each subgroup equals its centralizer in S₈, and its intersection with Q is the corresponding clique, explaining inclusion-maximality without forcing equal cardinalities. [computed: python3, close the two XOR sets under permutation multiplication and enumerate their point orbits and centralizers in S8 and Q; output C7: subgroup order=8, orbit sizes=(8), centralizer orders=(8,7); C9: subgroup order=16, orbit sizes=(4,4), centralizer orders=(16,9); both groups have exponent 2]

- Connectedness of the carrier does not make the action on maximal cliques transitive. The complete clique spectrum has 30 seven-element cliques and 35 nine-element cliques; conjugation by the generated A₈ splits them into orbits of sizes 15, 15 and 35. Equal size survives within each such orbit and within each of the two cardinality families. [computed: python3, Bron-Kerbosch enumeration of the R-commutation graph followed by conjugation-orbit enumeration using all class generators; output 65 maximal cliques, size histogram={7:30,9:35}, A8 orbit sizes by clique size={7:(15,15),9:(35)}]

- For the finite affine families tested, a stronger conclusion survives: every maximal R-clique is a singleton, so equal size and divisibility all hold. The cyclic operation is x ∗ y = tx + (1−t)y on Z/n, with both t and 1−t units; the binary-vector operation is x ∗ y = Tx + (I−T)y, with T and I−T invertible. [computed: python3, enumerate all eligible t for 2≤n≤20 and all eligible binary matrices in dimensions 2 and 3, test connectedness and enumerate right-translation cliques; output 67 cyclic models, 2 models on 4 points, 48 models on 8 points, all connected with only singleton maximal cliques]

- Does the singleton conclusion extend to every finite connected affine quandle, and does requiring the right multiplication group to act transitively on maximal R-cliques give a useful general equal-size repair beyond the computed examples? These general statements have no proof in this module. [open]

- The paper's §5.5 construction retains the desired behavior in every tested parameter case: Q_m(e) has exactly the three coordinate blocks as maximal R-cliques, each of size 2^m, in a carrier of size 3·2^m. This supplies restricted positive cases of 5.22 and divisibility in 5.24; it also attains, without exceeding, the one-third ratio discussed in 5.25. [computed: python3, build the three-case operation of §5.5 for m=1,2,3,4 and every e in the binary m-space, test the quandle laws and connectedness and enumerate maximal R-cliques; output 30 parameter cases, (carrier size, clique size)=(6,2),(12,4),(24,8),(48,16), exactly 3 blocks and all right translations distinct in each case]

- The S₈ witness is compatible with the local conclusions of Proposition 5.15 and Corollaries 5.18–5.19: every maximal clique has restricted operation x ∗ y = x, is a proper subquandle, and has only singleton internal orbits. Thus the unequal sizes do not produce a failure of those subrack or disconnectedness conclusions. Its largest clique has ratio 9/105=3/35, below both thresholds in Problem 5.25, so this witness does not answer that neighbouring question. [computed: python3, restrict the literal table to every enumerated maximal clique, compute internal right-translation orbits and the largest size ratio; output 65 trivial restricted tables, internal orbit size=1, largest clique=9<35=105/3, ratio=3/35]

## ASSUMED-UNVERIFIED

The journal full text was not read. Equality of its numbering and wording with arXiv v1 is unverified; this dossier cites arXiv v1. Literature priority beyond the bounded searched scope is unverified. 逃逸审计未完成：no existing enrolled template directly supplies the faithful realization bridge for these typeclass-quantified universal rack claims; no Reg registration is delivered. This boundary is disclosed with issue #9420.
