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

## ASSUMED-UNVERIFIED

The journal full text was not read. Equality of its numbering and wording with arXiv v1 is unverified; this dossier cites arXiv v1. Literature priority beyond the bounded searched scope is unverified. 逃逸审计未完成：no existing enrolled template directly supplies the faithful realization bridge for these typeclass-quantified universal rack claims; no Reg registration is delivered. This boundary is disclosed with issue #9420.
