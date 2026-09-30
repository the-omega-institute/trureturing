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

## Route

Use the conjugation rack of the 105 fixed-point-free involutions in S₈, indexed by Fin 105, with x ∗ y = y⁻¹xy. On points 0 through 7, let C₇ contain the seven translations x ↦ x XOR a for a = 1,…,7. Let C₉ contain the nine permutations pₐᵦ for a,b ∈ {1,2,3}, acting by x XOR a on the lower four-point block and by 4 + ((x−4) XOR b) on the upper block. Their index sets are {0,16,32,52,68,88,104} and {0,1,2,15,16,17,30,31,32}. Both are inclusion-maximal R-cliques; their cardinalities are 7 and 9. Problem 5.22 is answered No.

The right-rack convention is literal: every right translation x ↦ mul x y is bijective, and multiplication is right self-distributive. RCommute means pointwise commutation of right translations; it is not replaced by commutation of the corresponding group elements. IsRClique includes all pairs, including equal members. IsMaximalRClique uses inclusion, rather than maximum size.

Connected means that a finite word of right translations sends any x to any y. On a finite carrier each bijective right translation has finite order, so its inverse is a nonnegative power of that translation. Consequently positive words, allowing the empty word, give exactly the orbits of the right multiplication group from printed page 17. The proof supplies explicit forward and return words for every index.

Fintype provides the finite carrier, and Finset represents every subset of it. DecidableEq is classically available and imposes no extra mathematical restriction. There are no additional rack hypotheses.

## Falsifier

Either clique failing pairwise R-commutation or inclusion-maximality, the rack failing connectedness, or equality of the two cardinalities would invalidate this witness. The local checks in result22 discharge these conditions using the pointwise conjugation table, its injective permutation embedding, right-translation words, and finite clique tests.

## Evidence

`D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.result22` has Lean type `¬ claim22`. Its kernel-checked axiom closure is `propext`, `Classical.choice`, and `Quot.sound`. Finite tests use `decide +kernel`; no native-decide axiom is used. All intermediate proof steps are local haves. The 17 authored private definitions contain witness data; there are no authored private theorem or lemma declarations.

## Triage

`theorem`. The result settles Problem 5.22 as quoted from arXiv v1. Problem 5.25, minimality of the witness, and exhaustive classification of connected racks are outside this conclusion.

## ASSUMED-UNVERIFIED

The journal full text was not read. Equality of its numbering and wording with arXiv v1 is unverified; this dossier cites arXiv v1. Literature priority beyond the bounded searched scope is unverified. 逃逸审计未完成：no existing enrolled template directly supplies the faithful realization bridge for these typeclass-quantified universal rack claims; no Reg registration is delivered. This boundary is disclosed with issue #9420.
