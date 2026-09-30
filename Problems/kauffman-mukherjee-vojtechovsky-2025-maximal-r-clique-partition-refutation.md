---
slug: kauffman-mukherjee-vojtechovsky-2025-maximal-r-clique-partition-refutation
bibkey: kauffman2026multivirtual
doi: 10.1016/j.jalgebra.2026.03.018
url: https://arxiv.org/abs/2504.09368v1
triage: theorem
motivation_gids:
  - D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.result23
---

# Kauffman–Mukherjee–Vojtěchovský Problem 5.23

## Problem

Printed page 21 of arXiv:2504.09368v1, section 5.5, states:

> Problem 5.23. Do maximal R-cliques in a finite connected rack Q partition Q?

The affirmative reading includes both coverage of every element by a maximal R-clique and equality of any two maximal R-cliques with nonempty intersection. The formal claim23 keeps both conjuncts and quantifies over every finite carrier, binary operation, and pair of cliques under the rack and connectedness premises.

## Motivation

The source presents this as one of several open problems about finite connected racks. The result settles the stated question with a finite conjugation-rack counterexample. Preregistration: https://github.com/the-omega-institute/trureturing/issues/9420.

## Gap

This is a first-tier externally named problem. The bounded literature checks recorded in issue #9420 and Library/Certificates/kauffman2026multivirtual.md found no settlement in the searched scope. The 2026-09-30 check of five citing arXiv TeX sources and MathDB is orchestrator-reported. It does not establish exhaustive publication priority.

## Route

Use the conjugation rack of the ten transpositions in S₅, indexed by Fin 10, with x ∗ y = y⁻¹xy. The inclusion-maximal R-cliques {(1 2),(3 4)} and {(1 2),(3 5)} are distinct and intersect in (1 2). Their index sets are {6,1} and {6,2}. This refutes the uniqueness conjunct of the full partition assertion, without removing its coverage conjunct. Problem 5.23 is answered No.

The right-rack convention is literal: every right translation x ↦ mul x y is bijective, and multiplication is right self-distributive. RCommute means pointwise commutation of right translations; it is not replaced by commutation of the corresponding group elements. IsRClique includes all pairs, including equal members. IsMaximalRClique uses inclusion, rather than maximum size.

Connected means that a finite word of right translations sends any x to any y. On a finite carrier each bijective right translation has finite order, so its inverse is a nonnegative power of that translation. Consequently positive words, allowing the empty word, give exactly the orbits of the right multiplication group from printed page 17. The proof supplies explicit forward and return words for every index.

Fintype provides the finite carrier, and Finset represents every subset of it. DecidableEq is classically available and imposes no extra mathematical restriction. There are no additional rack hypotheses.

## Falsifier

Failure of connectedness or inclusion-maximality, equality of the two cliques, or empty intersection would invalidate this witness. The local checks in result23 discharge these conditions using the pointwise conjugation table, its injective permutation embedding, right-translation words, and finite clique tests.

## Evidence

`D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.result23` has Lean type `¬ claim23`. Its kernel-checked axiom closure is `propext`, `Classical.choice`, and `Quot.sound`. Finite tests use `decide +kernel`; no native-decide axiom is used. All intermediate proof steps are local haves. The 17 authored private definitions contain witness data; there are no authored private theorem or lemma declarations.

## Triage

`theorem`. The result settles Problem 5.23 as quoted from arXiv v1. Problem 5.25, minimality of the witness, and exhaustive classification of connected racks are outside this conclusion.

### What the settlement shows

- The full partition assertion in Problem 5.23 is false; the settling result refutes its uniqueness requirement for intersecting maximal cliques. [proved: D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.result23]

- The obstruction is present in a connected, faithful quandle. The ten transpositions generate S₅ with trivial centre, and their R-commutation is exactly group-element commutation. Consequently the problem here is an overlap of ordinary commuting transpositions, rather than an identification of different elements by equal right translations. [computed: python3, reconstruct the conjugation table, enumerate the generated group and centre, and compare group, central-commutator and right-translation tests; output |Q|=10, |generated group|=120, |centre|=1, distinct right translations=10, connected=True, idempotent=True, 0 discrepancies among 100 pairs]

- The transposition (1 2) can be completed by any of (3 4), (3 5) or (4 5). Each resulting pair is maximal because a third disjoint transposition would require six points; the three alternative completions do not commute with one another. Exhaustive enumeration gives fifteen two-element maximal cliques and three cliques through every transposition, so coverage survives while uniqueness fails. Equal size and divisibility also survive in this witness, showing that even their conjunction does not repair 5.23; this realizes the overlap phenomenon of Example 5.17 in a connected quandle. [computed: python3, enumerate all S5 transpositions and their right-translation cliques, independently check all 1023 nonempty subsets; output 15 maximal cliques of size 2, incidence=3 at every element, the two settling pairs have intersection size=1, 10%2=0]

- The nearest smaller transposition classes do partition their carriers: for S₃ the maximal cliques are the three singletons, and for S₄ they are the three pairs of disjoint transpositions. In the tested range S₅ through S₈ every clique still has the same size and that size divides the carrier, but each element belongs to several cliques. [computed: python3, build transposition conjugation tables and enumerate maximal R-cliques for n=3,4,5,6,7,8; output carrier sizes=(3,6,10,15,21,28), clique sizes=(1,2,2,3,3,4), clique counts=(3,3,15,15,105,105), incidences per element=(1,1,3,3,15,15), partitions only at n=3,4]

- Singleton partitions survive in the tested dihedral and affine families. For x ∗ y = 2y−x on Z/n, every odd n from 3 through 19 gives n singleton maximal cliques. The affine operations tx+(1−t)y on Z/n and Tx+(I−T)y on binary vector spaces give the same outcome when both indicated linear maps are invertible, within the enumerated ranges. [computed: python3, enumerate the R-commutation graphs of odd dihedral orders 3..19, all eligible cyclic affine parameters for 2≤n≤20 and all eligible binary matrices in dimensions 2,3; output 9 dihedral cases, 67 cyclic models, 2 binary models of order 4 and 48 of order 8, every case connected with a singleton partition]

- A substantial centre of the generated group is also compatible with singleton cliques: take the conjugates of (u,1), where u is the matrix with rows (1,1) and (0,1) over F₃, in SL(2,3) × C₅. This four-element conjugacy class generates the whole 120-element group, with centre of order ten, yet has four distinct right translations and exactly four singleton maximal R-cliques. This gives a tested positive case with a nontrivial centre, alongside the negative S₅ example with trivial centre. [computed: python3, enumerate determinant-one matrices over F3, the stated conjugacy class, its generated subgroup in the direct product, its centre and conjugation right translations; output |Q|=4, |generated group|=120, |centre|=10, connected=True, distinct right translations=4, 4 maximal cliques of size 1]

- For arbitrary finite racks, does transitivity of the R-commutation relation characterize a partition by maximal R-cliques, with coverage always holding even when transitivity fails? Does the singleton result extend to every finite connected affine quandle? Neither general assertion is proved by this module. [open]

- The overlap does not break the local subrack conclusions of Proposition 5.15 or Corollaries 5.18–5.19 in the witness: its maximal cliques are proper trivial two-element subquandles with singleton internal orbits. The §5.5 examples retain three disjoint coordinate-block cliques in all thirty tested cases, so their operator-quandle construction is compatible with the refutation. The S₅ ratio 2/10=1/5 and the tested §5.5 ratio 1/3 do not exceed either threshold in 5.25. [computed: python3, restrict all S5 maximal clique tables and enumerate Q_m(e) from the three-case source operation for m=1,2,3,4 and all e; output 15 trivial two-element restricted tables; 30 connected source-family cases, 3 blocks each, (carrier size, clique size)=(6,2),(12,4),(24,8),(48,16), ratios=1/5 and 1/3]

## ASSUMED-UNVERIFIED

The journal full text was not read. Equality of its numbering and wording with arXiv v1 is unverified; this dossier cites arXiv v1. Literature priority beyond the bounded searched scope is unverified. 逃逸审计未完成：no existing enrolled template directly supplies the faithful realization bridge for these typeclass-quantified universal rack claims; no Reg registration is delivered. This boundary is disclosed with issue #9420.
