---
slug: aliabadi-2605-16478v2-problem-7-6
bibkey: aliabadi2026nonabeliantwist
doi: 10.61091/um128-18
url: https://arxiv.org/html/2605.16478v2
triage: theorem
motivation_gids:
  - D5/S3/FiniteGroups/AliabadiQuotientObstruction.exists_obstructed_multiset
---

# Aliabadi's finite nonabelian quotient-multiset problem

## Problem

Mohsen Aliabadi, *A nonabelian twist on differences of bijections*,
arXiv:2605.16478v2, Section 7, Problem 7.6, asks:

> Does every finite nonabelian group admit a multiset A of cardinality |G|
> satisfying the abelianization obstruction but not quotient-realizable?

The following paragraph says that a positive answer would characterize finite
abelian groups as precisely those finite groups for which the abelianization
obstruction is the only obstruction. The official journal article, DOI
[10.61091/um128-18](https://doi.org/10.61091/um128-18), has the same question,
global conventions and relevant definitions. The source note is
[aliabadi2026nonabeliantwist](../Library/FiniteGroups/aliabadi2026nonabeliantwist.md).

For every finite group G with multiplication not commutative, let n=|G| and
let pi:G->G/[G,G] be the canonical abelianization map. There exists a
multiset A of elements of G, counted with multiplicity, such that |A|=n
and the multiplicity-counted product of pi(a) over A is 1, but there are
no bijections b,c:{1,...,n}->G for which A is the multiset of
b(i)*c(i)^(-1). Repeated identity entries are allowed. No
product-one ordering in G, identity-free condition, group-family,
solvability or parity restriction is imposed.

Definition 2.1 supplies exactly this two-bijection meaning of quotient
realizability. Proposition 2.3 supplies the necessary abelianization
condition: the product is taken after projection, with multiplicities,
in the abelian group G/[G,G]. It does not assert an unordered product in G.

## Motivation

The canonical abelianization condition is necessary for every realizable
multiset. The result determines that it is insufficient in every finite
nonabelian group, using one uniform construction. It concerns the full
literal Problem 7.6, rather than a selected family of groups or the
stronger variant requiring a product-one ordering in G.

## Gap

The bounded accepted source reading covers the complete arXiv v2 article
and official journal body, including their conventions, Definition 2.1,
Lemma 2.2, Proposition 2.3 and the entire problem with its following
paragraph. Both sources state the question and do not give this witness.
Their permutation and cycle criteria are existing suppliers, not separate
resolution units.

The accepted repository search, including private declarations, found no
earlier exact named resolution or corresponding theory volume. Searches
of pinned Mathlib identified the generic commutator, abelianization and
permutation-support suppliers used below. The inspected third-party
formal-conjectures snapshot and bounded public literature routes found
no explicit earlier full resolution in their searched scope. These are
bounded observations, not a certificate of worldwide absence or priority.
The preregistration is
[issue #26316](https://github.com/the-omega-institute/trureturing/issues/26316#issuecomment-6620252567).

## Route

Fix an arbitrary finite nonabelian group G and put n=|G|. A group is
nonempty, so n>0. The equivalence `commutator_eq_bot_iff` makes [G,G]
nontrivial. The subgroup nontriviality equivalences supply an element
a in [G,G] with a unequal to 1. The exact kernel identity
`Abelianization.ker_of` gives pi(a)=1.

Take A to contain a once and 1 exactly n-1 times. Its cardinality is
1+(n-1)=n. Every entry maps to 1 under pi, so the multiplicity-counted
product of its images equals 1.

Suppose bijections b,c realize A. Regard them as equivalences and put
tau=c inverse composed with b, a permutation of the index set. For each
index i, tau(i) differs from i if and only if b(i)*c(i)^(-1) differs
from 1. Filtering the multiset equality by being different from 1
therefore identifies the number of moved points of tau with the number
of nonidentity entries of A, which is exactly one. The theorem
`Equiv.Perm.card_support_ne_one` rules this out. Thus no such pair
of actual bijections exists.

The Lean result uses `G : Type u`, `[Group G]`, `[Fintype G]` and
`hna : ¬ IsMulCommutative G`. Every finite group admits such a Fintype
presentation. Its conclusion is an actual `Multiset G` with
`A.card = Fintype.card G`, the product of
`A.map (Abelianization.of : G → Abelianization G)` equal to 1, and
the negation of two `Function.Bijective` functions on `Fin (Fintype.card G)`
whose literal right-quotient multiset is A. Adding one identifies `Fin n`
with {1,...,n}. The equivalence and filter/support transports are proved
inside the theorem; no additional realization premise is assumed.

Every ordering of this A in G has product a, which is unequal to 1.
Consequently this construction leaves the stronger product-one-ordering
and identity-free variants outside its scope. No additional claim for
Problem 7.5, a group instance, or a stronger problem is attached here.

## Falsifier

A mismatch in any universal quantifier, multiset multiplicity, exact
cardinality, canonical projection or literal quotient direction would
invalidate identification with the source question. So would an
unproved bijection-to-permutation bridge, a nonstandard axiom, a sorry,
or a noncurrent theorem identity. A realizing pair for the constructed
multiset would contradict the singleton-support obstruction. Restricting
to a family of groups or imposing a product-one-ordering premise would
not settle this question.

## Evidence

The single mathematical result is
`D5/S3/FiniteGroups/AliabadiQuotientObstruction.exists_obstructed_multiset`,
with statement identity
`sha256:c2d852f2f46e6523674a3925fcc3a24654f943f5c337faea1070bf972da6e854`.
Its canonical membership record is
`Golden/Frozen/state/D5/S3/FiniteGroups/AliabadiQuotientObstruction.lean.json`.
The owning Scribe and generated Blueprint are in
`Blueprint/D5/S3/FiniteGroups/AliabadiQuotientObstruction`.
The compiled axiom closure is `Classical.choice`, `Quot.sound`, and
`propext`, with no sorry. The exact source theorem is the mathematical
authority; the dossier and source article are explanatory inputs.

The pinned Mathlib revision is
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The live proof applies
`commutator_eq_bot_iff`, `Subgroup.nontrivial_iff_ne_bot`,
`Subgroup.nontrivial_iff_exists_ne_one`, `Abelianization.ker_of`, and
`Equiv.Perm.card_support_ne_one`. `Equiv.ofBijective`, `Equiv.trans`,
`Equiv.symm_apply_eq`, `mul_inv_eq_one`, `Multiset.filter_map`,
`Multiset.card_map` and the support membership characterization supply
the transports and normalization. These are generic existing results;
no independent new supplier theorem is asserted.

## Triage

The typed `OpenProblemResolutionClaim` is `Proved` for the single slug
`aliabadi-2605-16478v2-problem-7-6`, attached only to the exact theorem
above. Its source is the qualified Library note and its mathematical
scope is the entire literal Problem 7.6.

`proof_shape: bind-only`; `escape_witness: none`;
`admission_basis: open-problem-resolution`, with the preregistration
linked in Gap. There is one authored D5 theorem, zero earning definitions
and zero authored D5 helpers. Compiler-generated proof helpers are
consumed by that theorem. It has no direct frozen D5 public dependencies;
its mathematical suppliers are pinned Mathlib declarations. The named
external resolution is the sole admission unit; no extra wrapper or
companion result is included.

`question_answered`: the full universal source question above.
`dominating_theorem_search`: no earlier exact named resolution found in
the bounded repository, pinned Mathlib and stated external scope;
generic suppliers are reused directly. `computational_content.kind:
none` and `utility: none`: this is a theorem for arbitrary finite groups,
not a bounded enumeration, checker, numerical reduction or certified
fixed instance. The other computational utility fields are
not-applicable(kind=none).

The mirrored Reg declaration is
`Reg.D5.S3.FiniteGroups.AliabadiQuotientObstruction.registration`.
Its source-equivalence registration is `declared_validated`, with
source statement identity
`3165bd7fb2ebd4375f8faf9d70f8cd1621a267743dc1feb1f0838e8d17db92a1`.
It retains the complete source telescope and all conclusion clauses;
the selected readout is multiset cardinality. The typed actual law,
rejected zero-readout variation, sensitivity and nonconstant observation
are compiled evidence. `continuation: unknown` and `familyRecord: none`
do not assert undecidability or inexhaustibility. Reg audit declarations
are not additional D5 mathematical results.

## ASSUMED-UNVERIFIED

Literature completeness and worldwide priority are not verified. The
accepted bounded searches include unavailable cited-paper bodies and
rate-limited public routes; they are not promoted to exhaustive negative
evidence. Earlier source qualification and independent mathematical
assessments remain fallible supplied evidence. No model diversity or
sterile prior is certified. The stronger product-one-ordering and
identity-free questions are not settled by this result. Independent
final assessment, remote required checks, publication and external
credit remain outside this local mathematical dossier.
