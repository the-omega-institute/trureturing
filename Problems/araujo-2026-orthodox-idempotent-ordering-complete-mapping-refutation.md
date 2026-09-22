---
slug: araujo-2026-orthodox-idempotent-ordering-complete-mapping-refutation
bibkey: araujo2026completemappings
doi: 10.48550/arXiv.2608.25092
url: https://arxiv.org/abs/2608.25092
triage: theorem
motivation_gids:
  - D5/S0/Certificates/AraujoOrthodoxCompleteMappingRefutation.result
---

# Problem 15.5 answered negatively by a five-element Clifford semigroup

## Problem

Araújo, Bentz, Cameron, Hendrey, and Kinyon, *Complete Mappings of
Semigroups*, arXiv:2608.25092v1 (2026), define a complete mapping in the
abstract on printed page 1:

> A complete mapping of a semigroup S is a bijection α : S → S such that the
> map θ : S → S defined by xθ = x · xα is also a bijection.

Section 2 defines regularity on printed page 6:

> An element a of a semigroup S is said to be regular if there exists b ∈ S
> such that aba = a. If every element of a semigroup is regular, then the
> semigroup itself is said to be regular.

Section 14 defines E-semigroups and orthodox semigroups on printed page 59:

> A semigroup S is said to be an E-semigroup if the set E(S) of idempotents is
> a subsemigroup of S. A regular E-semigroup is said to be orthodox.

Theorem 14.3 on printed page 59 states:

> **Theorem 14.3.** Let S be a finite E-semigroup with a complete mapping. Then
> there exists an ordering c1, . . . , cn of all elements of S such that
> c1 · · · cn is an idempotent.

The following remark on printed page 59 records the zero case:

> We remark that for semigroups with zero this conclusion can be uninformative:
> nothing rules out the possibility that the product of elements given by
> Theorem 14.3 is zero, even if restricted to the non-zero elements. For
> instance, for the 3-element commutative idempotent semigroup S = {0, 1, 2}
> with 1 · 2 = 0, let α = θ = id_S and note that Pα = {{0}, {1}, {2}}.

Section 15 then says on printed page 60:

> The converse of Theorem 14.3 leads to the following question. An affirmative
> answer would generalize the Hall–Paige conjecture.

Problem 15.5 on printed page 60 asks:

> **Problem 15.5.** Let S be an orthodox semigroup with an ordering c1, . . . ,
> cn of all elements of S such that c1 · · · cn is an idempotent. Must S have a
> complete mapping?

The formal reading makes six decisions: (i) an ordering of all elements is a
duplicate-free finite list containing every element; (ii) `c₁ ⋯ c_n` is the
left fold; (iii) idempotent means `p * p = p`; (iv) orthodox means regular and
closed under multiplication of idempotents; (v) a complete mapping is a
bijection whose product map is also bijective; and (vi) the question is the
universal claim over `S : Type`, so one counterexample answers No.

## Motivation

The counterexample is the five-element semigroup `W` with the following
multiplication table. Rows are `x`, columns are `y`, and entries are `x * y`.

| `x \ y` | `w0` | `w1` | `w2` | `w3` | `w4` |
| --- | --- | --- | --- | --- | --- |
| `w0` | `w0` | `w1` | `w2` | `w3` | `w4` |
| `w1` | `w1` | `w0` | `w2` | `w3` | `w4` |
| `w2` | `w2` | `w2` | `w2` | `w3` | `w4` |
| `w3` | `w3` | `w3` | `w3` | `w4` | `w2` |
| `w4` | `w4` | `w4` | `w4` | `w2` | `w3` |

It is orthodox, and `[w0, w1, w2, w3, w4]` is an ordering of all elements
whose product is the idempotent `w2`. It has no complete mapping, so it gives a
negative answer to Problem 15.5.

## Gap

Issue #9377 preregistered the literal published question, the six reading
decisions, the five-element counterexample, and the literature check before the
formal proof. The checked source is arXiv:2608.25092v1, dated 2026-08-25; no
journal version was found. OpenAlex work `W7204444461` reported `cited_by: 0`,
and Crossref returned no record. Peter Cameron's 2026-08-27 blog announcement
had no comments. Four MathDB queries found no entry for Problem 15.5.
Semantic Scholar was not checked and remains `ASSUMED-UNVERIFIED`.

These bounded searches do not establish exhaustive literature coverage or
publication priority. Problems 15.1--15.4 and 15.6--15.10, Theorems 10.1 and
4.4, and the three-element `C₂⁰` case are not asserted as new results or as
separately resolved problems.

## Route

The Lean kernel decides associativity, regularity, closure of the idempotents,
the ordering `[w0, w1, w2, w3, w4]` with product `w2`, and the absence of a
complete mapping among all `5^5 = 3125` maps `W → W`. The result introduces no
intermediate proposition beyond finite computation and normalization. Its
`proof_shape` is therefore `bind-only`, its `escape_witness` is `none`, and its
preregistered `admission_basis` is `open-problem-resolution`.

Structurally, `W` is the Clifford semigroup `C₂ ∪ C₃`:
`{w0, w1} ≅ C₂` with identity `w0`, and `{w2, w3, w4} ≅ C₃` with identity
`w2`. The J-class `{w0, w1}` has maximal subgroup `C₂` and one L-class, so the
paper's Theorem 10.1 on printed page 50 explains why `W` has no complete
mapping. This structural explanation is prose and is not used by the Lean
proof.

## Falsifier

A complete mapping of `W` would overturn the refutation; the kernel checks all
3125 maps. A failure of any hypothesis would also overturn it, but
associativity, regularity, idempotent closure, and the idempotent ordering are
each kernel-decided. The printed-page-59 zero remark does not apply because `W`
has no absorbing zero.

## Evidence

- Lean theorem:
  `D5/S0/Certificates/AraujoOrthodoxCompleteMappingRefutation.result`.
- Freeze event:
  `sha256:330826dedef39b49803767597f04140489a6941193a1280cf7d93961b796eba3`.
- Module statement identity:
  `sha256:7385552d046083f4f4fc21b3d99856ff88f395b3d77e33fe29358f4f9618cc23`.
- Result declaration identity:
  `sha256:fab3c15ea37fd9722745a3b9e13d01b0781ffc3932c789e7b202359a50804f06`.
- The Freeze event has no project-level frozen prerequisites. The sole import is
  pinned Mathlib's `Mathlib.Data.Fintype.Pi` module.
- The axiom closure is `propext`, `Classical.choice`, and `Quot.sound`.
- Independent Python checked all 125 triples and found associativity; found
  regularity; found idempotents `{0, 2}` closed under multiplication; and found
  the unique inverse sets `{0:[0], 1:[1], 2:[2], 3:[4], 4:[3]}`.
- All 120 orderings have idempotent product, and every product is `2`.
- Among all 120 bijections, the number of complete mappings is `0`.
- The same independent enumeration found no absorbing zero.

## Triage

| proof_shape | direct frozen dependencies | escape_witness | admission_basis |
| --- | --- | --- | --- |
| bind-only | none | none | open-problem-resolution |

This is a preregistered first-tier external named problem under issue #9377,
resolved as `Refuted`. Its computational use is a `certified-instance` with a
typed `refutes` edge from `result` to `claim`. There is no atom and no digestion
coverage edge.

## ASSUMED-UNVERIFIED

Semantic Scholar was not checked. Literature completeness and publication
priority remain `ASSUMED-UNVERIFIED`: the bounded searches cannot exclude every
prior resolution. Source-to-Lean fidelity, the interpretation of "ordering",
and the proof-shape classification remain semantic review judgments; the Lean
kernel checks the formal statement and proof, not their equivalence to the
cited prose.
