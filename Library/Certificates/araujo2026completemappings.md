---
bibkey: araujo2026completemappings
authors: João Araújo; Wolfram Bentz; Peter J. Cameron; Kevin Hendrey; Michael Kinyon
year: 2026
title: Complete Mappings of Semigroups
doi: 10.48550/arXiv.2608.25092
url: https://arxiv.org/abs/2608.25092
claim: Problem 15.5 asks whether an orthodox semigroup with an ordering whose product is idempotent must have a complete mapping.
strata_touched:
  - D5/S0/Certificates/AraujoOrthodoxCompleteMappingRefutation
license: citation-only
triage: anchor
---

# Complete mappings of semigroups

The abstract, printed page 1, defines the central notion:

> A complete mapping of a semigroup S is a bijection α : S → S such that the
> map θ : S → S defined by xθ = x · xα is also a bijection.

Section 2, printed page 6, defines regularity:

> An element a of a semigroup S is said to be regular if there exists b ∈ S
> such that aba = a. If every element of a semigroup is regular, then the
> semigroup itself is said to be regular.

Section 14, printed page 59, defines E-semigroups and orthodox semigroups:

> A semigroup S is said to be an E-semigroup if the set E(S) of idempotents is
> a subsemigroup of S. A regular E-semigroup is said to be orthodox.

Theorem 14.3 on the same printed page states:

> **Theorem 14.3.** Let S be a finite E-semigroup with a complete mapping. Then
> there exists an ordering c1, . . . , cn of all elements of S such that
> c1 · · · cn is an idempotent.

The following remark on printed page 59 identifies a zero-semigroup limitation:

> We remark that for semigroups with zero this conclusion can be uninformative:
> nothing rules out the possibility that the product of elements given by
> Theorem 14.3 is zero, even if restricted to the non-zero elements.

Section 15, printed page 60, introduces the converse question:

> The converse of Theorem 14.3 leads to the following question. An affirmative
> answer would generalize the Hall–Paige conjecture.

It then states:

> **Problem 15.5.** Let S be an orthodox semigroup with an ordering
> c1, . . . , cn of all elements of S such that c1 · · · cn is an idempotent.
> Must S have a complete mapping?

The formal reading makes six choices. An ordering is a duplicate-free finite
list containing every element. Its product is the left fold under semigroup
multiplication. Idempotence means `p * p = p`. Orthodox means regular with the
idempotents closed under multiplication. A complete mapping is a bijection
`α` for which `x ↦ x * α x` is also bijective. The question is a universal
claim over `S : Type` equipped with a semigroup structure.

The note records only Problem 15.5 and the definitions needed to state it. It
does not make a claim about Problems 15.1--15.4 or 15.6--15.10, Theorem 4.4,
Theorem 10.1, or the three-element semigroup obtained from `C₂` by adjoining a
zero.

## Literature status

The source is arXiv:2608.25092v1, dated 2026-08-25; no journal version is listed.
OpenAlex work `W7204444461` reported zero citations, and Crossref returned no
record. Peter Cameron's 2026-08-27 blog announcement had no comments. Four
MathDB searches found no entry for this problem. Semantic Scholar was not
checked and remains `ASSUMED-UNVERIFIED`. These bounded searches do not establish
exhaustive historical coverage or publication priority.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2608.25092
- URL: https://arxiv.org/abs/2608.25092
- Printed page 1: complete-mapping definition.
- Printed page 6: regularity definition.
- Printed page 59: E-semigroup and orthodox definitions, Theorem 14.3, and the
  zero-semigroup remark.
- Printed page 60: the lead-in and Problem 15.5.
