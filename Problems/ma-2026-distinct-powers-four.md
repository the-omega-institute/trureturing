---
slug: ma-2026-distinct-powers-four
bibkey: ma2026distinctpowers
doi: 10.48550/arXiv.2611.13582
url: https://arxiv.org/abs/2611.13582v1
triage: theorem
motivation_gids:
  - D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour.result
---

# Distinct powers for generator classes of size at most four

## Problem

Dingying Ma, *On Distinct Powers in Finite Groups*, arXiv:2611.13582v1, Remark 2.2 and Section 9, asks whether the class-size bound in Theorem 1.1 can be raised from three to four. The source note records the statement and the surrounding results. [Source note](../Library/FiniteGroups/ma2026distinctpowers.md) · [Preregistration #29890](https://github.com/the-omega-institute/trureturing/issues/29890)

Remark 2.2 (p. 3) asks, “It remains open whether an analogous general theorem holds when the equivalence classes have size at most 4.”

Section 9 (p. 16) repeats the question, “More generally, it would be interesting to know whether the hypothesis ‘size at most 3’ in Theorem 1.1 can be replaced by ‘size at most 4’.”

For every positive integer \(n\), every finite group \(G\) having no elements of orders \(2,\ldots,n+1\), and every \(n\)-element subset \(A\) whose classes under equality of generated cyclic subgroups have size at most four, there is an enumeration of \(A\) whose powers with exponents \(1,\ldots,n\) are pairwise distinct. In Lean the enumeration is an equivalence from `Fin n` to the subtype of members of `A`. Its exponent is the index value plus one. The class-size premise counts the subtype of members having the same `Subgroup.zpowers` as each given member.

## Motivation

The question extends the arbitrary-size theorem in Ma's paper. The class-size restriction allows arbitrary finite groups and arbitrary positive subset sizes.

## Gap

Remark 2.2 gives a multiset of prime-field residues for which a four-term block fails. The proof requires control of four distinct unit coordinates modulo the full generator order and allows their prime-field images to coincide.

## Route

Preservation of the generated subgroup separates powers from different classes. Complementary endpoints go to size-two classes and consecutive triples and quadruples occupy disjoint intervals. Singletons use the remaining slots. For the four-element class, a checked order-four Latin-array classification supplies a transversal, equal column symbol sets, or a motif. Commutativity excludes the motif. Equal columns force a coefficient coset in a prime reduction, contradicting the first and second power sums of four consecutive coefficients. The transversal gives the required permutation modulo the full order, and the slot assignment assembles the local permutations.

## Falsifier

A finite group, positive subset size, and subset satisfying the full order and class-size hypotheses with a collision in every enumeration would refute the assertion. A repeated multiset in a prime reduction is compatible with a successful assignment modulo the full order.

## Evidence

The theorem is `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour.result`. The finite certificate supplies the order-four classification used by the product-array proof. Best, Hendrey, Wanless, Wilson and Wood give the small-order classification context in Section 4 and Table 1. [Classification source note](../Library/FiniteGroups/best2017latinarrays.md)

The escape audit is unfinished for 38 supporting theorems. The issue lists the affected theorems and their missing source-binding and template evidence. [Escape audit #32494](https://github.com/the-omega-institute/trureturing/issues/32494)

## Triage

The proved statement covers every positive subset size under the size-four class bound. Classes of size five and above and the unrestricted distinct powers conjecture lie outside its conclusion. The mechanism allows repeated reductions of distinct unit coordinates and proves that consecutive four-term blocks already suffice modulo the full generator order. The source's separate unrestricted case \(n=7\) is outside this settlement in general.

## ASSUMED-UNVERIFIED

Completeness of the literature screen and publication priority are unverified.
The preregistration identifies this as a Tier 1 question. Its arXiv, MathOverflow, Zenodo, Crossref and Lean searches found no settlement of the size-four assertion in the screened material. Citation-index requests were rate-limited, and the preregistration records the remaining search and access limits. [Preregistration #29890](https://github.com/the-omega-institute/trureturing/issues/29890)
