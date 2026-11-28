---
slug: mesyan-2026-question-34-domain-commutativity
bibkey: mesyan2026quantales
doi: 10.48550/arXiv.2611.31109
url: https://arxiv.org/abs/2611.31109v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/ResidueRings/MesyanDomainCommutativity.result
---

# The domain equivalence in Mesyan's Question 34

## Problem

Zachary Mesyan asks, “For a domain \(R\), is \(R\) being commutative
equivalent to \(\mathcal M(R)\) being commutative?” Section 2.2 allows
semirings without a multiplicative identity. Remark 14 requires a nonzero
semiring in which the product of two nonzero elements is nonzero.
[Question 34](https://arxiv.org/html/2611.31109v1#Thmtheorem34) · [Section 2.2](https://arxiv.org/html/2611.31109v1#S2.SS2) · [Remark 14](https://arxiv.org/html/2611.31109v1#Thmtheorem14)

| Source clause | Lean counterpart |
| --- | --- |
| A domain \(R\) | `R : Type` with `NonUnitalSemiring R`, `Nontrivial R` and `NoZeroDivisors R` |
| \(R\) is commutative | `∀ x y : R, x * y = y * x` |
| \(\mathcal M(R)\) is commutative | `∀ A B : AddSubmonoid R, A * B = B * A` |
| Equivalence for every domain | `claim : Prop`, with the two commutativity predicates joined by `↔` |
| Refutation of that universal claim | `result : ¬ claim` |

Definition 4 uses all additive submonoids. Its product \(AB\) consists of
ordered sums \(\sum_{i=1}^n a_i b_i\) with \(n>0\), \(a_i\in A\)
and \(b_i\in B\). The one-term sum \(0\cdot0\) supplies zero.
These sums form the least additive submonoid containing the pairwise
products, the same product characterized by Mathlib's
`AddSubmonoid.mul_mem_mul` and `AddSubmonoid.mul_le`.
[Definition 4](https://arxiv.org/html/2611.31109v1#Thmtheorem4)

## Motivation

Commutative multiplication on elements gives equal quantale products by
reversing each factor pair. The converse asks whether passing to additive
submonoids preserves enough information to detect a difference in the order
of multiplication.

## Gap

Mesyan's Example 6 gives noncommuting elements and a commutative
submonoid quantale in positive odd characteristic. Its original algebra has
zero divisors. The bounded screen in the preregistration inspected the source,
two arXiv queries, and repository issues, pull requests, Lean modules, dossiers
and Library notes. It found the source example and nearby Question 36 work,
with no earlier delivery of the domain refutation in that scope.
[Example 6](https://arxiv.org/html/2611.31109v1#Thmtheorem6) · [Preregistration #35365](https://github.com/the-omega-institute/trureturing/issues/35365)

## Route

Over \(\mathbb F_3\), keep the coordinatewise addition of Example 6 and
its product \((a,b,c)(d,e,f)=(0,0,ae-bd)\). The product is bilinear and
both bracketings of any triple product give the original zero. Adjoin a
fresh additive identity that absorbs multiplication, keeping the
operations between original triples. The carrier has \(3^3+1=28\) elements.
Every product of two original triples is an original triple, including
those that give the original zero. Thus two nonzero elements of the
extension always have nonzero product.

Reversing the two factors negates the old product, which doubles it in
characteristic three. The doubling identity also holds for products
involving the fresh zero. Consequently each generator of \(AB\) is the
double of a generator of \(BA\) and belongs to \(BA\). Additive closure
gives containment, and exchanging the two submonoids gives equality.

## Falsifier

The elements \((1,0,0)\) and \((0,1,0)\) multiply to \((0,0,1)\) and
\((0,0,2)\) in the two orders. Their inequality, together with equality
of the products for every pair of additive submonoids, refutes the
converse implication.

## Evidence

The settling GID is
`D5/S3/Arith/ResidueRings/MesyanDomainCommutativity.result`.
Its compiled type is the literal negation of the proposition `claim`.
The proof instantiates the universal claim at the constructed
`WithZero` semiring and uses the private doubling and generator
inequality lemmas. The result's axiom closure in the official Mathlib
build is `Classical.choice`, `Quot.sound` and `propext`.

## Triage

Admission uses `open-problem-resolution` through #35365. The result has
`proof_shape: content`. The 28-element countermodel is used in the
proof to turn quantale commutativity into the false equality of its
two ordered generator products.

- **Refuted.** The equivalence in the first clause fails for domains
  under the source's semiring convention. The fresh zero ensures the
  domain property while the doubling identity makes the submonoid
  product commutative.
- **Open here.** The broader classification of semirings and rings with
  commutative submonoid quantale remains open in this dossier. So do
  the converse restricted to ordinary ring domains and the converse
  restricted to unital semiring domains.

## ASSUMED-UNVERIFIED

Literature-search completeness and priority outside the bounded
preregistration screen remain unverified.
[Preregistration and literature scope](https://github.com/the-omega-institute/trureturing/issues/35365)
