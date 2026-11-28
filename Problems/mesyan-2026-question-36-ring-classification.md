---
slug: mesyan-2026-question-36-ring-classification
bibkey: mesyan2026quantales
doi: 10.48550/arXiv.2611.31109
url: https://arxiv.org/abs/2611.31109v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/ResidueRings/MesyanQuantaleClassification.product_unit_iff
---

# The ring classification in Mesyan's Question 36

## Problem

Zachary Mesyan, *Quantales Arising From Rings*, arXiv:2611.31109v1, Question 36:

> Is there a nonunital (semi)ring \(R\) for which \(\mathcal M(R)\) unital? If so, is it possible to classify the (semi)rings with this property?

Definition 4 takes every additive submonoid of \(R\) and defines \(S\cdot T\)
to consist of sums \(\sum_{i=1}^n s_i t_i\), with \(n>0\), \(s_i\in S\)
and \(t_i\in T\). The factors have the indicated order. The product contains
zero by taking \(n=1\) and both factors zero.
[Question 36](https://arxiv.org/html/2611.31109v1#Thmtheorem36) · [Definition 4](https://arxiv.org/html/2611.31109v1#Thmtheorem4)

For every associative ring \(R\), including the zero ring, there is an additive
submonoid \(E\) such that \(EM=M=ME\) for every additive submonoid \(M\) if and
only if at least one of the following holds.

- There is \(u\in R\) with \(ux=x=xu\) for every \(x\in R\).
- The additive group of \(R\) is torsion and for each prime \(p\) there is an
  element \(u\) killed by some power of \(p\) such that \(ux=x=xu\) for every
  \(x\) killed by some power of \(p\). The powers may depend on the element.

The second condition uses the inherited operations on each primary component.
The zero component has identity zero. The disjunction allows overlap. The
classification here is the associative-ring clause of Question 36.
[Preregistration](https://github.com/the-omega-institute/trureturing/issues/35261)

## Motivation

An identity for the quantale acts on all additive submonoids, while an identity
of the ring acts through multiplication on its elements. The classification
identifies precisely when quantale identity can arise from internal identities
of smaller ring components.

## Gap

The first-tier preregistration records the v1 source and the searched literature.
Its arXiv exact-phrase search for “submonoid quantale” surfaced Mesyan's paper.
Four Crossref queries produced related work on primary multiplication,
subgroup preservation, and endomorphisms without a match for the full
equivalence in the results inspected. Beaumont's work concerns additive groups
that are direct sums of cyclic groups. The title of the 2017 one-sided-ideals
paper concerns rings with identity and imposes a condition on all subgroups.
[Preregistration and literature scope](https://github.com/the-omega-institute/trureturing/issues/35261) · [Beaumont](https://doi.org/10.1215/S0012-7094-48-01535-X) · [One-sided ideals](https://doi.org/10.1080/0020739X.2016.1264637) · [Inner endomorphisms](https://doi.org/10.1007/BF00967129)

## Route

Test a quantale identity on the cyclic additive submonoid of each element.
Every multiplier in that identity acts by a natural multiple on each argument,
and each argument has a fixing multiplier. Comparison on a sum with a fixed
element rules out kernel elements whose additive order divides that of the
fixed element. An infinite-order fixed element thus gives injectivity on the
whole ring. The square of its multiplier is a natural multiple of the
multiplier, and applying this relation to the fixed element makes that multiple
one. This yields a left identity.

For a nonzero \(p\)-primary component, take a fixed element of order \(p\).
The kernel statement extends from order \(p\) to all powers of \(p\). On that
component the multiplier acts as a scalar coprime to \(p\). Project the
multiplier to the component and invert that scalar modulo a power of \(p\)
annihilating the projected multiplier. This constructs an internal left
identity. The opposite ring gives right identities, and the corresponding
left and right identities agree.

Conversely, natural multiples of a ring identity give a quantale identity.
In a torsion ring, the primary decomposition has finite support on each
argument, and products between distinct components vanish. Chinese
remaindering on that support expresses the left and right action of each
primary identity as the same natural multiple. The sum of the primary
identities on the support of an element fixes it on both sides. The additive
submonoid of multipliers with these natural-multiple actions is a two-sided
quantale identity.

## Falsifier

A ring with a two-sided quantale identity, no ring identity, and an infinite
additive-order element would refute necessity. A torsion ring with a two-sided
quantale identity and a primary component lacking an internal identity would
also refute necessity when the ring lacks an identity. A ring satisfying either
listed condition whose additive-submonoid product lacked a two-sided identity
would refute sufficiency.

## Evidence

The two implications are proved by
`D5/S3/Arith/ResidueRings/MesyanQuantaleClassification.product_unit_iff`.
It quantifies over `Type u` with `NonUnitalRing`, and its axiom closure in the
official Mathlib build is `propext`, `Classical.choice`, and `Quot.sound`.
An exact Lean application expands membership in each product into the positive
finite-sum condition of Definition 4. The existence witness for the nonzero,
nonunital case is the separate result associated with issue #35254.
[Independent replay scope](https://github.com/the-omega-institute/trureturing/issues/35261#issuecomment-7237907085) · [Existence witness](https://github.com/the-omega-institute/trureturing/issues/35254#issuecomment-7237620771)

## Triage

`theorem`

### Proved mechanism

Testing on cyclic additive submonoids gives natural-multiple actions and a
fixing multiplier for each element. Comparing the action on a sum with a fixed
element shows that its multiplier kills no nonzero element whose additive
order divides the order of the fixed element. An infinite-order fixed element
gives injectivity on the whole ring and yields a global identity. An order-\(p\)
fixed element gives injectivity on elements killed by \(p\) and, by induction,
on the whole \(p\)-primary component. For sufficiency, the Chinese remainder
theorem combines the actions on the finitely many primary coordinates of each
argument into one natural multiple.

### Proved scope

For a ring containing an element of infinite additive order, the quantale
identity exists exactly when the ring has an identity. For a torsion ring, it
exists exactly when every primary component has an internal identity, even if
the ring already has a global identity. The additive order of a primary
identity is the exponent of its component. Any integer that kills the identity
also kills every element by distributivity, and any integer that kills the
component kills the identity. The construction allows infinitely many nonzero
primary components. When only finitely many are nonzero, the sum of their
identities gives a global identity. When infinitely many are nonzero, every
element has finite support and annihilates the components outside that support.
This precludes a global identity.

### Source consequences

The equivalence answers the classification clause of Question 36 for all
associative rings using Definition 4's ordered positive finite sums. The zero
ring and zero primary components use zero as their identity. The separate
existence witness realizes the nonzero case with infinitely many nonzero
primary components and no global identity.
[Definition 4](https://arxiv.org/html/2611.31109v1#Thmtheorem4) · [Question 36](https://arxiv.org/html/2611.31109v1#Thmtheorem36) · [Existence witness](https://github.com/the-omega-institute/trureturing/issues/35254#issuecomment-7237620771)

The same classification extends to associative semirings with cancellative
addition. The cyclic-multiplier criterion characterizes two-sided units of
the binary additive-submonoid product even without multiplicative
associativity. For idempotent addition, such a binary unit exists exactly when
the carrier has a two-sided multiplicative identity. The general structural
classification for arbitrary noncancellative semirings and alternative zero
conventions remain open here.
[Cancellative classification and binary criterion](../Blueprint/D5/S3/Arith/ResidueRings/MesyanCancellative.md) · [Idempotent classification](../Blueprint/D5/S3/Arith/ResidueRings/MesyanIdempotent.md)

## ASSUMED-UNVERIFIED

The preregistration records that the full text of the 2017 paper was unavailable
at the DOI route (HTTP 403), and that OpenAlex and Semantic Scholar did not
complete. Exact priority remains unverified.
[Preregistration and literature scope](https://github.com/the-omega-institute/trureturing/issues/35261)
