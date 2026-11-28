---
bibkey: mesyan2026quantales
authors: Zachary Mesyan
year: 2026
title: Quantales Arising From Rings
doi: 10.48550/arXiv.2611.31109
url: https://arxiv.org/abs/2611.31109v1
claim: Question 36 asks whether a nonunital (semi)ring can have a unital quantale of additive submonoids and asks for a classification.
strata_touched: []
license: citation-only
triage: anchor
---

# The unit question for additive-submonoid quantales

## Verified locator

The first arXiv revision is available at https://arxiv.org/abs/2611.31109v1. The registered DOI is https://doi.org/10.48550/arXiv.2611.31109. Definition 4 specifies the product on all additive submonoids. Question 36 asks about its identity.

## Source question

[Question 36](https://arxiv.org/html/2611.31109v1#Thmtheorem36) asks:

> Is there a nonunital (semi)ring \(R\) for which \(\mathcal M(R)\) unital? If so, is it possible to classify the (semi)rings with this property?

[Definition 4](https://arxiv.org/html/2611.31109v1#Thmtheorem4) takes all additive
submonoids of \(R\). It defines \(S\cdot T\) as the set of sums
\(\sum_{i=1}^{n}s_it_i\) with \(n>0\), \(s_i\in S\), and \(t_i\in T\).

The direct sum of the prime residue rings with coordinatewise operations gives
an affirmative answer to the existence clause. The entire ring is the two-sided
identity for the product of its additive submonoids. The classification clause
is outside the scope of this construction. [Construction in #35254](https://github.com/the-omega-institute/trureturing/issues/35254)

## The domain clause of Question 34

[Question 34](https://arxiv.org/html/2611.31109v1#Thmtheorem34) on page 24 asks, “For a domain
\(R\), is \(R\) being commutative equivalent to \(\mathcal M(R)\) being
commutative?” Section 2.2 permits semirings without a multiplicative identity.
[Remark 14](https://arxiv.org/html/2611.31109v1#Thmtheorem14) uses domain for a
nonzero semiring where products of nonzero elements are nonzero.

[Example 6](https://arxiv.org/html/2611.31109v1#Thmtheorem6) gives a nonunital
algebra with basis \(x,y,xy\) over a field of characteristic other than two.
In these coordinates its product is
\((a,b,c)(d,e,f)=(0,0,ae-bd)\). The example observes that in positive odd
characteristic reversing the product gives an additive multiple of the
original product.
