---
bibkey: artigue2027shadowing
authors: Alfonso Artigue
year: 2027
title: Shadowing maps
doi: 10.2140/om.2027.4.29
url: https://doi.org/10.2140/om.2027.4.29
claim: Final Question 5.19 asks for an exactly translationally equivariant shadowing map for north-south sphere homeomorphisms.
strata_touched: []
license: citation-only
triage: anchor
---

# North-south equivariant selectors

The final source is Orbita Mathematicae 4 (2027), no. 1, 29–66,
DOI [10.2140/om.2027.4.29](https://doi.org/10.2140/om.2027.4.29).
The supplied terminal mathematical source identifies final Question 5.19
on printed p. 52 and arXiv:2504.00171v1 Question 5.21 as the same existence
question. Its primary-source readback records final PDF SHA-256
`40be7aee21b4212ee132ecc935c7ce17251a9baad2b0a993551d456f89fd6632`.

The primary domain in Section 2.1 is the entire set of integer sequences
with every link error at most δ, with the product subspace topology.
Definition 2.3 requires continuity and fixing every true orbit. Definition
2.4 concerns all-accuracy tracing on smaller domains. Definition 6.1 on
printed p. 53 requires exact translation equivariance. Section 5.2 on
printed p. 51 starts with the literal two-sided pointwise north-south
condition, then uses simplifying smooth/hyperbolic assumptions for its
particular construction. Proposition 5.18 on printed p. 52 proves that
particular bracket map is not equivariant; it does not prove nonexistence
of another map.

`D5/S1/Dynamics/Shadowing/NorthSouthSelector` constructs the full selector
for arbitrary compact metric spaces with explicit local equiconnection
data and literal pointwise north-south dynamics. Stability, uniform
attraction on compact sets avoiding the opposite pole, and a strict height
are conclusions of `PointwiseNorthSouth` and `NorthSouthOrbitClock`.
`LocalEquiconnection` supplies normalized nonantipodal sphere interpolation
and transfer through a homeomorphism. The resulting topological-sphere
application preserves arbitrary north-south homeomorphisms and compatible
metrics, including the two-point case.

The existing `CompactPseudoOrbitSelector` supplier gives global tracing at
all accuracies on smaller closed domains and cofinite two-sided limit
tracing on the original domain for the same Q. Its exact restored source
is commit `5c2269ceb35eac4b8cf436d183defc9e2a1ffbc3`, SHA-256
`df66b7c5c21214ee7ba72379e228e16f19bdb386ccbec713f83fef198a30834d`.
The precise parameter substitution and derivation are in the owning
`NorthSouthSelector` Scribe; the application adds no duplicate tracing proof.

The mathematical construction is attributed to the supplied terminal proof
`public-proof.txt`, SHA-256
`9d2c8af332171841b0de2122a8a6d18d3f094b8ee563ff2b50646332144306bc`,
and its formal route `lean-route.txt`, SHA-256
`1a51a2083580f57293ae2e0f032afb5257d891328f247d26b97b81b483360a97`.
The substantive admission basis is `escape-witness`: the proof derives stability
from the literal pointwise assumptions, constructs a strict height, and constructs
the full selector using crossing interpolation and continuity at arbitrary cap
histories. These constructions are used in the selector's proof. The external
existence question is a precisely scoped application of that construction,
without an `open-problem-resolution` admission claim. No literature-priority,
comprehensive novelty or official acceptance assertion is made. The full vertical
suspension selector remains a separate theorem and does not substitute for the
arbitrary pointwise north-south result.

## Verified locator

[DOI](https://doi.org/10.2140/om.2027.4.29),
[final article](https://msp.org/om/2027/4-1/p02.xhtml),
[final PDF](https://msp.org/om/2027/4-1/om-v4-n1-p02-s.pdf),
[arXiv v1](https://arxiv.org/abs/2504.00171v1).
