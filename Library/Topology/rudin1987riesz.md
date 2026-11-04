---
bibkey: rudin1987riesz
authors: Walter Rudin
year: 1987
title: Real and Complex Analysis, third edition
doi: null
url: https://en.wikipedia.org/wiki/Riesz%E2%80%93Markov%E2%80%93Kakutani_representation_theorem
claim: The Riesz representation theorem identifies continuous linear functionals on C0 of a locally compact Hausdorff space with finite regular signed or complex Borel measures, with operator norm equal to total variation mass.
strata_touched:
  - D5/S3/Topology/Measures
license: citation-only
triage: anchor
---

# Signed Riesz representation on compact Hausdorff spaces

Rudin, *Real and Complex Analysis*, third edition, treats
the regular-measure representation of bounded functionals on C0. The
linked exposition states the signed real and complex forms and the
isometric identification by total variation. On compact Hausdorff K,
C0(K, Real) is C(K, Real). Empty K and the zero functional are included.
This is classical mathematics, with no claim of literature novelty.

The project construction uses the real Hahn–Banach theorem on the range
of J(f,t) = (t+f,t-f) in C(K disjoint-union K, Real). For nonempty K its
norm is |t|+norm(f), rather than the usual maximum norm on the product.
A norm-preserving extension taking the value norm(F) at the unit is
positive. Its two summand restrictions give positive functionals P,Q
with F=P-Q and P(1)+Q(1)=norm(F). Positive RMK on K supplies finite
regular measures mu,nu. The signed difference represents F, and its
variation is dominated by mu+nu. Finite domination transports compact
inner approximation and hence regularity. The signed integration
operator bound forces equality of variation mass with norm(F).

The positive RMK and Hahn–Banach suppliers are in Mathlib at revision
56a005855ea17e0b0958f73ec801ae140b0a1679. For uniqueness, the regular Jordan parts of two representatives give
equal continuous integrals on their crossed positive sums. Positive RMK
uniqueness identifies those sums, and signed Jordan reconstruction
identifies the signed measures. Applying existence to the integration
functional of any regular signed measure then gives its exact norm.
This order of inference avoids using the universal norm identity in
either existence nor uniqueness.

## Verified locator

https://en.wikipedia.org/wiki/Riesz%E2%80%93Markov%E2%80%93Kakutani_representation_theorem

The linked public exposition states the signed representation, uniqueness
and total variation norm identity and cites Rudin. This is a citation-only
reference; the book text has not been checked directly.
