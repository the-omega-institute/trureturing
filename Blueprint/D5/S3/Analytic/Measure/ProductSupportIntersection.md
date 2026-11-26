# Intersection of coordinate supports

## Abstract

Almost-everywhere equal measurable nonnegative functions under a finite product probability law have a common measurable representative supported on the intersection of their coordinate sets.

**Theorem 1.1 (A common representative on the intersection).**

Lean statement: `D5/S3/Analytic/Measure/ProductSupportIntersection.exists_measurable_intersection_representative`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Measure/ProductSupportIntersection.exists_measurable_intersection_representative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let I be any finite coordinate type, X_i arbitrary measurable spaces, mu_i probability measures, and mu their actual product measure. Let f,g:product_i X_i->ENNReal be measurable and mu-almost everywhere equal. Suppose f depends only on a set S of coordinates and g depends only on a set T. Then there is a measurable h depending only on S intersect T such that h=f and h=g mu-almost everywhere. No integrability, boundedness, topology or pointwise positivity is assumed. I, S and T may be empty.

Take h to be the marginal of g obtained by integrating the coordinates outside S. This removes those coordinates from its possible dependencies, so h depends only on T intersect S. The same marginal of f equals f pointwise: f does not depend on the integrated coordinates and their product law has total mass one.

To transport the almost-everywhere equality through marginal integration, let e be the indicator of f differing from g. Its integral is zero. Marginalization over a fixed coordinate set is idempotent under probability laws. Applying Mathlib's lintegral_eq_of_lmarginal_eq to the marginal of e and e shows that the marginal also has integral zero. Hence it vanishes almost everywhere. On every such slice, f and g agree almost everywhere under the integrated coordinate law, and their nonnegative integrals agree. Measurable.lmarginal supplies measurability of the resulting representative.

This is a general product-measure support lemma. It gives no equality criterion for Finner's inequality by itself: normalized conditional factors must first be shown equal under one common product law, and any change of law must still be undone on each original factor, including slices of zero conditional mass. No mathematical priority is claimed.

## References

- Truth anchor: `D5/S3/Analytic/Measure/ProductSupportIntersection.exists_measurable_intersection_representative`
