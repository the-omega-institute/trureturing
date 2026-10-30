# Signed variation through finite joint observations

## Abstract

A finite joint observation retains the variation masses of a fixed finite signed family to arbitrary accuracy.

Let K be a compact Hausdorff zero-dimensional space with its Borel measurable structure. For each index i, let O(i) be a finite discrete Borel space and q(i) a continuous map from K to O(i). Assume that equality of all sensor outputs forces equality of source points. For a finite index set J, the existing finiteObservationReadout is the dependent tuple of outputs q(i), for i in J. Its output space includes unrealized tuples; no surjectivity onto that product is required.

**Theorem 1.1 (One finite budget for a finite signed family).**

Lean statement: `D5/S3/Topology/Measures/FiniteObservationVariation.exists_common_finite_readout_variation`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/FiniteObservationVariation.exists_common_finite_readout_variation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite type A, every family s(a) of real SignedMeasure values on K whose positive and negative Jordan parts are both regular, and every positive real epsilon, there exists a finite sensor set J such that, for every a, the real whole mass of the total variation of the pushforward of s(a) through finiteObservationReadout is strictly greater than the real whole mass of the total variation of s(a) minus epsilon, and is at most that original whole mass. Both empty source spaces and empty families A are included. Every Jordan part and total variation used here is finite.

Write p(a) and n(a) for the Jordan parts. The positive-clopen mass theorem supplies a clopen W(a) with signed mass above p(a)(K) minus epsilon/2. Embed K into the product of all sensor outputs using joint point separation. The native compact profinite product and clopen descent theorems show that membership in W(a) depends on finitely many original sensors. Take the union of these finite sensor sets over A. If B(a) is the image of W(a) under that joint readout, then the preimage of B(a) is exactly W(a); the reverse inclusion uses the constructed fiber constancy. The output product is finite discrete, so B(a) is measurable even when some tuples are unrealized.

The pushed-forward signed mass of B(a) equals the original signed mass of W(a), and is bounded above by the pushed-forward positive Jordan whole mass. Thus its positive Jordan mass loses less than epsilon/2. Signed whole mass is preserved by pushforward. Combining positive-minus-negative reconstruction with positive-plus-negative variation gives loss less than epsilon in variation whole mass. Native variation contraction gives the opposite inequality. This connects the actual finite joint-readout interface to signed-measure approximation; injectivity or exact preservation by an individual finite readout is never assumed.

For discrimination among finitely many regular signed hypotheses, apply the theorem to their finite family of pairwise differences. Whenever those differences have regular Jordan parts, one common finite sensor budget retains every pairwise variation mass within epsilon. For probability laws, the statistical total-variation distance is one half of the variation mass of their difference, so the corresponding error is epsilon/2. The theorem concerns masses of projected signed measures on their own finite output space. It makes no claim that lifted approximations converge in total variation, and gives no sensor budget uniform over all measures or accuracies. Compactness, regularity and joint point separation carry distinct obligations.

## References

- Truth anchor: `D5/S3/Topology/Measures/FiniteObservationVariation.exists_common_finite_readout_variation`
- Dependency: [D5/S3/ConceptDynamics/CanonicalImage/FiniteObservationQuotientRange](../../ConceptDynamics/CanonicalImage/FiniteObservationQuotientRange.md)
- Dependency: [D5/S3/Topology/Measures/PositiveClopenMass](PositiveClopenMass.md)
