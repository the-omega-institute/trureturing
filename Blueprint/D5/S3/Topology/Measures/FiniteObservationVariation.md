# Signed variation through finite joint observations

## Abstract

Finite joint observations recover variation uniformly on norm-compact regular signed families.

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

**Theorem 1.2 (One finite budget for a norm-compact signed family).**

Lean statement: `D5/S3/Topology/Measures/FiniteObservationVariation.exists_uniform_finite_readout_variation`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/FiniteObservationVariation.exists_uniform_finite_readout_variation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Keep exactly the compact Hausdorff zero-dimensional Borel carrier and arbitrary dependent finite discrete Borel sensors described above, with the complete sensor tuple injective. Now A is any type, with no finiteness, countability, topology or nonemptiness condition. Both Jordan parts of each s(a) are regular. Assume that the range of a mapped to NormPreservingLifts.signedFunctional(s(a)) is compact in the StrongDual operator-norm topology. For every epsilon greater than zero, there is a finite J such that every a satisfies V(s(a)) minus epsilon less than V(s(a).map q_J) less than or equal to V(s(a)), where V is totalVariation.real(univ) and q_J is literally the existing finiteObservationReadout. Empty K, empty A and unrealized output tuples are included.

The additional analytic step controls variation loss for one fixed continuous readout p, assuming regular source and output variations. This holds for the finite discrete readout used here. Write F(s) for signedFunctional(s). The existing signed integral-map identity gives F(s.map p)(g) = F(s)(g composed with p), and the supremum norm of g composed with p is at most the norm of g. Consequently the operator norm of F(s.map p) minus F(t.map p) is at most the norm of F(s) minus F(t). The signed Riesz norm identity and the two norm triangle inequalities give V(s) minus V(s.map p) at most V(t) minus V(t.map p) plus twice the norm of F(s) minus F(t). Regularity of the original variations follows from regularity of their two Jordan parts; all measures on the finite discrete output have the required regularity.

Cover the compact functional range by open balls of radius epsilon/4 centered at its own family members. A finite subcover selects finitely many centers, even when A is arbitrary. Apply exists_common_finite_readout_variation to these centers with accuracy epsilon/2. Its single finite sensor set J is then fixed. For an arbitrary family member, choose a center within epsilon/4 and use the loss-transfer estimate; the center loses less than epsilon/2 and transfer costs less than epsilon/2. This proves strict loss less than epsilon simultaneously for all a. Native variation contraction supplies the upper bound independently of compactness.

For an infinite compact example, fix a nonzero continuous linear functional L and let c range over the real interval from zero to one. The signed Riesz theorem supplies a regular signed representative s(c) with signedFunctional(s(c)) = c times L. This range is the continuous image of a compact interval in operator norm. Scalar multiplication by nonzero L is injective, so the example contains infinitely many distinct signed measures. One finite J therefore retains every variation mass in this entire continuum within epsilon. This is an application of the general theorem, with the representative regularity and compactness hypotheses discharged.

Norm compactness is essential to this argument. On the Boolean sequence space, every finite coordinate set J misses a coordinate n. The all-false sequence and the sequence true only at n have identical J readouts but are distinct. Their difference of Dirac measures has variation mass two and projects to zero. The larger family of all differences delta_x minus delta_y, for (x,y) in K times K, is compact for the weak-star topology as a continuous image of K times K, but admits no common loss less than one for any finite J. Thus weak-star compactness cannot replace the norm-compact premise. The result asserts no universal budget over all measures, computable sensor selection, noisy recovery, finite-readout injectivity or convergence of lifted reconstructions. The proof combines standard compactness and Riesz theory with the existing finite-family theorem; no claim of literature novelty or exhaustive library search is made.

## References

- Truth anchor: `D5/S3/Topology/Measures/FiniteObservationVariation.exists_common_finite_readout_variation`
- Truth anchor: `D5/S3/Topology/Measures/FiniteObservationVariation.exists_uniform_finite_readout_variation`
- Dependency: [D5/S3/ConceptDynamics/CanonicalImage/FiniteObservationQuotientRange](../../ConceptDynamics/CanonicalImage/FiniteObservationQuotientRange.md)
- Dependency: [D5/S3/Topology/Measures/PositiveClopenMass](PositiveClopenMass.md)
- Dependency: [D5/S3/Topology/Measures/SignedRieszRepresentation](SignedRieszRepresentation.md)
