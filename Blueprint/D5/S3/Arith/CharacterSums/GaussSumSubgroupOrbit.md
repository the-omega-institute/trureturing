# Weighted subgroup orbits of Gauss sums

## Abstract

Weighted orbit sums lie in the inverse-weight eigenspace for subgroup translation. Comparing this eigencharacter with that of a Gauss function gives the weighted Gauss-sum orbit formula.

Let A be a finite commutative ring, K a commutative ring, chi a multiplicative character from A to K, psi an additive character, H a subgroup of the unit group of A, rho a homomorphism from H to the units of K, and a any element of A. In the orbit formulas below h is coerced from H through the units of A into A. Write sigma for chi.toUnitHom.comp H.subtype. Neither a nor the subgroup cardinality needs to be invertible, and psi need not be primitive.

The new group-action ingredient applies to every function F from A to K. The output of the weighted orbit operator belongs to the inverse-rho eigenspace of the right-translation action of H on functions from A to K. The final Gauss formula uses this eigenlaw through the nonzero-weights theorem in its nonmatching branch; it is not an unused companion to the character-sum computation.

Four-slot source-bound audit registrations for the five public theorem targets remain unfinished, tracked at https://github.com/the-omega-institute/trureturing/issues/27398. No declared_validated registration status is claimed.

**Definition 1.1 (The weighted orbit operator).**

$$\operatorname{weightedOrbitSum}\left(H, rho, F, a\right)=\sum_{h\in H} \operatorname{rho}\left(h\right)\cdot \operatorname{F}\left(a\cdot h\right)$$

*Formalization.* `D5/S3/Arith/CharacterSums/GaussSumSubgroupOrbit.weightedOrbitSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The operator sums an arbitrary function over the unit-subgroup orbit with the indicated unit-valued weights. It uses no division by the subgroup cardinality and is defined over every commutative coefficient ring.

**Theorem 1.2 (Right translation has inverse-weight eigencharacter).**

$$\operatorname{weightedOrbitSum}\left(H, rho, F, a\cdot g\right)=\operatorname{rho}\left(g\right)^{-1}\cdot \operatorname{weightedOrbitSum}\left(H, rho, F, a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/GaussSumSubgroupOrbit.weightedOrbitSum_mulRight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every g in H, reindex the finite sum by the subgroup bijection h maps to g*h. The homomorphism law identifies rho(g) inverse times rho(g*h) with rho(h), and associativity identifies the translated arguments. This proves the eigenlaw for arbitrary F without using any Gauss-sum API or a domain hypothesis. The inverse is taken in K units before coercion. In representation terms the operator's image lies in the inverse-weight eigenspace; it is an unnormalized character-selection operator, with no idempotence claim.

**Theorem 1.3 (Factorization over an arbitrary coefficient ring).**

$$\sum_{h\in H} \operatorname{rho}\left(h\right)\cdot \operatorname{gaussSum}\left(chi, \operatorname{mulShift}\left(psi, a\cdot h\right)\right)=(\sum_{h\in H} \operatorname{rho}\left(h\right)\cdot \operatorname{chiInv}\left(h\right))\cdot \operatorname{gaussSum}\left(chi, \operatorname{mulShift}\left(psi, a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/GaussSumSubgroupOrbit.weighted_gaussSum_subgroup_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here chiInv denotes the inverse multiplicative character, evaluated at h. AddChar.mulShift_mulShift identifies the shift by a*h with the successive shifts by a and h. Mathlib's gaussSum_mulShift_eq extracts chiInv(h) from each summand, and finite-sum distributivity extracts the common Gauss sum. This factorization remains valid when K has zero divisors.

**Theorem 1.4 (Weighted character orthogonality).**

$$\sum_{g\in G} \operatorname{rho}\left(g\right)\cdot \operatorname{sigma}\left(g\right)^{-1}=if rho=sigma then \operatorname{card}\left(G\right) else 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/GaussSumSubgroupOrbit.weighted_unitHom_orthogonality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite group G and integral domain K, rho and sigma may be arbitrary homomorphisms from G to K units. Inversion is taken in the unit group and then coerced into K, so field division is unnecessary. Construct the quotient character delta as Units.coeHom composed with rho*sigma inverse. Pointwise injectivity of the unit coercion proves delta=1 if and only if rho=sigma. The genuine Mathlib API sum_hom_units then gives the displayed dichotomy.

**Theorem 1.5 (A nonzero Gauss orbit forces matching weights).**

$$\sum_{h\in H} \operatorname{rho}\left(h\right)\cdot \operatorname{gaussSum}\left(chi, \operatorname{mulShift}\left(psi, a\cdot h\right)\right)\neq0 \implies rho=sigma$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/GaussSumSubgroupOrbit.weighted_gaussSum_subgroup_nonzero_weights` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume IsDomain K and instantiate the general operator with F(b)=gaussSum chi (psi.mulShift b). Its output has inverse-rho eigencharacter by weightedOrbitSum_mulRight. Independently the Gauss-function shift law, commutativity of A and sum distributivity give the inverse-sigma eigencharacter for the same output. If the orbit value is nonzero, cancellation forces equality of the two eigencharacters at every subgroup element, hence rho=sigma. This proof actually consumes the group-action theorem and does not invoke the weighted orthogonality dichotomy.

**Theorem 1.6 (The weighted orbit selects the restricted character).**

$$\sum_{h\in H} \operatorname{rho}\left(h\right)\cdot \operatorname{gaussSum}\left(chi, \operatorname{mulShift}\left(psi, a\cdot h\right)\right)=if rho=sigma then \operatorname{card}\left(H\right)\cdot \operatorname{gaussSum}\left(chi, \operatorname{mulShift}\left(psi, a\right)\right) else 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/GaussSumSubgroupOrbit.weighted_gaussSum_subgroup_orbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume IsDomain K. The matching branch uses the general factorization and weighted orthogonality: chiInv(h) is the coercion of sigma(h) inverse, so the coefficient is the subgroup cardinality in K. The nonmatching branch uses weighted_gaussSum_subgroup_nonzero_weights by contradiction, so the live proof path is the subgroup-translation eigenlaw, then nonzero weight matching, then this final orbit formula. In positive characteristic the subgroup cardinality may itself vanish.

The domain assumption is essential for the orthogonality step. For example the two-element character with value 3 in ZMod 8 is nontrivial but has sum 1+3=4. No orthogonality statement over arbitrary commutative coefficient rings, literature novelty claim, or assertion of a nonzero selected orbit is made.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/GaussSumSubgroupOrbit.weightedOrbitSum`
- Truth anchor: `D5/S3/Arith/CharacterSums/GaussSumSubgroupOrbit.weightedOrbitSum_mulRight`
- Truth anchor: `D5/S3/Arith/CharacterSums/GaussSumSubgroupOrbit.weighted_gaussSum_subgroup_factor`
- Truth anchor: `D5/S3/Arith/CharacterSums/GaussSumSubgroupOrbit.weighted_gaussSum_subgroup_nonzero_weights`
- Truth anchor: `D5/S3/Arith/CharacterSums/GaussSumSubgroupOrbit.weighted_gaussSum_subgroup_orbit`
- Truth anchor: `D5/S3/Arith/CharacterSums/GaussSumSubgroupOrbit.weighted_unitHom_orthogonality`
