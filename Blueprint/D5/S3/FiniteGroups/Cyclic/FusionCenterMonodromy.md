# Fusion-Center Monodromy

## Abstract

The order power of a self-half-braiding scalar gives the cyclic product of the associator in fusion coordinates.

Let G be a group and C a complex-linear preadditive monoidal category. Choose an object X(a) for each a in G and isomorphisms μ(a,b) from X(a) ⊗ X(b) to X(ab). For each a, assume that z ↦ z • id on X(a) is a bijection from ℂ to its endomorphisms. The half-braiding results also assume that tensoring in either variable is additive and complex-linear on morphisms.

**Theorem 1.1 (The scalar of the forward associator).**

Lean statement: `D5/S3/FiniteGroups/Cyclic/FusionCenterMonodromy.reassociation_hom`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Cyclic/FusionCenterMonodromy.reassociation_hom` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Start at X((ab)c), undo the two fusion maps in the left parenthesization, apply the forward associator, then fuse in the right parenthesization and transport along a(bc) = (ab)c. The resulting endomorphism is α(a,b,c) • id on X((ab)c). The scalar is unique by the endomorphism hypothesis. Applying that hypothesis to the inverse and composing shows that its scalar is the multiplicative inverse, so α(a,b,c) lies in ℂˣ.

**Theorem 1.2 (The hexagon and naturality give the scalar recurrence).**

Lean statement: `D5/S3/FiniteGroups/Cyclic/FusionCenterMonodromy.halfBraidingScalar_mul`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Cyclic/FusionCenterMonodromy.halfBraidingScalar_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a Mathlib HalfBraiding on X(g), a family of isomorphisms β(U) from X(g) ⊗ U to U ⊗ X(g) for every object U of C, natural in every morphism of C and satisfying the half-braiding hexagon. For h commuting with g, define θ(h) in ℂˣ by comparing μ(g,h) with β(X(h)) followed by μ(h,g) and transport along hg = gh. The theorem gives θ(h) θ(g) = α(g,h,g) θ(hg).

Compute the composite that first reassociates (X(g) ⊗ X(h)) ⊗ X(g), then crosses X(g) past X(h) ⊗ X(g), then fuses to X((hg)g). Use as a common comparison map the left fusion of (g,h,g) followed by transport along (gh)g = (hg)g. Expanding the crossing by the hexagon cancels the initial associator with its inverse. Cancelling the fusion isomorphism μ(g,g) in the definition of θ(g) shows that the self-crossing is θ(g) times the identity. Pulling that scalar out of the left whiskering cancels the remaining forward and inverse associators at (h,g,g). Right whiskering of the crossing at h and transport through the next fusion map give the coefficient θ(g) θ(h) on the common map.

Naturality along μ(h,g) moves the fusion of h and g before the crossing. The resulting crossing contributes θ(hg), with target transported along g(hg) = (hg)g. The forward associator followed by right fusion contributes α(g,h,g). The transport agrees with the common map by g(hg) = (gh)g = (hg)g. Precomposing with the inverse of that map reduces equality of the two scalar multiples to equality of scalar identities. Injectivity and commutativity in ℂˣ give the stated recurrence.

**Theorem 1.3 (The order power is the cyclic product).**

Lean statement: `D5/S3/FiniteGroups/Cyclic/FusionCenterMonodromy.pow_orderOf_eq_cyclicProduct`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Cyclic/FusionCenterMonodromy.pow_orderOf_eq_cyclicProduct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put θᵢ = θ(g^i) and s = θ(g). Transport the recurrence along g^i g = g^(i+1) to obtain θᵢ s = α(g,g^i,g) θᵢ₊₁. Induction on n gives θ₀ s^n equal to the product of α(g,g^i,g) over 0 ≤ i < n, multiplied by θₙ. At n = orderOf(g), the equality g^n = 1 = g^0 identifies θₙ with θ₀. Cancelling this unit gives s^orderOf(g) = cyclicProduct(α,g). The argument works with arbitrary choices of the fusion isomorphisms, including those at degree 1. For infinite-order g, Lean uses orderOf(g) = 0 and the identity is the empty-product equality.

**Theorem 1.4 (A nontrivial order power excludes a coboundary restriction).**

Lean statement: `D5/S3/FiniteGroups/Cyclic/FusionCenterMonodromy.not_mem_of_selfHalfBraiding_pow_ne_one`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Cyclic/FusionCenterMonodromy.not_mem_of_selfHalfBraiding_pow_ne_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose the self-crossing is z • id for z in ℂˣ and z^orderOf(g) ≠ 1. For a subgroup H of G, assume α on triples from H agrees with the two-coboundary of a cochain γ from H × H to ℂˣ with trivial coefficient action. Then g lies outside H. Comparing the self-crossing after fusion by μ(g,g) identifies z with s by scalar injectivity. If g belonged to H, cyclicProduct_eq_one_of_mem would make the cyclic product one. All successive powers stay in H, and the two coboundary ratios cancel under cyclic rotation. The order-power identity then contradicts the hypothesis on z.

Applying the result to a vertex operator algebra requires a category with the specified fusion data and a half-braiding on the chosen object. An evaluation using conformal weights also requires a comparison identifying the resulting self-crossing scalar with the proposed conformal phase.

## References

- Truth anchor: `D5/S3/FiniteGroups/Cyclic/FusionCenterMonodromy.halfBraidingScalar_mul`
- Truth anchor: `D5/S3/FiniteGroups/Cyclic/FusionCenterMonodromy.not_mem_of_selfHalfBraiding_pow_ne_one`
- Truth anchor: `D5/S3/FiniteGroups/Cyclic/FusionCenterMonodromy.pow_orderOf_eq_cyclicProduct`
- Truth anchor: `D5/S3/FiniteGroups/Cyclic/FusionCenterMonodromy.reassociation_hom`
- Dependency: [D5/S3/FiniteGroups/Cyclic/CyclicAssociatorObstruction](CyclicAssociatorObstruction.md)
